%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:36 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  27 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,k3_tarski(B_12))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [A_21,B_22] :
      ( ~ r2_hidden('#skF_1'(A_21,B_22),B_22)
      | r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [A_27,A_28] :
      ( r1_tarski(A_27,k1_zfmisc_1(A_28))
      | ~ r1_tarski('#skF_1'(A_27,k1_zfmisc_1(A_28)),A_28) ) ),
    inference(resolution,[status(thm)],[c_10,c_36])).

tff(c_175,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,k1_zfmisc_1(k3_tarski(B_56)))
      | ~ r2_hidden('#skF_1'(A_55,k1_zfmisc_1(k3_tarski(B_56))),B_56) ) ),
    inference(resolution,[status(thm)],[c_20,c_55])).

tff(c_199,plain,(
    ! [A_1] : r1_tarski(A_1,k1_zfmisc_1(k3_tarski(A_1))) ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_4',k1_zfmisc_1(k3_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.14  
% 1.87/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.14  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.87/1.14  
% 1.87/1.14  %Foreground sorts:
% 1.87/1.14  
% 1.87/1.14  
% 1.87/1.14  %Background operators:
% 1.87/1.14  
% 1.87/1.14  
% 1.87/1.14  %Foreground operators:
% 1.87/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.87/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.87/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.87/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.14  
% 1.87/1.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.87/1.15  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 1.87/1.15  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.87/1.15  tff(f_46, negated_conjecture, ~(![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 1.87/1.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.15  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(A_11, k3_tarski(B_12)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.15  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.15  tff(c_36, plain, (![A_21, B_22]: (~r2_hidden('#skF_1'(A_21, B_22), B_22) | r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.87/1.15  tff(c_55, plain, (![A_27, A_28]: (r1_tarski(A_27, k1_zfmisc_1(A_28)) | ~r1_tarski('#skF_1'(A_27, k1_zfmisc_1(A_28)), A_28))), inference(resolution, [status(thm)], [c_10, c_36])).
% 1.87/1.15  tff(c_175, plain, (![A_55, B_56]: (r1_tarski(A_55, k1_zfmisc_1(k3_tarski(B_56))) | ~r2_hidden('#skF_1'(A_55, k1_zfmisc_1(k3_tarski(B_56))), B_56))), inference(resolution, [status(thm)], [c_20, c_55])).
% 1.87/1.15  tff(c_199, plain, (![A_1]: (r1_tarski(A_1, k1_zfmisc_1(k3_tarski(A_1))))), inference(resolution, [status(thm)], [c_6, c_175])).
% 1.87/1.15  tff(c_22, plain, (~r1_tarski('#skF_4', k1_zfmisc_1(k3_tarski('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.87/1.15  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_22])).
% 1.87/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.15  
% 1.87/1.15  Inference rules
% 1.87/1.15  ----------------------
% 1.87/1.15  #Ref     : 0
% 1.87/1.15  #Sup     : 37
% 1.87/1.15  #Fact    : 0
% 1.87/1.15  #Define  : 0
% 1.87/1.15  #Split   : 0
% 1.87/1.15  #Chain   : 0
% 1.87/1.15  #Close   : 0
% 1.87/1.15  
% 1.87/1.15  Ordering : KBO
% 1.87/1.15  
% 1.87/1.15  Simplification rules
% 1.87/1.15  ----------------------
% 1.87/1.15  #Subsume      : 1
% 1.87/1.15  #Demod        : 2
% 1.87/1.15  #Tautology    : 4
% 1.87/1.15  #SimpNegUnit  : 0
% 1.87/1.15  #BackRed      : 1
% 1.87/1.15  
% 1.87/1.15  #Partial instantiations: 0
% 1.87/1.15  #Strategies tried      : 1
% 1.87/1.15  
% 1.87/1.15  Timing (in seconds)
% 1.87/1.15  ----------------------
% 1.87/1.15  Preprocessing        : 0.26
% 1.87/1.15  Parsing              : 0.14
% 1.87/1.15  CNF conversion       : 0.02
% 1.87/1.15  Main loop            : 0.17
% 1.87/1.15  Inferencing          : 0.07
% 1.87/1.15  Reduction            : 0.04
% 1.87/1.15  Demodulation         : 0.02
% 1.87/1.15  BG Simplification    : 0.01
% 1.87/1.15  Subsumption          : 0.04
% 1.87/1.15  Abstraction          : 0.01
% 1.87/1.15  MUC search           : 0.00
% 1.87/1.15  Cooper               : 0.00
% 1.87/1.15  Total                : 0.45
% 1.87/1.15  Index Insertion      : 0.00
% 1.87/1.15  Index Deletion       : 0.00
% 1.87/1.15  Index Matching       : 0.00
% 1.87/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
