%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:32 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  35 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(c_16,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_39,plain,(
    ! [A_23,B_24] :
      ( r2_hidden('#skF_2'(A_23,B_24),A_23)
      | r1_tarski(k3_tarski(A_23),B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_30,B_31,B_32] :
      ( r2_hidden('#skF_2'(A_30,B_31),B_32)
      | ~ r1_tarski(A_30,B_32)
      | r1_tarski(k3_tarski(A_30),B_31) ) ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,k3_tarski(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( ~ r1_tarski('#skF_2'(A_21,B_22),B_22)
      | r1_tarski(k3_tarski(A_21),B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [A_21,B_7] :
      ( r1_tarski(k3_tarski(A_21),k3_tarski(B_7))
      | ~ r2_hidden('#skF_2'(A_21,k3_tarski(B_7)),B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_34])).

tff(c_68,plain,(
    ! [A_33,B_34] :
      ( ~ r1_tarski(A_33,B_34)
      | r1_tarski(k3_tarski(A_33),k3_tarski(B_34)) ) ),
    inference(resolution,[status(thm)],[c_59,c_38])).

tff(c_14,plain,(
    ~ r1_tarski(k3_tarski('#skF_3'),k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_14])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.10  
% 1.54/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.10  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.54/1.10  
% 1.54/1.10  %Foreground sorts:
% 1.54/1.10  
% 1.54/1.10  
% 1.54/1.10  %Background operators:
% 1.54/1.10  
% 1.54/1.10  
% 1.54/1.10  %Foreground operators:
% 1.54/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.54/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.54/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.54/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.54/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.54/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.54/1.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.54/1.10  
% 1.54/1.11  tff(f_48, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 1.54/1.11  tff(f_43, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 1.54/1.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.54/1.11  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 1.54/1.11  tff(c_16, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.54/1.11  tff(c_39, plain, (![A_23, B_24]: (r2_hidden('#skF_2'(A_23, B_24), A_23) | r1_tarski(k3_tarski(A_23), B_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.54/1.11  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.54/1.11  tff(c_59, plain, (![A_30, B_31, B_32]: (r2_hidden('#skF_2'(A_30, B_31), B_32) | ~r1_tarski(A_30, B_32) | r1_tarski(k3_tarski(A_30), B_31))), inference(resolution, [status(thm)], [c_39, c_2])).
% 1.54/1.11  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k3_tarski(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.54/1.11  tff(c_34, plain, (![A_21, B_22]: (~r1_tarski('#skF_2'(A_21, B_22), B_22) | r1_tarski(k3_tarski(A_21), B_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.54/1.11  tff(c_38, plain, (![A_21, B_7]: (r1_tarski(k3_tarski(A_21), k3_tarski(B_7)) | ~r2_hidden('#skF_2'(A_21, k3_tarski(B_7)), B_7))), inference(resolution, [status(thm)], [c_8, c_34])).
% 1.54/1.11  tff(c_68, plain, (![A_33, B_34]: (~r1_tarski(A_33, B_34) | r1_tarski(k3_tarski(A_33), k3_tarski(B_34)))), inference(resolution, [status(thm)], [c_59, c_38])).
% 1.54/1.11  tff(c_14, plain, (~r1_tarski(k3_tarski('#skF_3'), k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.54/1.11  tff(c_71, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_14])).
% 1.54/1.11  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_71])).
% 1.54/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.11  
% 1.54/1.11  Inference rules
% 1.54/1.11  ----------------------
% 1.54/1.11  #Ref     : 0
% 1.54/1.11  #Sup     : 11
% 1.54/1.11  #Fact    : 0
% 1.54/1.11  #Define  : 0
% 1.54/1.11  #Split   : 0
% 1.54/1.11  #Chain   : 0
% 1.54/1.11  #Close   : 0
% 1.54/1.11  
% 1.54/1.11  Ordering : KBO
% 1.54/1.11  
% 1.54/1.11  Simplification rules
% 1.54/1.11  ----------------------
% 1.54/1.11  #Subsume      : 0
% 1.54/1.11  #Demod        : 2
% 1.54/1.11  #Tautology    : 2
% 1.54/1.11  #SimpNegUnit  : 0
% 1.54/1.11  #BackRed      : 0
% 1.54/1.11  
% 1.54/1.11  #Partial instantiations: 0
% 1.54/1.11  #Strategies tried      : 1
% 1.54/1.11  
% 1.54/1.11  Timing (in seconds)
% 1.54/1.11  ----------------------
% 1.54/1.11  Preprocessing        : 0.25
% 1.54/1.11  Parsing              : 0.14
% 1.54/1.11  CNF conversion       : 0.02
% 1.54/1.11  Main loop            : 0.11
% 1.54/1.11  Inferencing          : 0.05
% 1.54/1.11  Reduction            : 0.02
% 1.54/1.11  Demodulation         : 0.02
% 1.54/1.11  BG Simplification    : 0.01
% 1.54/1.11  Subsumption          : 0.02
% 1.54/1.12  Abstraction          : 0.00
% 1.54/1.12  MUC search           : 0.00
% 1.54/1.12  Cooper               : 0.00
% 1.54/1.12  Total                : 0.38
% 1.54/1.12  Index Insertion      : 0.00
% 1.54/1.12  Index Deletion       : 0.00
% 1.54/1.12  Index Matching       : 0.00
% 1.54/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
