%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:23 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_tarski(A_15),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,(
    ~ r2_hidden('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_33,c_24])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_37])).

tff(c_54,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  %$ r2_hidden > r1_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_2 > #skF_1
% 1.70/1.16  
% 1.70/1.16  %Foreground sorts:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Background operators:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Foreground operators:
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.70/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.70/1.16  
% 1.70/1.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.70/1.17  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.70/1.17  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.70/1.17  tff(f_45, negated_conjecture, ~(![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 1.70/1.17  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.17  tff(c_10, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.70/1.17  tff(c_33, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.70/1.17  tff(c_24, plain, (~r1_tarski(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.70/1.17  tff(c_37, plain, (~r2_hidden('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_33, c_24])).
% 1.70/1.17  tff(c_50, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_37])).
% 1.70/1.17  tff(c_54, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_50])).
% 1.70/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  Inference rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Ref     : 0
% 1.70/1.17  #Sup     : 5
% 1.70/1.17  #Fact    : 0
% 1.70/1.17  #Define  : 0
% 1.70/1.17  #Split   : 0
% 1.70/1.17  #Chain   : 0
% 1.70/1.17  #Close   : 0
% 1.70/1.17  
% 1.70/1.17  Ordering : KBO
% 1.70/1.17  
% 1.70/1.17  Simplification rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Subsume      : 0
% 1.70/1.17  #Demod        : 2
% 1.70/1.17  #Tautology    : 3
% 1.70/1.17  #SimpNegUnit  : 0
% 1.70/1.17  #BackRed      : 0
% 1.70/1.17  
% 1.70/1.17  #Partial instantiations: 0
% 1.70/1.17  #Strategies tried      : 1
% 1.70/1.17  
% 1.70/1.17  Timing (in seconds)
% 1.70/1.17  ----------------------
% 1.70/1.17  Preprocessing        : 0.27
% 1.70/1.17  Parsing              : 0.15
% 1.70/1.17  CNF conversion       : 0.02
% 1.70/1.17  Main loop            : 0.08
% 1.70/1.17  Inferencing          : 0.03
% 1.70/1.17  Reduction            : 0.02
% 1.70/1.17  Demodulation         : 0.02
% 1.70/1.17  BG Simplification    : 0.01
% 1.70/1.17  Subsumption          : 0.02
% 1.70/1.17  Abstraction          : 0.00
% 1.70/1.17  MUC search           : 0.00
% 1.70/1.17  Cooper               : 0.00
% 1.70/1.17  Total                : 0.38
% 1.70/1.17  Index Insertion      : 0.00
% 1.70/1.17  Index Deletion       : 0.00
% 1.70/1.17  Index Matching       : 0.00
% 1.70/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
