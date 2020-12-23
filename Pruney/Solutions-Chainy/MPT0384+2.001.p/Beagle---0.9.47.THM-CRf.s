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
% DateTime   : Thu Dec  3 09:57:08 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    2
%              Number of atoms          :   12 (  12 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_46,negated_conjecture,(
    k1_setfam_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(c_24,plain,(
    k1_setfam_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_25,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.03  
% 1.55/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.04  %$ r2_hidden > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.55/1.04  
% 1.55/1.04  %Foreground sorts:
% 1.55/1.04  
% 1.55/1.04  
% 1.55/1.04  %Background operators:
% 1.55/1.04  
% 1.55/1.04  
% 1.55/1.04  %Foreground operators:
% 1.55/1.04  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.55/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.55/1.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.55/1.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.55/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.55/1.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.55/1.04  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.55/1.04  
% 1.55/1.05  tff(f_46, negated_conjecture, ~(k1_setfam_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_setfam_1)).
% 1.55/1.05  tff(f_44, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 1.55/1.05  tff(c_24, plain, (k1_setfam_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.55/1.05  tff(c_22, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.55/1.05  tff(c_25, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22])).
% 1.55/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.05  
% 1.55/1.05  Inference rules
% 1.55/1.05  ----------------------
% 1.55/1.05  #Ref     : 0
% 1.55/1.05  #Sup     : 0
% 1.55/1.05  #Fact    : 0
% 1.55/1.05  #Define  : 0
% 1.55/1.05  #Split   : 0
% 1.55/1.05  #Chain   : 0
% 1.55/1.05  #Close   : 0
% 1.55/1.05  
% 1.55/1.05  Ordering : KBO
% 1.55/1.05  
% 1.55/1.05  Simplification rules
% 1.55/1.05  ----------------------
% 1.55/1.05  #Subsume      : 11
% 1.55/1.05  #Demod        : 0
% 1.55/1.05  #Tautology    : 0
% 1.55/1.05  #SimpNegUnit  : 1
% 1.55/1.05  #BackRed      : 0
% 1.55/1.05  
% 1.55/1.05  #Partial instantiations: 0
% 1.55/1.05  #Strategies tried      : 1
% 1.55/1.05  
% 1.55/1.05  Timing (in seconds)
% 1.55/1.05  ----------------------
% 1.55/1.05  Preprocessing        : 0.26
% 1.55/1.05  Parsing              : 0.14
% 1.55/1.05  CNF conversion       : 0.02
% 1.55/1.05  Main loop            : 0.02
% 1.55/1.05  Inferencing          : 0.00
% 1.55/1.05  Reduction            : 0.01
% 1.55/1.05  Demodulation         : 0.00
% 1.55/1.05  BG Simplification    : 0.01
% 1.55/1.05  Subsumption          : 0.00
% 1.55/1.05  Abstraction          : 0.00
% 1.55/1.05  MUC search           : 0.00
% 1.55/1.05  Cooper               : 0.00
% 1.55/1.05  Total                : 0.31
% 1.55/1.05  Index Insertion      : 0.00
% 1.55/1.05  Index Deletion       : 0.00
% 1.55/1.05  Index Matching       : 0.00
% 1.55/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
