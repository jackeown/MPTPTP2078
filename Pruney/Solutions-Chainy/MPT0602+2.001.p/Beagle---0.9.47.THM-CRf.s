%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:23 EST 2020

% Result     : Theorem 1.34s
% Output     : CNFRefutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] :
        ( v4_relat_1(k1_xboole_0,A)
        & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t206_relat_1)).

tff(c_2,plain,(
    ! [A_1] : v4_relat_1(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [B_2] : v5_relat_1(k1_xboole_0,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,
    ( ~ v4_relat_1(k1_xboole_0,'#skF_2')
    | ~ v5_relat_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ~ v4_relat_1(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_10,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.34/0.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.34/0.99  
% 1.34/0.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.34/1.00  %$ v5_relat_1 > v4_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.34/1.00  
% 1.34/1.00  %Foreground sorts:
% 1.34/1.00  
% 1.34/1.00  
% 1.34/1.00  %Background operators:
% 1.34/1.00  
% 1.34/1.00  
% 1.34/1.00  %Foreground operators:
% 1.34/1.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.34/1.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.34/1.00  tff('#skF_2', type, '#skF_2': $i).
% 1.34/1.00  tff('#skF_1', type, '#skF_1': $i).
% 1.34/1.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.34/1.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.34/1.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.34/1.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.34/1.00  
% 1.34/1.01  tff(f_29, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 1.34/1.01  tff(f_34, negated_conjecture, ~(![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t206_relat_1)).
% 1.34/1.01  tff(c_2, plain, (![A_1]: (v4_relat_1(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.34/1.01  tff(c_4, plain, (![B_2]: (v5_relat_1(k1_xboole_0, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.34/1.01  tff(c_6, plain, (~v4_relat_1(k1_xboole_0, '#skF_2') | ~v5_relat_1(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.34/1.01  tff(c_8, plain, (~v4_relat_1(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.34/1.01  tff(c_10, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 1.34/1.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.34/1.01  
% 1.34/1.01  Inference rules
% 1.34/1.01  ----------------------
% 1.34/1.01  #Ref     : 0
% 1.34/1.01  #Sup     : 0
% 1.34/1.01  #Fact    : 0
% 1.34/1.01  #Define  : 0
% 1.34/1.01  #Split   : 0
% 1.34/1.01  #Chain   : 0
% 1.34/1.01  #Close   : 0
% 1.34/1.01  
% 1.34/1.01  Ordering : KBO
% 1.34/1.01  
% 1.34/1.01  Simplification rules
% 1.34/1.01  ----------------------
% 1.34/1.01  #Subsume      : 2
% 1.34/1.01  #Demod        : 2
% 1.34/1.01  #Tautology    : 0
% 1.34/1.01  #SimpNegUnit  : 0
% 1.34/1.01  #BackRed      : 0
% 1.34/1.01  
% 1.34/1.01  #Partial instantiations: 0
% 1.34/1.01  #Strategies tried      : 1
% 1.34/1.01  
% 1.34/1.01  Timing (in seconds)
% 1.34/1.01  ----------------------
% 1.34/1.01  Preprocessing        : 0.22
% 1.34/1.01  Parsing              : 0.12
% 1.34/1.01  CNF conversion       : 0.01
% 1.34/1.01  Main loop            : 0.02
% 1.34/1.01  Inferencing          : 0.00
% 1.34/1.01  Reduction            : 0.01
% 1.34/1.01  Demodulation         : 0.01
% 1.34/1.01  BG Simplification    : 0.01
% 1.34/1.01  Subsumption          : 0.00
% 1.34/1.01  Abstraction          : 0.00
% 1.34/1.01  MUC search           : 0.00
% 1.34/1.01  Cooper               : 0.00
% 1.34/1.01  Total                : 0.27
% 1.34/1.01  Index Insertion      : 0.00
% 1.34/1.01  Index Deletion       : 0.00
% 1.34/1.01  Index Matching       : 0.00
% 1.34/1.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
