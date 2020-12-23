%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:25 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_48,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_22,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_41,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_16])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [A_18] : k5_xboole_0(k1_xboole_0,A_18) = k2_xboole_0(k1_xboole_0,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_77])).

tff(c_4,plain,(
    ! [A_2] : k5_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_4])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_132,plain,(
    ! [A_21] :
      ( k2_xboole_0(k1_relat_1(A_21),k2_relat_1(A_21)) = k3_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_141,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_132])).

tff(c_148,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_100,c_20,c_141])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  %$ v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0
% 1.81/1.21  
% 1.81/1.21  %Foreground sorts:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Background operators:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Foreground operators:
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.81/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.21  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.81/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.81/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.81/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.21  
% 1.81/1.21  tff(f_48, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 1.81/1.21  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.81/1.21  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.81/1.21  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.81/1.21  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.81/1.21  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.81/1.21  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.81/1.21  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.81/1.21  tff(c_22, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.21  tff(c_41, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.81/1.21  tff(c_16, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.21  tff(c_45, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_41, c_16])).
% 1.81/1.21  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.81/1.21  tff(c_77, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.21  tff(c_89, plain, (![A_18]: (k5_xboole_0(k1_xboole_0, A_18)=k2_xboole_0(k1_xboole_0, A_18))), inference(superposition, [status(thm), theory('equality')], [c_2, c_77])).
% 1.81/1.21  tff(c_4, plain, (![A_2]: (k5_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.21  tff(c_100, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_89, c_4])).
% 1.81/1.21  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.21  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.81/1.21  tff(c_132, plain, (![A_21]: (k2_xboole_0(k1_relat_1(A_21), k2_relat_1(A_21))=k3_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.81/1.21  tff(c_141, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_132])).
% 1.81/1.21  tff(c_148, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_45, c_100, c_20, c_141])).
% 1.81/1.21  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_148])).
% 1.81/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  Inference rules
% 1.81/1.21  ----------------------
% 1.81/1.21  #Ref     : 0
% 1.81/1.22  #Sup     : 33
% 1.81/1.22  #Fact    : 0
% 1.81/1.22  #Define  : 0
% 1.81/1.22  #Split   : 0
% 1.81/1.22  #Chain   : 0
% 1.81/1.22  #Close   : 0
% 1.81/1.22  
% 1.81/1.22  Ordering : KBO
% 1.81/1.22  
% 1.81/1.22  Simplification rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Subsume      : 0
% 1.81/1.22  #Demod        : 7
% 1.81/1.22  #Tautology    : 28
% 1.81/1.22  #SimpNegUnit  : 1
% 1.81/1.22  #BackRed      : 0
% 1.81/1.22  
% 1.81/1.22  #Partial instantiations: 0
% 1.81/1.22  #Strategies tried      : 1
% 1.81/1.22  
% 1.81/1.22  Timing (in seconds)
% 1.81/1.22  ----------------------
% 1.81/1.22  Preprocessing        : 0.29
% 1.81/1.22  Parsing              : 0.16
% 1.81/1.22  CNF conversion       : 0.02
% 1.81/1.22  Main loop            : 0.11
% 1.81/1.22  Inferencing          : 0.05
% 1.81/1.22  Reduction            : 0.03
% 1.81/1.22  Demodulation         : 0.03
% 1.81/1.22  BG Simplification    : 0.01
% 1.81/1.22  Subsumption          : 0.02
% 1.81/1.22  Abstraction          : 0.01
% 1.81/1.22  MUC search           : 0.00
% 1.81/1.22  Cooper               : 0.00
% 1.81/1.22  Total                : 0.43
% 1.81/1.22  Index Insertion      : 0.00
% 1.81/1.22  Index Deletion       : 0.00
% 1.81/1.22  Index Matching       : 0.00
% 1.81/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
