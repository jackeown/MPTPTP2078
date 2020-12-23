%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:25 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  37 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_24,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ! [B_16] : k2_zfmisc_1(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_95,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_86])).

tff(c_99,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_95])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_111,plain,(
    ! [A_23] : k5_xboole_0(k1_xboole_0,A_23) = k2_xboole_0(k1_xboole_0,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_8])).

tff(c_126,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_6])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_177,plain,(
    ! [A_27] :
      ( k2_xboole_0(k1_relat_1(A_27),k2_relat_1(A_27)) = k3_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_186,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_177])).

tff(c_193,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_126,c_22,c_186])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  
% 1.63/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.15  %$ v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0
% 1.63/1.15  
% 1.63/1.15  %Foreground sorts:
% 1.63/1.15  
% 1.63/1.15  
% 1.63/1.15  %Background operators:
% 1.63/1.15  
% 1.63/1.15  
% 1.63/1.15  %Foreground operators:
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.15  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.63/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.63/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.63/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.63/1.15  
% 1.81/1.16  tff(f_50, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 1.81/1.16  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.81/1.16  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.81/1.16  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.81/1.16  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.81/1.16  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.81/1.16  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.81/1.16  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.81/1.16  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.81/1.16  tff(c_24, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.16  tff(c_50, plain, (![B_16]: (k2_zfmisc_1(k1_xboole_0, B_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.81/1.16  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.81/1.16  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_18])).
% 1.81/1.16  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.16  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.16  tff(c_86, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.81/1.16  tff(c_95, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_86])).
% 1.81/1.16  tff(c_99, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_95])).
% 1.81/1.16  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.16  tff(c_111, plain, (![A_23]: (k5_xboole_0(k1_xboole_0, A_23)=k2_xboole_0(k1_xboole_0, A_23))), inference(superposition, [status(thm), theory('equality')], [c_99, c_8])).
% 1.81/1.16  tff(c_126, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_111, c_6])).
% 1.81/1.16  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.16  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.16  tff(c_177, plain, (![A_27]: (k2_xboole_0(k1_relat_1(A_27), k2_relat_1(A_27))=k3_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.16  tff(c_186, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_177])).
% 1.81/1.16  tff(c_193, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_126, c_22, c_186])).
% 1.81/1.16  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_193])).
% 1.81/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.16  
% 1.81/1.16  Inference rules
% 1.81/1.16  ----------------------
% 1.81/1.16  #Ref     : 0
% 1.81/1.16  #Sup     : 43
% 1.81/1.16  #Fact    : 0
% 1.81/1.16  #Define  : 0
% 1.81/1.16  #Split   : 0
% 1.81/1.16  #Chain   : 0
% 1.81/1.16  #Close   : 0
% 1.81/1.16  
% 1.81/1.16  Ordering : KBO
% 1.81/1.16  
% 1.81/1.16  Simplification rules
% 1.81/1.16  ----------------------
% 1.81/1.16  #Subsume      : 0
% 1.81/1.16  #Demod        : 11
% 1.81/1.16  #Tautology    : 36
% 1.81/1.16  #SimpNegUnit  : 1
% 1.81/1.16  #BackRed      : 0
% 1.81/1.16  
% 1.81/1.16  #Partial instantiations: 0
% 1.81/1.16  #Strategies tried      : 1
% 1.81/1.16  
% 1.81/1.16  Timing (in seconds)
% 1.81/1.16  ----------------------
% 1.81/1.16  Preprocessing        : 0.27
% 1.81/1.16  Parsing              : 0.15
% 1.81/1.16  CNF conversion       : 0.01
% 1.81/1.16  Main loop            : 0.13
% 1.81/1.16  Inferencing          : 0.05
% 1.81/1.16  Reduction            : 0.04
% 1.81/1.16  Demodulation         : 0.03
% 1.81/1.16  BG Simplification    : 0.01
% 1.81/1.17  Subsumption          : 0.02
% 1.81/1.17  Abstraction          : 0.01
% 1.81/1.17  MUC search           : 0.00
% 1.81/1.17  Cooper               : 0.00
% 1.81/1.17  Total                : 0.42
% 1.81/1.17  Index Insertion      : 0.00
% 1.81/1.17  Index Deletion       : 0.00
% 1.81/1.17  Index Matching       : 0.00
% 1.81/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
