%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:35 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  47 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [B_40,A_39] :
      ( k3_xboole_0(k1_relat_1(B_40),A_39) = k1_relat_1(k7_relat_1(B_40,A_39))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_41] :
      ( k7_relat_1(A_41,k1_relat_1(A_41)) = A_41
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_108,plain,(
    ! [C_60,A_61,B_62] :
      ( k7_relat_1(k7_relat_1(C_60,A_61),B_62) = k7_relat_1(C_60,k3_xboole_0(A_61,B_62))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_164,plain,(
    ! [A_70,B_71] :
      ( k7_relat_1(A_70,k3_xboole_0(k1_relat_1(A_70),B_71)) = k7_relat_1(A_70,B_71)
      | ~ v1_relat_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_108])).

tff(c_253,plain,(
    ! [B_82,A_83] :
      ( k7_relat_1(B_82,k1_relat_1(k7_relat_1(B_82,A_83))) = k7_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_164])).

tff(c_16,plain,(
    ! [A_30,B_31] : k6_subset_1(A_30,B_31) = k4_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [B_38,A_37] :
      ( k1_relat_1(k6_subset_1(B_38,k7_relat_1(B_38,A_37))) = k6_subset_1(k1_relat_1(B_38),A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [B_38,A_37] :
      ( k1_relat_1(k4_xboole_0(B_38,k7_relat_1(B_38,A_37))) = k4_xboole_0(k1_relat_1(B_38),A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_22])).

tff(c_708,plain,(
    ! [B_110,A_111] :
      ( k4_xboole_0(k1_relat_1(B_110),k1_relat_1(k7_relat_1(B_110,A_111))) = k1_relat_1(k4_xboole_0(B_110,k7_relat_1(B_110,A_111)))
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_32])).

tff(c_28,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_31,plain,(
    k4_xboole_0(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_28])).

tff(c_714,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_31])).

tff(c_749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.42  
% 2.63/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.42  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.63/1.42  
% 2.63/1.42  %Foreground sorts:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Background operators:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Foreground operators:
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.63/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.42  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.63/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.63/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.63/1.42  
% 2.63/1.43  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t213_relat_1)).
% 2.63/1.43  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.63/1.43  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.63/1.43  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.63/1.43  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.63/1.43  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 2.63/1.43  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.63/1.43  tff(c_24, plain, (![B_40, A_39]: (k3_xboole_0(k1_relat_1(B_40), A_39)=k1_relat_1(k7_relat_1(B_40, A_39)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.43  tff(c_26, plain, (![A_41]: (k7_relat_1(A_41, k1_relat_1(A_41))=A_41 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.63/1.43  tff(c_108, plain, (![C_60, A_61, B_62]: (k7_relat_1(k7_relat_1(C_60, A_61), B_62)=k7_relat_1(C_60, k3_xboole_0(A_61, B_62)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.63/1.43  tff(c_164, plain, (![A_70, B_71]: (k7_relat_1(A_70, k3_xboole_0(k1_relat_1(A_70), B_71))=k7_relat_1(A_70, B_71) | ~v1_relat_1(A_70) | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_26, c_108])).
% 2.63/1.43  tff(c_253, plain, (![B_82, A_83]: (k7_relat_1(B_82, k1_relat_1(k7_relat_1(B_82, A_83)))=k7_relat_1(B_82, A_83) | ~v1_relat_1(B_82) | ~v1_relat_1(B_82) | ~v1_relat_1(B_82))), inference(superposition, [status(thm), theory('equality')], [c_24, c_164])).
% 2.63/1.43  tff(c_16, plain, (![A_30, B_31]: (k6_subset_1(A_30, B_31)=k4_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.43  tff(c_22, plain, (![B_38, A_37]: (k1_relat_1(k6_subset_1(B_38, k7_relat_1(B_38, A_37)))=k6_subset_1(k1_relat_1(B_38), A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.63/1.43  tff(c_32, plain, (![B_38, A_37]: (k1_relat_1(k4_xboole_0(B_38, k7_relat_1(B_38, A_37)))=k4_xboole_0(k1_relat_1(B_38), A_37) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_22])).
% 2.63/1.43  tff(c_708, plain, (![B_110, A_111]: (k4_xboole_0(k1_relat_1(B_110), k1_relat_1(k7_relat_1(B_110, A_111)))=k1_relat_1(k4_xboole_0(B_110, k7_relat_1(B_110, A_111))) | ~v1_relat_1(B_110) | ~v1_relat_1(B_110) | ~v1_relat_1(B_110) | ~v1_relat_1(B_110))), inference(superposition, [status(thm), theory('equality')], [c_253, c_32])).
% 2.63/1.43  tff(c_28, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.63/1.43  tff(c_31, plain, (k4_xboole_0(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_28])).
% 2.63/1.43  tff(c_714, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_708, c_31])).
% 2.63/1.43  tff(c_749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_714])).
% 2.63/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.43  
% 2.63/1.43  Inference rules
% 2.63/1.43  ----------------------
% 2.63/1.43  #Ref     : 0
% 2.63/1.43  #Sup     : 197
% 2.63/1.43  #Fact    : 0
% 2.63/1.43  #Define  : 0
% 2.63/1.43  #Split   : 0
% 2.63/1.43  #Chain   : 0
% 2.63/1.43  #Close   : 0
% 2.63/1.43  
% 2.63/1.43  Ordering : KBO
% 2.63/1.43  
% 2.63/1.43  Simplification rules
% 2.63/1.43  ----------------------
% 2.63/1.43  #Subsume      : 13
% 2.63/1.43  #Demod        : 5
% 2.63/1.43  #Tautology    : 56
% 2.63/1.43  #SimpNegUnit  : 0
% 2.63/1.43  #BackRed      : 0
% 2.63/1.43  
% 2.63/1.43  #Partial instantiations: 0
% 2.63/1.43  #Strategies tried      : 1
% 2.63/1.43  
% 2.63/1.43  Timing (in seconds)
% 2.63/1.43  ----------------------
% 2.63/1.43  Preprocessing        : 0.28
% 2.63/1.43  Parsing              : 0.15
% 2.63/1.43  CNF conversion       : 0.02
% 2.63/1.43  Main loop            : 0.34
% 2.63/1.43  Inferencing          : 0.15
% 2.63/1.43  Reduction            : 0.09
% 2.63/1.43  Demodulation         : 0.06
% 2.63/1.43  BG Simplification    : 0.03
% 2.63/1.43  Subsumption          : 0.06
% 2.63/1.43  Abstraction          : 0.03
% 2.63/1.43  MUC search           : 0.00
% 2.63/1.43  Cooper               : 0.00
% 2.63/1.43  Total                : 0.65
% 2.63/1.43  Index Insertion      : 0.00
% 2.63/1.43  Index Deletion       : 0.00
% 2.63/1.43  Index Matching       : 0.00
% 2.63/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
