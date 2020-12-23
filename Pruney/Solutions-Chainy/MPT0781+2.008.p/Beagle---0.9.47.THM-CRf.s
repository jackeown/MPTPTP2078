%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:45 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   42 (  44 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  62 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ! [A_27] :
      ( k2_xboole_0(k1_relat_1(A_27),k2_relat_1(A_27)) = k3_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_27] :
      ( r1_tarski(k1_relat_1(A_27),k3_relat_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_10])).

tff(c_122,plain,(
    ! [B_38,A_39] :
      ( k7_relat_1(B_38,A_39) = B_38
      | ~ r1_tarski(k1_relat_1(B_38),A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    ! [A_41] :
      ( k7_relat_1(A_41,k3_relat_1(A_41)) = A_41
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_60,c_122])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k8_relat_1(A_15,k7_relat_1(B_16,A_15)) = k2_wellord1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_391,plain,(
    ! [A_70] :
      ( k8_relat_1(k3_relat_1(A_70),A_70) = k2_wellord1(A_70,k3_relat_1(A_70))
      | ~ v1_relat_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_20])).

tff(c_14,plain,(
    ! [A_10] :
      ( k2_xboole_0(k1_relat_1(A_10),k2_relat_1(A_10)) = k3_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_88,plain,(
    ! [A_33,B_34] :
      ( k8_relat_1(A_33,B_34) = B_34
      | ~ r1_tarski(k2_relat_1(B_34),A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_315,plain,(
    ! [C_60,B_61,B_62] :
      ( k8_relat_1(k2_xboole_0(C_60,B_61),B_62) = B_62
      | ~ v1_relat_1(B_62)
      | ~ r1_tarski(k2_relat_1(B_62),B_61) ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_332,plain,(
    ! [C_63,B_64] :
      ( k8_relat_1(k2_xboole_0(C_63,k2_relat_1(B_64)),B_64) = B_64
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_315])).

tff(c_349,plain,(
    ! [A_10] :
      ( k8_relat_1(k3_relat_1(A_10),A_10) = A_10
      | ~ v1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_332])).

tff(c_424,plain,(
    ! [A_73] :
      ( k2_wellord1(A_73,k3_relat_1(A_73)) = A_73
      | ~ v1_relat_1(A_73)
      | ~ v1_relat_1(A_73)
      | ~ v1_relat_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_349])).

tff(c_22,plain,(
    k2_wellord1('#skF_1',k3_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_430,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_22])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:18:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.25  
% 2.09/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.25  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 2.09/1.25  
% 2.09/1.25  %Foreground sorts:
% 2.09/1.25  
% 2.09/1.25  
% 2.09/1.25  %Background operators:
% 2.09/1.25  
% 2.09/1.25  
% 2.09/1.25  %Foreground operators:
% 2.09/1.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.09/1.25  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.09/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.25  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.09/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.25  
% 2.09/1.27  tff(f_64, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_wellord1)).
% 2.09/1.27  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.09/1.27  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.09/1.27  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.09/1.27  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 2.09/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.09/1.27  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.09/1.27  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.09/1.27  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.27  tff(c_51, plain, (![A_27]: (k2_xboole_0(k1_relat_1(A_27), k2_relat_1(A_27))=k3_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.27  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.27  tff(c_60, plain, (![A_27]: (r1_tarski(k1_relat_1(A_27), k3_relat_1(A_27)) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_51, c_10])).
% 2.09/1.27  tff(c_122, plain, (![B_38, A_39]: (k7_relat_1(B_38, A_39)=B_38 | ~r1_tarski(k1_relat_1(B_38), A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.27  tff(c_154, plain, (![A_41]: (k7_relat_1(A_41, k3_relat_1(A_41))=A_41 | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_60, c_122])).
% 2.09/1.27  tff(c_20, plain, (![A_15, B_16]: (k8_relat_1(A_15, k7_relat_1(B_16, A_15))=k2_wellord1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.27  tff(c_391, plain, (![A_70]: (k8_relat_1(k3_relat_1(A_70), A_70)=k2_wellord1(A_70, k3_relat_1(A_70)) | ~v1_relat_1(A_70) | ~v1_relat_1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_154, c_20])).
% 2.09/1.27  tff(c_14, plain, (![A_10]: (k2_xboole_0(k1_relat_1(A_10), k2_relat_1(A_10))=k3_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.27  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.27  tff(c_88, plain, (![A_33, B_34]: (k8_relat_1(A_33, B_34)=B_34 | ~r1_tarski(k2_relat_1(B_34), A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.27  tff(c_315, plain, (![C_60, B_61, B_62]: (k8_relat_1(k2_xboole_0(C_60, B_61), B_62)=B_62 | ~v1_relat_1(B_62) | ~r1_tarski(k2_relat_1(B_62), B_61))), inference(resolution, [status(thm)], [c_8, c_88])).
% 2.09/1.27  tff(c_332, plain, (![C_63, B_64]: (k8_relat_1(k2_xboole_0(C_63, k2_relat_1(B_64)), B_64)=B_64 | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_6, c_315])).
% 2.09/1.27  tff(c_349, plain, (![A_10]: (k8_relat_1(k3_relat_1(A_10), A_10)=A_10 | ~v1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_332])).
% 2.09/1.27  tff(c_424, plain, (![A_73]: (k2_wellord1(A_73, k3_relat_1(A_73))=A_73 | ~v1_relat_1(A_73) | ~v1_relat_1(A_73) | ~v1_relat_1(A_73) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_391, c_349])).
% 2.09/1.27  tff(c_22, plain, (k2_wellord1('#skF_1', k3_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.27  tff(c_430, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_424, c_22])).
% 2.09/1.27  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_430])).
% 2.09/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  
% 2.09/1.27  Inference rules
% 2.09/1.27  ----------------------
% 2.09/1.27  #Ref     : 0
% 2.09/1.27  #Sup     : 93
% 2.09/1.27  #Fact    : 0
% 2.09/1.27  #Define  : 0
% 2.09/1.27  #Split   : 0
% 2.09/1.27  #Chain   : 0
% 2.09/1.27  #Close   : 0
% 2.09/1.27  
% 2.09/1.27  Ordering : KBO
% 2.09/1.27  
% 2.09/1.27  Simplification rules
% 2.09/1.27  ----------------------
% 2.09/1.27  #Subsume      : 2
% 2.09/1.27  #Demod        : 3
% 2.09/1.27  #Tautology    : 47
% 2.09/1.27  #SimpNegUnit  : 0
% 2.09/1.27  #BackRed      : 0
% 2.09/1.27  
% 2.09/1.27  #Partial instantiations: 0
% 2.09/1.27  #Strategies tried      : 1
% 2.09/1.27  
% 2.09/1.27  Timing (in seconds)
% 2.09/1.27  ----------------------
% 2.09/1.27  Preprocessing        : 0.26
% 2.09/1.27  Parsing              : 0.14
% 2.09/1.27  CNF conversion       : 0.02
% 2.09/1.27  Main loop            : 0.25
% 2.09/1.27  Inferencing          : 0.11
% 2.09/1.27  Reduction            : 0.06
% 2.09/1.27  Demodulation         : 0.04
% 2.09/1.27  BG Simplification    : 0.02
% 2.09/1.27  Subsumption          : 0.05
% 2.09/1.27  Abstraction          : 0.01
% 2.09/1.27  MUC search           : 0.00
% 2.09/1.27  Cooper               : 0.00
% 2.09/1.27  Total                : 0.53
% 2.09/1.27  Index Insertion      : 0.00
% 2.09/1.27  Index Deletion       : 0.00
% 2.09/1.27  Index Matching       : 0.00
% 2.09/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
