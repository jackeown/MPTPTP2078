%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:07 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   65 (  78 expanded)
%              Number of leaves         :   34 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :   61 (  76 expanded)
%              Number of equality atoms :   35 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_45,B_46] :
      ( v1_relat_1(k7_relat_1(A_45,B_46))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [C_49,A_47,B_48] :
      ( k7_relat_1(k7_relat_1(C_49,A_47),B_48) = k7_relat_1(C_49,k3_xboole_0(A_47,B_48))
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [B_51,A_50] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_51,A_50)),k1_relat_1(B_51))
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_124,plain,(
    ! [B_70,A_71] :
      ( k7_relat_1(B_70,A_71) = B_70
      | ~ r1_tarski(k1_relat_1(B_70),A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_973,plain,(
    ! [B_147,A_148] :
      ( k7_relat_1(k7_relat_1(B_147,A_148),k1_relat_1(B_147)) = k7_relat_1(B_147,A_148)
      | ~ v1_relat_1(k7_relat_1(B_147,A_148))
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_2958,plain,(
    ! [C_213,A_214] :
      ( k7_relat_1(C_213,k3_xboole_0(A_214,k1_relat_1(C_213))) = k7_relat_1(C_213,A_214)
      | ~ v1_relat_1(k7_relat_1(C_213,A_214))
      | ~ v1_relat_1(C_213)
      | ~ v1_relat_1(C_213) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_973])).

tff(c_10,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_244,plain,(
    ! [A_81,B_82,C_83] : k2_xboole_0(k2_tarski(A_81,B_82),k1_tarski(C_83)) = k1_enumset1(A_81,B_82,C_83) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_253,plain,(
    ! [A_13,C_83] : k2_xboole_0(k1_tarski(A_13),k1_tarski(C_83)) = k1_enumset1(A_13,A_13,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_244])).

tff(c_256,plain,(
    ! [A_13,C_83] : k2_xboole_0(k1_tarski(A_13),k1_tarski(C_83)) = k2_tarski(A_13,C_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_253])).

tff(c_14,plain,(
    ! [A_19,B_20,C_21,D_22] : k3_enumset1(A_19,A_19,B_20,C_21,D_22) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_328,plain,(
    ! [E_100,C_102,D_103,A_99,B_101] : k2_xboole_0(k2_tarski(A_99,B_101),k1_enumset1(C_102,D_103,E_100)) = k3_enumset1(A_99,B_101,C_102,D_103,E_100) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_346,plain,(
    ! [A_13,C_102,D_103,E_100] : k3_enumset1(A_13,A_13,C_102,D_103,E_100) = k2_xboole_0(k1_tarski(A_13),k1_enumset1(C_102,D_103,E_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_328])).

tff(c_350,plain,(
    ! [A_104,C_105,D_106,E_107] : k2_xboole_0(k1_tarski(A_104),k1_enumset1(C_105,D_106,E_107)) = k2_enumset1(A_104,C_105,D_106,E_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_346])).

tff(c_370,plain,(
    ! [A_108,A_109,B_110] : k2_xboole_0(k1_tarski(A_108),k2_tarski(A_109,B_110)) = k2_enumset1(A_108,A_109,A_109,B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_350])).

tff(c_129,plain,(
    ! [D_72,C_73,B_74,A_75] : k2_enumset1(D_72,C_73,B_74,A_75) = k2_enumset1(A_75,B_74,C_73,D_72) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_16,B_17,C_18] : k2_enumset1(A_16,A_16,B_17,C_18) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    ! [D_72,C_73,B_74] : k2_enumset1(D_72,C_73,B_74,B_74) = k1_enumset1(B_74,C_73,D_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_12])).

tff(c_380,plain,(
    ! [A_108,B_110] : k2_xboole_0(k1_tarski(A_108),k2_tarski(B_110,B_110)) = k1_enumset1(B_110,B_110,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_145])).

tff(c_434,plain,(
    ! [B_117,A_118] : k2_tarski(B_117,A_118) = k2_tarski(A_118,B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_10,c_8,c_380])).

tff(c_24,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_497,plain,(
    ! [B_119,A_120] : k1_setfam_1(k2_tarski(B_119,A_120)) = k3_xboole_0(A_120,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_24])).

tff(c_503,plain,(
    ! [B_119,A_120] : k3_xboole_0(B_119,A_120) = k3_xboole_0(A_120,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_24])).

tff(c_34,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_523,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_34])).

tff(c_2980,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2958,c_523])).

tff(c_3020,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2980])).

tff(c_3024,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_3020])).

tff(c_3028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:47:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.76  
% 4.32/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.77  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.32/1.77  
% 4.32/1.77  %Foreground sorts:
% 4.32/1.77  
% 4.32/1.77  
% 4.32/1.77  %Background operators:
% 4.32/1.77  
% 4.32/1.77  
% 4.32/1.77  %Foreground operators:
% 4.32/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.32/1.77  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.32/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.32/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.32/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.32/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.32/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.32/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.32/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.32/1.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.77  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.32/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.32/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.32/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.32/1.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.32/1.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.32/1.77  
% 4.39/1.78  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 4.39/1.78  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.39/1.78  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 4.39/1.78  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 4.39/1.78  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 4.39/1.78  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.39/1.78  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.39/1.78  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 4.39/1.78  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.39/1.78  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 4.39/1.78  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 4.39/1.78  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.39/1.78  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.39/1.78  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.39/1.78  tff(c_26, plain, (![A_45, B_46]: (v1_relat_1(k7_relat_1(A_45, B_46)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.39/1.78  tff(c_28, plain, (![C_49, A_47, B_48]: (k7_relat_1(k7_relat_1(C_49, A_47), B_48)=k7_relat_1(C_49, k3_xboole_0(A_47, B_48)) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.39/1.78  tff(c_30, plain, (![B_51, A_50]: (r1_tarski(k1_relat_1(k7_relat_1(B_51, A_50)), k1_relat_1(B_51)) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.39/1.78  tff(c_124, plain, (![B_70, A_71]: (k7_relat_1(B_70, A_71)=B_70 | ~r1_tarski(k1_relat_1(B_70), A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.39/1.78  tff(c_973, plain, (![B_147, A_148]: (k7_relat_1(k7_relat_1(B_147, A_148), k1_relat_1(B_147))=k7_relat_1(B_147, A_148) | ~v1_relat_1(k7_relat_1(B_147, A_148)) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_30, c_124])).
% 4.39/1.78  tff(c_2958, plain, (![C_213, A_214]: (k7_relat_1(C_213, k3_xboole_0(A_214, k1_relat_1(C_213)))=k7_relat_1(C_213, A_214) | ~v1_relat_1(k7_relat_1(C_213, A_214)) | ~v1_relat_1(C_213) | ~v1_relat_1(C_213))), inference(superposition, [status(thm), theory('equality')], [c_28, c_973])).
% 4.39/1.78  tff(c_10, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.39/1.78  tff(c_8, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.39/1.78  tff(c_244, plain, (![A_81, B_82, C_83]: (k2_xboole_0(k2_tarski(A_81, B_82), k1_tarski(C_83))=k1_enumset1(A_81, B_82, C_83))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.39/1.78  tff(c_253, plain, (![A_13, C_83]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(C_83))=k1_enumset1(A_13, A_13, C_83))), inference(superposition, [status(thm), theory('equality')], [c_8, c_244])).
% 4.39/1.78  tff(c_256, plain, (![A_13, C_83]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(C_83))=k2_tarski(A_13, C_83))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_253])).
% 4.39/1.78  tff(c_14, plain, (![A_19, B_20, C_21, D_22]: (k3_enumset1(A_19, A_19, B_20, C_21, D_22)=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.39/1.78  tff(c_328, plain, (![E_100, C_102, D_103, A_99, B_101]: (k2_xboole_0(k2_tarski(A_99, B_101), k1_enumset1(C_102, D_103, E_100))=k3_enumset1(A_99, B_101, C_102, D_103, E_100))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.39/1.78  tff(c_346, plain, (![A_13, C_102, D_103, E_100]: (k3_enumset1(A_13, A_13, C_102, D_103, E_100)=k2_xboole_0(k1_tarski(A_13), k1_enumset1(C_102, D_103, E_100)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_328])).
% 4.39/1.78  tff(c_350, plain, (![A_104, C_105, D_106, E_107]: (k2_xboole_0(k1_tarski(A_104), k1_enumset1(C_105, D_106, E_107))=k2_enumset1(A_104, C_105, D_106, E_107))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_346])).
% 4.39/1.78  tff(c_370, plain, (![A_108, A_109, B_110]: (k2_xboole_0(k1_tarski(A_108), k2_tarski(A_109, B_110))=k2_enumset1(A_108, A_109, A_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_10, c_350])).
% 4.39/1.78  tff(c_129, plain, (![D_72, C_73, B_74, A_75]: (k2_enumset1(D_72, C_73, B_74, A_75)=k2_enumset1(A_75, B_74, C_73, D_72))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.39/1.78  tff(c_12, plain, (![A_16, B_17, C_18]: (k2_enumset1(A_16, A_16, B_17, C_18)=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.39/1.78  tff(c_145, plain, (![D_72, C_73, B_74]: (k2_enumset1(D_72, C_73, B_74, B_74)=k1_enumset1(B_74, C_73, D_72))), inference(superposition, [status(thm), theory('equality')], [c_129, c_12])).
% 4.39/1.78  tff(c_380, plain, (![A_108, B_110]: (k2_xboole_0(k1_tarski(A_108), k2_tarski(B_110, B_110))=k1_enumset1(B_110, B_110, A_108))), inference(superposition, [status(thm), theory('equality')], [c_370, c_145])).
% 4.39/1.78  tff(c_434, plain, (![B_117, A_118]: (k2_tarski(B_117, A_118)=k2_tarski(A_118, B_117))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_10, c_8, c_380])).
% 4.39/1.78  tff(c_24, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.39/1.78  tff(c_497, plain, (![B_119, A_120]: (k1_setfam_1(k2_tarski(B_119, A_120))=k3_xboole_0(A_120, B_119))), inference(superposition, [status(thm), theory('equality')], [c_434, c_24])).
% 4.39/1.78  tff(c_503, plain, (![B_119, A_120]: (k3_xboole_0(B_119, A_120)=k3_xboole_0(A_120, B_119))), inference(superposition, [status(thm), theory('equality')], [c_497, c_24])).
% 4.39/1.78  tff(c_34, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.39/1.78  tff(c_523, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_34])).
% 4.39/1.78  tff(c_2980, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2958, c_523])).
% 4.39/1.78  tff(c_3020, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2980])).
% 4.39/1.78  tff(c_3024, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_3020])).
% 4.39/1.78  tff(c_3028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_3024])).
% 4.39/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.78  
% 4.39/1.78  Inference rules
% 4.39/1.78  ----------------------
% 4.39/1.78  #Ref     : 0
% 4.39/1.78  #Sup     : 734
% 4.39/1.78  #Fact    : 0
% 4.39/1.78  #Define  : 0
% 4.39/1.78  #Split   : 0
% 4.39/1.78  #Chain   : 0
% 4.39/1.78  #Close   : 0
% 4.39/1.78  
% 4.39/1.78  Ordering : KBO
% 4.39/1.78  
% 4.39/1.78  Simplification rules
% 4.39/1.78  ----------------------
% 4.39/1.78  #Subsume      : 107
% 4.39/1.78  #Demod        : 444
% 4.39/1.78  #Tautology    : 472
% 4.39/1.78  #SimpNegUnit  : 0
% 4.39/1.78  #BackRed      : 4
% 4.39/1.78  
% 4.39/1.78  #Partial instantiations: 0
% 4.39/1.78  #Strategies tried      : 1
% 4.39/1.78  
% 4.39/1.78  Timing (in seconds)
% 4.39/1.78  ----------------------
% 4.39/1.78  Preprocessing        : 0.33
% 4.39/1.78  Parsing              : 0.18
% 4.39/1.78  CNF conversion       : 0.02
% 4.39/1.78  Main loop            : 0.65
% 4.39/1.78  Inferencing          : 0.24
% 4.39/1.78  Reduction            : 0.27
% 4.39/1.78  Demodulation         : 0.23
% 4.39/1.78  BG Simplification    : 0.03
% 4.39/1.78  Subsumption          : 0.08
% 4.39/1.78  Abstraction          : 0.04
% 4.39/1.78  MUC search           : 0.00
% 4.39/1.78  Cooper               : 0.00
% 4.39/1.78  Total                : 1.01
% 4.39/1.78  Index Insertion      : 0.00
% 4.39/1.78  Index Deletion       : 0.00
% 4.39/1.79  Index Matching       : 0.00
% 4.39/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
