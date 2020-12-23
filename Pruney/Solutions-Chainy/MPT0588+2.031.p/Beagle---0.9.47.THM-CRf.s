%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:07 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   63 (  72 expanded)
%              Number of leaves         :   34 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :   59 (  70 expanded)
%              Number of equality atoms :   33 (  41 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(k7_relat_1(A_44,B_45))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [B_50,A_49] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_50,A_49)),k1_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_200,plain,(
    ! [B_76,A_77] :
      ( k7_relat_1(B_76,A_77) = B_76
      | ~ r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_782,plain,(
    ! [B_137,A_138] :
      ( k7_relat_1(k7_relat_1(B_137,A_138),k1_relat_1(B_137)) = k7_relat_1(B_137,A_138)
      | ~ v1_relat_1(k7_relat_1(B_137,A_138))
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_30,c_200])).

tff(c_28,plain,(
    ! [C_48,A_46,B_47] :
      ( k7_relat_1(k7_relat_1(C_48,A_46),B_47) = k7_relat_1(C_48,k3_xboole_0(A_46,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3750,plain,(
    ! [B_211,A_212] :
      ( k7_relat_1(B_211,k3_xboole_0(A_212,k1_relat_1(B_211))) = k7_relat_1(B_211,A_212)
      | ~ v1_relat_1(B_211)
      | ~ v1_relat_1(k7_relat_1(B_211,A_212))
      | ~ v1_relat_1(B_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_782,c_28])).

tff(c_4,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_18,B_19,C_20,D_21] : k3_enumset1(A_18,A_18,B_19,C_20,D_21) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_284,plain,(
    ! [A_96,C_95,B_94,E_97,D_93] : k2_xboole_0(k2_tarski(A_96,B_94),k1_enumset1(C_95,D_93,E_97)) = k3_enumset1(A_96,B_94,C_95,D_93,E_97) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_296,plain,(
    ! [A_12,C_95,D_93,E_97] : k3_enumset1(A_12,A_12,C_95,D_93,E_97) = k2_xboole_0(k1_tarski(A_12),k1_enumset1(C_95,D_93,E_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_284])).

tff(c_300,plain,(
    ! [A_98,C_99,D_100,E_101] : k2_xboole_0(k1_tarski(A_98),k1_enumset1(C_99,D_100,E_101)) = k2_enumset1(A_98,C_99,D_100,E_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_296])).

tff(c_321,plain,(
    ! [A_108,A_109,B_110] : k2_xboole_0(k1_tarski(A_108),k2_tarski(A_109,B_110)) = k2_enumset1(A_108,A_109,A_109,B_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_300])).

tff(c_153,plain,(
    ! [D_72,B_73,C_74,A_75] : k2_enumset1(D_72,B_73,C_74,A_75) = k2_enumset1(A_75,B_73,C_74,D_72) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_169,plain,(
    ! [D_72,B_73,C_74] : k2_enumset1(D_72,B_73,C_74,B_73) = k1_enumset1(B_73,C_74,D_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_12])).

tff(c_331,plain,(
    ! [A_108,B_110] : k2_xboole_0(k1_tarski(A_108),k2_tarski(B_110,B_110)) = k1_enumset1(B_110,B_110,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_169])).

tff(c_376,plain,(
    ! [B_111,A_112] : k2_tarski(B_111,A_112) = k2_tarski(A_112,B_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10,c_8,c_331])).

tff(c_24,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_442,plain,(
    ! [B_120,A_121] : k1_setfam_1(k2_tarski(B_120,A_121)) = k3_xboole_0(A_121,B_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_24])).

tff(c_448,plain,(
    ! [B_120,A_121] : k3_xboole_0(B_120,A_121) = k3_xboole_0(A_121,B_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_24])).

tff(c_34,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_468,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_34])).

tff(c_3775,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3750,c_468])).

tff(c_3815,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3775])).

tff(c_3819,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_3815])).

tff(c_3823,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3819])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:37:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.75  
% 4.16/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.76  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.16/1.76  
% 4.16/1.76  %Foreground sorts:
% 4.16/1.76  
% 4.16/1.76  
% 4.16/1.76  %Background operators:
% 4.16/1.76  
% 4.16/1.76  
% 4.16/1.76  %Foreground operators:
% 4.16/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.16/1.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.16/1.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.16/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.16/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.16/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.16/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.16/1.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.16/1.76  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.16/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.16/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.16/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.16/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.16/1.76  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.16/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.16/1.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.16/1.76  
% 4.16/1.77  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 4.16/1.77  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.16/1.77  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 4.16/1.77  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 4.16/1.77  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 4.16/1.77  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 4.16/1.77  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.16/1.77  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.16/1.77  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.16/1.77  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 4.16/1.77  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_enumset1)).
% 4.16/1.77  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.16/1.77  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.16/1.77  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.16/1.77  tff(c_26, plain, (![A_44, B_45]: (v1_relat_1(k7_relat_1(A_44, B_45)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.16/1.77  tff(c_30, plain, (![B_50, A_49]: (r1_tarski(k1_relat_1(k7_relat_1(B_50, A_49)), k1_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.16/1.77  tff(c_200, plain, (![B_76, A_77]: (k7_relat_1(B_76, A_77)=B_76 | ~r1_tarski(k1_relat_1(B_76), A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.16/1.77  tff(c_782, plain, (![B_137, A_138]: (k7_relat_1(k7_relat_1(B_137, A_138), k1_relat_1(B_137))=k7_relat_1(B_137, A_138) | ~v1_relat_1(k7_relat_1(B_137, A_138)) | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_30, c_200])).
% 4.16/1.77  tff(c_28, plain, (![C_48, A_46, B_47]: (k7_relat_1(k7_relat_1(C_48, A_46), B_47)=k7_relat_1(C_48, k3_xboole_0(A_46, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.16/1.77  tff(c_3750, plain, (![B_211, A_212]: (k7_relat_1(B_211, k3_xboole_0(A_212, k1_relat_1(B_211)))=k7_relat_1(B_211, A_212) | ~v1_relat_1(B_211) | ~v1_relat_1(k7_relat_1(B_211, A_212)) | ~v1_relat_1(B_211))), inference(superposition, [status(thm), theory('equality')], [c_782, c_28])).
% 4.16/1.77  tff(c_4, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.16/1.77  tff(c_10, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.16/1.77  tff(c_8, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.16/1.77  tff(c_14, plain, (![A_18, B_19, C_20, D_21]: (k3_enumset1(A_18, A_18, B_19, C_20, D_21)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.16/1.77  tff(c_284, plain, (![A_96, C_95, B_94, E_97, D_93]: (k2_xboole_0(k2_tarski(A_96, B_94), k1_enumset1(C_95, D_93, E_97))=k3_enumset1(A_96, B_94, C_95, D_93, E_97))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.77  tff(c_296, plain, (![A_12, C_95, D_93, E_97]: (k3_enumset1(A_12, A_12, C_95, D_93, E_97)=k2_xboole_0(k1_tarski(A_12), k1_enumset1(C_95, D_93, E_97)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_284])).
% 4.16/1.77  tff(c_300, plain, (![A_98, C_99, D_100, E_101]: (k2_xboole_0(k1_tarski(A_98), k1_enumset1(C_99, D_100, E_101))=k2_enumset1(A_98, C_99, D_100, E_101))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_296])).
% 4.16/1.77  tff(c_321, plain, (![A_108, A_109, B_110]: (k2_xboole_0(k1_tarski(A_108), k2_tarski(A_109, B_110))=k2_enumset1(A_108, A_109, A_109, B_110))), inference(superposition, [status(thm), theory('equality')], [c_10, c_300])).
% 4.16/1.77  tff(c_153, plain, (![D_72, B_73, C_74, A_75]: (k2_enumset1(D_72, B_73, C_74, A_75)=k2_enumset1(A_75, B_73, C_74, D_72))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.16/1.77  tff(c_12, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.16/1.77  tff(c_169, plain, (![D_72, B_73, C_74]: (k2_enumset1(D_72, B_73, C_74, B_73)=k1_enumset1(B_73, C_74, D_72))), inference(superposition, [status(thm), theory('equality')], [c_153, c_12])).
% 4.16/1.77  tff(c_331, plain, (![A_108, B_110]: (k2_xboole_0(k1_tarski(A_108), k2_tarski(B_110, B_110))=k1_enumset1(B_110, B_110, A_108))), inference(superposition, [status(thm), theory('equality')], [c_321, c_169])).
% 4.16/1.77  tff(c_376, plain, (![B_111, A_112]: (k2_tarski(B_111, A_112)=k2_tarski(A_112, B_111))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10, c_8, c_331])).
% 4.16/1.77  tff(c_24, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.16/1.77  tff(c_442, plain, (![B_120, A_121]: (k1_setfam_1(k2_tarski(B_120, A_121))=k3_xboole_0(A_121, B_120))), inference(superposition, [status(thm), theory('equality')], [c_376, c_24])).
% 4.16/1.77  tff(c_448, plain, (![B_120, A_121]: (k3_xboole_0(B_120, A_121)=k3_xboole_0(A_121, B_120))), inference(superposition, [status(thm), theory('equality')], [c_442, c_24])).
% 4.16/1.77  tff(c_34, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.16/1.77  tff(c_468, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_448, c_34])).
% 4.16/1.77  tff(c_3775, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3750, c_468])).
% 4.16/1.77  tff(c_3815, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3775])).
% 4.16/1.77  tff(c_3819, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_3815])).
% 4.16/1.77  tff(c_3823, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_3819])).
% 4.16/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.77  
% 4.16/1.77  Inference rules
% 4.16/1.77  ----------------------
% 4.16/1.77  #Ref     : 0
% 4.16/1.77  #Sup     : 922
% 4.16/1.77  #Fact    : 0
% 4.16/1.77  #Define  : 0
% 4.16/1.77  #Split   : 0
% 4.16/1.77  #Chain   : 0
% 4.16/1.77  #Close   : 0
% 4.16/1.77  
% 4.16/1.77  Ordering : KBO
% 4.16/1.77  
% 4.16/1.77  Simplification rules
% 4.16/1.77  ----------------------
% 4.16/1.77  #Subsume      : 142
% 4.16/1.77  #Demod        : 717
% 4.16/1.77  #Tautology    : 589
% 4.16/1.77  #SimpNegUnit  : 0
% 4.16/1.77  #BackRed      : 1
% 4.16/1.77  
% 4.16/1.77  #Partial instantiations: 0
% 4.16/1.77  #Strategies tried      : 1
% 4.16/1.77  
% 4.16/1.77  Timing (in seconds)
% 4.16/1.77  ----------------------
% 4.16/1.77  Preprocessing        : 0.31
% 4.16/1.77  Parsing              : 0.17
% 4.16/1.77  CNF conversion       : 0.02
% 4.16/1.77  Main loop            : 0.71
% 4.16/1.77  Inferencing          : 0.26
% 4.16/1.77  Reduction            : 0.30
% 4.16/1.77  Demodulation         : 0.25
% 4.16/1.77  BG Simplification    : 0.03
% 4.16/1.77  Subsumption          : 0.09
% 4.16/1.77  Abstraction          : 0.04
% 4.16/1.77  MUC search           : 0.00
% 4.16/1.77  Cooper               : 0.00
% 4.16/1.77  Total                : 1.05
% 4.16/1.77  Index Insertion      : 0.00
% 4.16/1.77  Index Deletion       : 0.00
% 4.16/1.77  Index Matching       : 0.00
% 4.16/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
