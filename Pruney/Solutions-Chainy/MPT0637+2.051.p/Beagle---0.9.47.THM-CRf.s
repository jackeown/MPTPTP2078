%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:30 EST 2020

% Result     : Theorem 13.75s
% Output     : CNFRefutation 13.75s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 138 expanded)
%              Number of leaves         :   34 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :   94 ( 176 expanded)
%              Number of equality atoms :   46 (  82 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_55,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_99,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_26,plain,(
    ! [A_28] : v1_relat_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [A_45] : k2_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_89,plain,(
    ! [A_60] :
      ( k8_relat_1(k2_relat_1(A_60),A_60) = A_60
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_98,plain,(
    ! [A_45] :
      ( k8_relat_1(A_45,k6_relat_1(A_45)) = k6_relat_1(A_45)
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_89])).

tff(c_102,plain,(
    ! [A_45] : k8_relat_1(A_45,k6_relat_1(A_45)) = k6_relat_1(A_45) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_98])).

tff(c_48,plain,(
    ! [A_46] : k4_relat_1(k6_relat_1(A_46)) = k6_relat_1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_44,plain,(
    ! [A_45] : k1_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_743,plain,(
    ! [B_134,A_135] :
      ( k3_xboole_0(B_134,k2_zfmisc_1(k1_relat_1(B_134),A_135)) = k8_relat_1(A_135,B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_803,plain,(
    ! [A_45,A_135] :
      ( k3_xboole_0(k6_relat_1(A_45),k2_zfmisc_1(A_45,A_135)) = k8_relat_1(A_135,k6_relat_1(A_45))
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_743])).

tff(c_1704,plain,(
    ! [A_203,A_204] : k3_xboole_0(k6_relat_1(A_203),k2_zfmisc_1(A_203,A_204)) = k8_relat_1(A_204,k6_relat_1(A_203)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_803])).

tff(c_28,plain,(
    ! [A_29,B_30] :
      ( v1_relat_1(k3_xboole_0(A_29,B_30))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1743,plain,(
    ! [A_204,A_203] :
      ( v1_relat_1(k8_relat_1(A_204,k6_relat_1(A_203)))
      | ~ v1_relat_1(k6_relat_1(A_203)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1704,c_28])).

tff(c_1754,plain,(
    ! [A_204,A_203] : v1_relat_1(k8_relat_1(A_204,k6_relat_1(A_203))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1743])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1746,plain,(
    ! [A_204,A_203] : r1_tarski(k8_relat_1(A_204,k6_relat_1(A_203)),k6_relat_1(A_203)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1704,c_8])).

tff(c_1150,plain,(
    ! [A_166,B_167,C_168] :
      ( k8_relat_1(k3_xboole_0(A_166,B_167),C_168) = k8_relat_1(A_166,k8_relat_1(B_167,C_168))
      | ~ v1_relat_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1189,plain,(
    ! [A_166,B_167] :
      ( k8_relat_1(A_166,k8_relat_1(B_167,k6_relat_1(k3_xboole_0(A_166,B_167)))) = k6_relat_1(k3_xboole_0(A_166,B_167))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(A_166,B_167))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_1150])).

tff(c_1197,plain,(
    ! [A_166,B_167] : k8_relat_1(A_166,k8_relat_1(B_167,k6_relat_1(k3_xboole_0(A_166,B_167)))) = k6_relat_1(k3_xboole_0(A_166,B_167)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1189])).

tff(c_8773,plain,(
    ! [A_407,B_408] : k8_relat_1(A_407,k8_relat_1(B_408,k6_relat_1(k3_xboole_0(A_407,B_408)))) = k6_relat_1(k3_xboole_0(A_407,B_408)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1189])).

tff(c_808,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(k8_relat_1(A_136,B_137),B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_830,plain,(
    ! [A_136,B_137] :
      ( k8_relat_1(A_136,B_137) = B_137
      | ~ r1_tarski(B_137,k8_relat_1(A_136,B_137))
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_808,c_2])).

tff(c_8806,plain,(
    ! [A_407,B_408] :
      ( k8_relat_1(A_407,k8_relat_1(B_408,k6_relat_1(k3_xboole_0(A_407,B_408)))) = k8_relat_1(B_408,k6_relat_1(k3_xboole_0(A_407,B_408)))
      | ~ r1_tarski(k8_relat_1(B_408,k6_relat_1(k3_xboole_0(A_407,B_408))),k6_relat_1(k3_xboole_0(A_407,B_408)))
      | ~ v1_relat_1(k8_relat_1(B_408,k6_relat_1(k3_xboole_0(A_407,B_408)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8773,c_830])).

tff(c_39639,plain,(
    ! [B_851,A_852] : k8_relat_1(B_851,k6_relat_1(k3_xboole_0(A_852,B_851))) = k6_relat_1(k3_xboole_0(A_852,B_851)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1754,c_1746,c_1197,c_8806])).

tff(c_30,plain,(
    ! [B_32,A_31] :
      ( k5_relat_1(B_32,k6_relat_1(A_31)) = k8_relat_1(A_31,B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1305,plain,(
    ! [B_182,A_183] :
      ( k5_relat_1(k4_relat_1(B_182),k4_relat_1(A_183)) = k4_relat_1(k5_relat_1(A_183,B_182))
      | ~ v1_relat_1(B_182)
      | ~ v1_relat_1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1314,plain,(
    ! [A_46,A_183] :
      ( k5_relat_1(k6_relat_1(A_46),k4_relat_1(A_183)) = k4_relat_1(k5_relat_1(A_183,k6_relat_1(A_46)))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1305])).

tff(c_3328,plain,(
    ! [A_280,A_281] :
      ( k5_relat_1(k6_relat_1(A_280),k4_relat_1(A_281)) = k4_relat_1(k5_relat_1(A_281,k6_relat_1(A_280)))
      | ~ v1_relat_1(A_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1314])).

tff(c_3357,plain,(
    ! [A_46,A_280] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_46),k6_relat_1(A_280))) = k5_relat_1(k6_relat_1(A_280),k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_3328])).

tff(c_4145,plain,(
    ! [A_310,A_311] : k4_relat_1(k5_relat_1(k6_relat_1(A_310),k6_relat_1(A_311))) = k5_relat_1(k6_relat_1(A_311),k6_relat_1(A_310)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3357])).

tff(c_4181,plain,(
    ! [A_31,A_310] :
      ( k5_relat_1(k6_relat_1(A_31),k6_relat_1(A_310)) = k4_relat_1(k8_relat_1(A_31,k6_relat_1(A_310)))
      | ~ v1_relat_1(k6_relat_1(A_310)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4145])).

tff(c_4463,plain,(
    ! [A_316,A_317] : k5_relat_1(k6_relat_1(A_316),k6_relat_1(A_317)) = k4_relat_1(k8_relat_1(A_316,k6_relat_1(A_317))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4181])).

tff(c_4502,plain,(
    ! [A_316,A_317] :
      ( k4_relat_1(k8_relat_1(A_316,k6_relat_1(A_317))) = k8_relat_1(A_317,k6_relat_1(A_316))
      | ~ v1_relat_1(k6_relat_1(A_316)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4463,c_30])).

tff(c_4548,plain,(
    ! [A_316,A_317] : k4_relat_1(k8_relat_1(A_316,k6_relat_1(A_317))) = k8_relat_1(A_317,k6_relat_1(A_316)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4502])).

tff(c_39859,plain,(
    ! [A_852,B_851] : k8_relat_1(k3_xboole_0(A_852,B_851),k6_relat_1(B_851)) = k4_relat_1(k6_relat_1(k3_xboole_0(A_852,B_851))) ),
    inference(superposition,[status(thm),theory(equality)],[c_39639,c_4548])).

tff(c_41546,plain,(
    ! [A_868,B_869] : k8_relat_1(k3_xboole_0(A_868,B_869),k6_relat_1(B_869)) = k6_relat_1(k3_xboole_0(A_868,B_869)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_39859])).

tff(c_36,plain,(
    ! [A_36,B_37,C_38] :
      ( k8_relat_1(k3_xboole_0(A_36,B_37),C_38) = k8_relat_1(A_36,k8_relat_1(B_37,C_38))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_41826,plain,(
    ! [A_868,B_869] :
      ( k8_relat_1(A_868,k8_relat_1(B_869,k6_relat_1(B_869))) = k6_relat_1(k3_xboole_0(A_868,B_869))
      | ~ v1_relat_1(k6_relat_1(B_869)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41546,c_36])).

tff(c_42009,plain,(
    ! [A_868,B_869] : k8_relat_1(A_868,k6_relat_1(B_869)) = k6_relat_1(k3_xboole_0(A_868,B_869)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_102,c_41826])).

tff(c_237,plain,(
    ! [B_80,A_81] :
      ( k5_relat_1(B_80,k6_relat_1(A_81)) = k8_relat_1(A_81,B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_250,plain,
    ( k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_56])).

tff(c_258,plain,(
    k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_250])).

tff(c_42185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42009,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:57:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.75/7.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/7.07  
% 13.75/7.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/7.08  %$ r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 13.75/7.08  
% 13.75/7.08  %Foreground sorts:
% 13.75/7.08  
% 13.75/7.08  
% 13.75/7.08  %Background operators:
% 13.75/7.08  
% 13.75/7.08  
% 13.75/7.08  %Foreground operators:
% 13.75/7.08  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 13.75/7.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.75/7.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.75/7.08  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.75/7.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.75/7.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.75/7.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.75/7.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.75/7.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.75/7.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.75/7.08  tff('#skF_2', type, '#skF_2': $i).
% 13.75/7.08  tff('#skF_1', type, '#skF_1': $i).
% 13.75/7.08  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.75/7.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.75/7.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.75/7.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.75/7.08  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.75/7.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.75/7.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.75/7.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.75/7.08  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 13.75/7.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.75/7.08  
% 13.75/7.09  tff(f_55, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 13.75/7.09  tff(f_97, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 13.75/7.09  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 13.75/7.09  tff(f_99, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 13.75/7.09  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 13.75/7.09  tff(f_59, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 13.75/7.09  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.75/7.09  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 13.75/7.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.75/7.09  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 13.75/7.09  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 13.75/7.09  tff(f_114, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 13.75/7.09  tff(c_26, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.75/7.09  tff(c_46, plain, (![A_45]: (k2_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.75/7.09  tff(c_89, plain, (![A_60]: (k8_relat_1(k2_relat_1(A_60), A_60)=A_60 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.75/7.09  tff(c_98, plain, (![A_45]: (k8_relat_1(A_45, k6_relat_1(A_45))=k6_relat_1(A_45) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_89])).
% 13.75/7.09  tff(c_102, plain, (![A_45]: (k8_relat_1(A_45, k6_relat_1(A_45))=k6_relat_1(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_98])).
% 13.75/7.09  tff(c_48, plain, (![A_46]: (k4_relat_1(k6_relat_1(A_46))=k6_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.75/7.09  tff(c_44, plain, (![A_45]: (k1_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.75/7.09  tff(c_743, plain, (![B_134, A_135]: (k3_xboole_0(B_134, k2_zfmisc_1(k1_relat_1(B_134), A_135))=k8_relat_1(A_135, B_134) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.75/7.09  tff(c_803, plain, (![A_45, A_135]: (k3_xboole_0(k6_relat_1(A_45), k2_zfmisc_1(A_45, A_135))=k8_relat_1(A_135, k6_relat_1(A_45)) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_743])).
% 13.75/7.09  tff(c_1704, plain, (![A_203, A_204]: (k3_xboole_0(k6_relat_1(A_203), k2_zfmisc_1(A_203, A_204))=k8_relat_1(A_204, k6_relat_1(A_203)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_803])).
% 13.75/7.09  tff(c_28, plain, (![A_29, B_30]: (v1_relat_1(k3_xboole_0(A_29, B_30)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.75/7.09  tff(c_1743, plain, (![A_204, A_203]: (v1_relat_1(k8_relat_1(A_204, k6_relat_1(A_203))) | ~v1_relat_1(k6_relat_1(A_203)))), inference(superposition, [status(thm), theory('equality')], [c_1704, c_28])).
% 13.75/7.09  tff(c_1754, plain, (![A_204, A_203]: (v1_relat_1(k8_relat_1(A_204, k6_relat_1(A_203))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1743])).
% 13.75/7.09  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.75/7.09  tff(c_1746, plain, (![A_204, A_203]: (r1_tarski(k8_relat_1(A_204, k6_relat_1(A_203)), k6_relat_1(A_203)))), inference(superposition, [status(thm), theory('equality')], [c_1704, c_8])).
% 13.75/7.09  tff(c_1150, plain, (![A_166, B_167, C_168]: (k8_relat_1(k3_xboole_0(A_166, B_167), C_168)=k8_relat_1(A_166, k8_relat_1(B_167, C_168)) | ~v1_relat_1(C_168))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.75/7.09  tff(c_1189, plain, (![A_166, B_167]: (k8_relat_1(A_166, k8_relat_1(B_167, k6_relat_1(k3_xboole_0(A_166, B_167))))=k6_relat_1(k3_xboole_0(A_166, B_167)) | ~v1_relat_1(k6_relat_1(k3_xboole_0(A_166, B_167))))), inference(superposition, [status(thm), theory('equality')], [c_102, c_1150])).
% 13.75/7.09  tff(c_1197, plain, (![A_166, B_167]: (k8_relat_1(A_166, k8_relat_1(B_167, k6_relat_1(k3_xboole_0(A_166, B_167))))=k6_relat_1(k3_xboole_0(A_166, B_167)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1189])).
% 13.75/7.09  tff(c_8773, plain, (![A_407, B_408]: (k8_relat_1(A_407, k8_relat_1(B_408, k6_relat_1(k3_xboole_0(A_407, B_408))))=k6_relat_1(k3_xboole_0(A_407, B_408)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1189])).
% 13.75/7.09  tff(c_808, plain, (![A_136, B_137]: (r1_tarski(k8_relat_1(A_136, B_137), B_137) | ~v1_relat_1(B_137))), inference(superposition, [status(thm), theory('equality')], [c_743, c_8])).
% 13.75/7.09  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.75/7.09  tff(c_830, plain, (![A_136, B_137]: (k8_relat_1(A_136, B_137)=B_137 | ~r1_tarski(B_137, k8_relat_1(A_136, B_137)) | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_808, c_2])).
% 13.75/7.09  tff(c_8806, plain, (![A_407, B_408]: (k8_relat_1(A_407, k8_relat_1(B_408, k6_relat_1(k3_xboole_0(A_407, B_408))))=k8_relat_1(B_408, k6_relat_1(k3_xboole_0(A_407, B_408))) | ~r1_tarski(k8_relat_1(B_408, k6_relat_1(k3_xboole_0(A_407, B_408))), k6_relat_1(k3_xboole_0(A_407, B_408))) | ~v1_relat_1(k8_relat_1(B_408, k6_relat_1(k3_xboole_0(A_407, B_408)))))), inference(superposition, [status(thm), theory('equality')], [c_8773, c_830])).
% 13.75/7.09  tff(c_39639, plain, (![B_851, A_852]: (k8_relat_1(B_851, k6_relat_1(k3_xboole_0(A_852, B_851)))=k6_relat_1(k3_xboole_0(A_852, B_851)))), inference(demodulation, [status(thm), theory('equality')], [c_1754, c_1746, c_1197, c_8806])).
% 13.75/7.09  tff(c_30, plain, (![B_32, A_31]: (k5_relat_1(B_32, k6_relat_1(A_31))=k8_relat_1(A_31, B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.75/7.09  tff(c_1305, plain, (![B_182, A_183]: (k5_relat_1(k4_relat_1(B_182), k4_relat_1(A_183))=k4_relat_1(k5_relat_1(A_183, B_182)) | ~v1_relat_1(B_182) | ~v1_relat_1(A_183))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.75/7.09  tff(c_1314, plain, (![A_46, A_183]: (k5_relat_1(k6_relat_1(A_46), k4_relat_1(A_183))=k4_relat_1(k5_relat_1(A_183, k6_relat_1(A_46))) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(A_183))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1305])).
% 13.75/7.09  tff(c_3328, plain, (![A_280, A_281]: (k5_relat_1(k6_relat_1(A_280), k4_relat_1(A_281))=k4_relat_1(k5_relat_1(A_281, k6_relat_1(A_280))) | ~v1_relat_1(A_281))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1314])).
% 13.75/7.09  tff(c_3357, plain, (![A_46, A_280]: (k4_relat_1(k5_relat_1(k6_relat_1(A_46), k6_relat_1(A_280)))=k5_relat_1(k6_relat_1(A_280), k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_3328])).
% 13.75/7.09  tff(c_4145, plain, (![A_310, A_311]: (k4_relat_1(k5_relat_1(k6_relat_1(A_310), k6_relat_1(A_311)))=k5_relat_1(k6_relat_1(A_311), k6_relat_1(A_310)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3357])).
% 13.75/7.09  tff(c_4181, plain, (![A_31, A_310]: (k5_relat_1(k6_relat_1(A_31), k6_relat_1(A_310))=k4_relat_1(k8_relat_1(A_31, k6_relat_1(A_310))) | ~v1_relat_1(k6_relat_1(A_310)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_4145])).
% 13.75/7.09  tff(c_4463, plain, (![A_316, A_317]: (k5_relat_1(k6_relat_1(A_316), k6_relat_1(A_317))=k4_relat_1(k8_relat_1(A_316, k6_relat_1(A_317))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4181])).
% 13.75/7.09  tff(c_4502, plain, (![A_316, A_317]: (k4_relat_1(k8_relat_1(A_316, k6_relat_1(A_317)))=k8_relat_1(A_317, k6_relat_1(A_316)) | ~v1_relat_1(k6_relat_1(A_316)))), inference(superposition, [status(thm), theory('equality')], [c_4463, c_30])).
% 13.75/7.09  tff(c_4548, plain, (![A_316, A_317]: (k4_relat_1(k8_relat_1(A_316, k6_relat_1(A_317)))=k8_relat_1(A_317, k6_relat_1(A_316)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4502])).
% 13.75/7.09  tff(c_39859, plain, (![A_852, B_851]: (k8_relat_1(k3_xboole_0(A_852, B_851), k6_relat_1(B_851))=k4_relat_1(k6_relat_1(k3_xboole_0(A_852, B_851))))), inference(superposition, [status(thm), theory('equality')], [c_39639, c_4548])).
% 13.75/7.09  tff(c_41546, plain, (![A_868, B_869]: (k8_relat_1(k3_xboole_0(A_868, B_869), k6_relat_1(B_869))=k6_relat_1(k3_xboole_0(A_868, B_869)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_39859])).
% 13.75/7.09  tff(c_36, plain, (![A_36, B_37, C_38]: (k8_relat_1(k3_xboole_0(A_36, B_37), C_38)=k8_relat_1(A_36, k8_relat_1(B_37, C_38)) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.75/7.09  tff(c_41826, plain, (![A_868, B_869]: (k8_relat_1(A_868, k8_relat_1(B_869, k6_relat_1(B_869)))=k6_relat_1(k3_xboole_0(A_868, B_869)) | ~v1_relat_1(k6_relat_1(B_869)))), inference(superposition, [status(thm), theory('equality')], [c_41546, c_36])).
% 13.75/7.09  tff(c_42009, plain, (![A_868, B_869]: (k8_relat_1(A_868, k6_relat_1(B_869))=k6_relat_1(k3_xboole_0(A_868, B_869)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_102, c_41826])).
% 13.75/7.09  tff(c_237, plain, (![B_80, A_81]: (k5_relat_1(B_80, k6_relat_1(A_81))=k8_relat_1(A_81, B_80) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.75/7.09  tff(c_56, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.75/7.09  tff(c_250, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_237, c_56])).
% 13.75/7.09  tff(c_258, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_250])).
% 13.75/7.09  tff(c_42185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42009, c_258])).
% 13.75/7.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/7.09  
% 13.75/7.09  Inference rules
% 13.75/7.09  ----------------------
% 13.75/7.09  #Ref     : 0
% 13.75/7.09  #Sup     : 9607
% 13.75/7.09  #Fact    : 0
% 13.75/7.09  #Define  : 0
% 13.75/7.09  #Split   : 2
% 13.75/7.09  #Chain   : 0
% 13.75/7.09  #Close   : 0
% 13.75/7.09  
% 13.75/7.09  Ordering : KBO
% 13.75/7.09  
% 13.75/7.09  Simplification rules
% 13.75/7.09  ----------------------
% 13.75/7.09  #Subsume      : 590
% 13.75/7.09  #Demod        : 5036
% 13.75/7.09  #Tautology    : 2840
% 13.75/7.09  #SimpNegUnit  : 0
% 13.75/7.09  #BackRed      : 100
% 13.75/7.09  
% 13.75/7.09  #Partial instantiations: 0
% 13.75/7.09  #Strategies tried      : 1
% 13.75/7.09  
% 13.75/7.09  Timing (in seconds)
% 13.75/7.09  ----------------------
% 13.75/7.09  Preprocessing        : 0.35
% 13.75/7.09  Parsing              : 0.19
% 13.75/7.09  CNF conversion       : 0.02
% 13.75/7.09  Main loop            : 5.97
% 13.75/7.09  Inferencing          : 0.94
% 13.75/7.09  Reduction            : 2.58
% 13.75/7.09  Demodulation         : 2.24
% 13.75/7.09  BG Simplification    : 0.14
% 13.75/7.10  Subsumption          : 1.92
% 13.75/7.10  Abstraction          : 0.19
% 13.75/7.10  MUC search           : 0.00
% 13.75/7.10  Cooper               : 0.00
% 13.75/7.10  Total                : 6.35
% 13.75/7.10  Index Insertion      : 0.00
% 13.75/7.10  Index Deletion       : 0.00
% 13.75/7.10  Index Matching       : 0.00
% 13.75/7.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
