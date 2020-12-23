%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:10 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 225 expanded)
%              Number of leaves         :   44 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          :  163 ( 338 expanded)
%              Number of equality atoms :   64 ( 148 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_36,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_108,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_54,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_104,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_36,plain,(
    ! [A_43] :
      ( v1_relat_1(k4_relat_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_99,plain,(
    ! [A_61] :
      ( v1_relat_1(A_61)
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_99])).

tff(c_14,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_195,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_207,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_195])).

tff(c_210,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_207])).

tff(c_30,plain,(
    ! [A_38,B_39] : k6_subset_1(A_38,B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_48,B_50] :
      ( k6_subset_1(k4_relat_1(A_48),k4_relat_1(B_50)) = k4_relat_1(k6_subset_1(A_48,B_50))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_327,plain,(
    ! [A_96,B_97] :
      ( k4_xboole_0(k4_relat_1(A_96),k4_relat_1(B_97)) = k4_relat_1(k4_xboole_0(A_96,B_97))
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_44])).

tff(c_334,plain,(
    ! [B_97] :
      ( k4_relat_1(k4_xboole_0(B_97,B_97)) = k1_xboole_0
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_210])).

tff(c_349,plain,(
    ! [B_97] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_334])).

tff(c_353,plain,(
    ! [B_98] :
      ( ~ v1_relat_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_361,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_103,c_353])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_361])).

tff(c_371,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_38,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(k5_relat_1(A_44,B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_133,plain,(
    ! [A_65,B_66] :
      ( v1_xboole_0(k2_zfmisc_1(A_65,B_66))
      | ~ v1_xboole_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [A_69,B_70] :
      ( k2_zfmisc_1(A_69,B_70) = k1_xboole_0
      | ~ v1_xboole_0(B_70) ) ),
    inference(resolution,[status(thm)],[c_133,c_6])).

tff(c_157,plain,(
    ! [A_69] : k2_zfmisc_1(A_69,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_151])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_556,plain,(
    ! [B_111,A_112] :
      ( k2_relat_1(k5_relat_1(B_111,A_112)) = k2_relat_1(A_112)
      | ~ r1_tarski(k1_relat_1(A_112),k2_relat_1(B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_559,plain,(
    ! [B_111] :
      ( k2_relat_1(k5_relat_1(B_111,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_556])).

tff(c_567,plain,(
    ! [B_113] :
      ( k2_relat_1(k5_relat_1(B_113,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_12,c_50,c_559])).

tff(c_42,plain,(
    ! [A_47] :
      ( k3_xboole_0(A_47,k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47))) = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_579,plain,(
    ! [B_113] :
      ( k3_xboole_0(k5_relat_1(B_113,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_113,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_113,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_113,k1_xboole_0))
      | ~ v1_relat_1(B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_42])).

tff(c_590,plain,(
    ! [B_114] :
      ( k5_relat_1(B_114,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_114,k1_xboole_0))
      | ~ v1_relat_1(B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_157,c_579])).

tff(c_600,plain,(
    ! [A_44] :
      ( k5_relat_1(A_44,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_38,c_590])).

tff(c_644,plain,(
    ! [A_121] :
      ( k5_relat_1(A_121,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_600])).

tff(c_666,plain,(
    ! [A_43] :
      ( k5_relat_1(k4_relat_1(A_43),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_36,c_644])).

tff(c_40,plain,(
    ! [A_46] :
      ( k4_relat_1(k4_relat_1(A_46)) = A_46
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_396,plain,(
    ! [B_99,A_100] :
      ( k5_relat_1(k4_relat_1(B_99),k4_relat_1(A_100)) = k4_relat_1(k5_relat_1(A_100,B_99))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_408,plain,(
    ! [A_100] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_100)) = k4_relat_1(k5_relat_1(A_100,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_396])).

tff(c_468,plain,(
    ! [A_108] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_108)) = k4_relat_1(k5_relat_1(A_108,k1_xboole_0))
      | ~ v1_relat_1(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_408])).

tff(c_1348,plain,(
    ! [A_146] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_146),k1_xboole_0)) = k5_relat_1(k1_xboole_0,A_146)
      | ~ v1_relat_1(k4_relat_1(A_146))
      | ~ v1_relat_1(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_468])).

tff(c_1420,plain,(
    ! [A_43] :
      ( k5_relat_1(k1_xboole_0,A_43) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_43))
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_1348])).

tff(c_1440,plain,(
    ! [A_147] :
      ( k5_relat_1(k1_xboole_0,A_147) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_147))
      | ~ v1_relat_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_1420])).

tff(c_1476,plain,(
    ! [A_148] :
      ( k5_relat_1(k1_xboole_0,A_148) = k1_xboole_0
      | ~ v1_relat_1(A_148) ) ),
    inference(resolution,[status(thm)],[c_36,c_1440])).

tff(c_1500,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_1476])).

tff(c_1512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1500])).

tff(c_1513,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1556,plain,(
    ! [A_154,B_155] :
      ( v1_xboole_0(k2_zfmisc_1(A_154,B_155))
      | ~ v1_xboole_0(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1566,plain,(
    ! [A_158,B_159] :
      ( k2_zfmisc_1(A_158,B_159) = k1_xboole_0
      | ~ v1_xboole_0(B_159) ) ),
    inference(resolution,[status(thm)],[c_1556,c_6])).

tff(c_1572,plain,(
    ! [A_158] : k2_zfmisc_1(A_158,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1566])).

tff(c_1818,plain,(
    ! [B_193,A_194] :
      ( k2_relat_1(k5_relat_1(B_193,A_194)) = k2_relat_1(A_194)
      | ~ r1_tarski(k1_relat_1(A_194),k2_relat_1(B_193))
      | ~ v1_relat_1(B_193)
      | ~ v1_relat_1(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1821,plain,(
    ! [B_193] :
      ( k2_relat_1(k5_relat_1(B_193,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_193))
      | ~ v1_relat_1(B_193)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1818])).

tff(c_1863,plain,(
    ! [B_195] :
      ( k2_relat_1(k5_relat_1(B_195,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_12,c_50,c_1821])).

tff(c_1875,plain,(
    ! [B_195] :
      ( k3_xboole_0(k5_relat_1(B_195,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_195,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_195,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_195,k1_xboole_0))
      | ~ v1_relat_1(B_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1863,c_42])).

tff(c_1884,plain,(
    ! [B_196] :
      ( k5_relat_1(B_196,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_196,k1_xboole_0))
      | ~ v1_relat_1(B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1572,c_1875])).

tff(c_1888,plain,(
    ! [A_44] :
      ( k5_relat_1(A_44,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_38,c_1884])).

tff(c_1892,plain,(
    ! [A_197] :
      ( k5_relat_1(A_197,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1888])).

tff(c_1907,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_1892])).

tff(c_1915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1513,c_1907])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:53:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.60  
% 3.80/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.60  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.80/1.60  
% 3.80/1.60  %Foreground sorts:
% 3.80/1.60  
% 3.80/1.60  
% 3.80/1.60  %Background operators:
% 3.80/1.60  
% 3.80/1.60  
% 3.80/1.60  %Foreground operators:
% 3.80/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.80/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.80/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.80/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.80/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.80/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.80/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.80/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.80/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.80/1.60  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.80/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.80/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.80/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.80/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.80/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.80/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.80/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.80/1.60  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.80/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.80/1.60  
% 3.80/1.62  tff(f_115, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.80/1.62  tff(f_68, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.80/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.80/1.62  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.80/1.62  tff(f_40, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.80/1.62  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.80/1.62  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.80/1.62  tff(f_58, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.80/1.62  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_relat_1)).
% 3.80/1.62  tff(f_74, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.80/1.62  tff(f_36, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.80/1.62  tff(f_56, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.80/1.62  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.80/1.62  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.80/1.62  tff(f_108, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.80/1.62  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.80/1.62  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 3.80/1.62  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.80/1.62  tff(f_105, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 3.80/1.62  tff(c_54, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.80/1.62  tff(c_104, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 3.80/1.62  tff(c_56, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.80/1.62  tff(c_36, plain, (![A_43]: (v1_relat_1(k4_relat_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.80/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.80/1.62  tff(c_99, plain, (![A_61]: (v1_relat_1(A_61) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.80/1.62  tff(c_103, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_99])).
% 3.80/1.62  tff(c_14, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.80/1.62  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.80/1.62  tff(c_195, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.80/1.62  tff(c_207, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_195])).
% 3.80/1.62  tff(c_210, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_207])).
% 3.80/1.62  tff(c_30, plain, (![A_38, B_39]: (k6_subset_1(A_38, B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.62  tff(c_44, plain, (![A_48, B_50]: (k6_subset_1(k4_relat_1(A_48), k4_relat_1(B_50))=k4_relat_1(k6_subset_1(A_48, B_50)) | ~v1_relat_1(B_50) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.80/1.62  tff(c_327, plain, (![A_96, B_97]: (k4_xboole_0(k4_relat_1(A_96), k4_relat_1(B_97))=k4_relat_1(k4_xboole_0(A_96, B_97)) | ~v1_relat_1(B_97) | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_44])).
% 3.80/1.62  tff(c_334, plain, (![B_97]: (k4_relat_1(k4_xboole_0(B_97, B_97))=k1_xboole_0 | ~v1_relat_1(B_97) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_327, c_210])).
% 3.80/1.62  tff(c_349, plain, (![B_97]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_97) | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_334])).
% 3.80/1.62  tff(c_353, plain, (![B_98]: (~v1_relat_1(B_98) | ~v1_relat_1(B_98))), inference(splitLeft, [status(thm)], [c_349])).
% 3.80/1.62  tff(c_361, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_103, c_353])).
% 3.80/1.62  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_361])).
% 3.80/1.62  tff(c_371, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_349])).
% 3.80/1.62  tff(c_38, plain, (![A_44, B_45]: (v1_relat_1(k5_relat_1(A_44, B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.80/1.62  tff(c_10, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.80/1.62  tff(c_133, plain, (![A_65, B_66]: (v1_xboole_0(k2_zfmisc_1(A_65, B_66)) | ~v1_xboole_0(B_66))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.80/1.62  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.62  tff(c_151, plain, (![A_69, B_70]: (k2_zfmisc_1(A_69, B_70)=k1_xboole_0 | ~v1_xboole_0(B_70))), inference(resolution, [status(thm)], [c_133, c_6])).
% 3.80/1.62  tff(c_157, plain, (![A_69]: (k2_zfmisc_1(A_69, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_151])).
% 3.80/1.62  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.80/1.62  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.80/1.62  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.80/1.62  tff(c_556, plain, (![B_111, A_112]: (k2_relat_1(k5_relat_1(B_111, A_112))=k2_relat_1(A_112) | ~r1_tarski(k1_relat_1(A_112), k2_relat_1(B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.80/1.62  tff(c_559, plain, (![B_111]: (k2_relat_1(k5_relat_1(B_111, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_556])).
% 3.80/1.62  tff(c_567, plain, (![B_113]: (k2_relat_1(k5_relat_1(B_113, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_12, c_50, c_559])).
% 3.80/1.62  tff(c_42, plain, (![A_47]: (k3_xboole_0(A_47, k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47)))=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.80/1.62  tff(c_579, plain, (![B_113]: (k3_xboole_0(k5_relat_1(B_113, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_113, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_113, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_113, k1_xboole_0)) | ~v1_relat_1(B_113))), inference(superposition, [status(thm), theory('equality')], [c_567, c_42])).
% 3.80/1.62  tff(c_590, plain, (![B_114]: (k5_relat_1(B_114, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_114, k1_xboole_0)) | ~v1_relat_1(B_114))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_157, c_579])).
% 3.80/1.62  tff(c_600, plain, (![A_44]: (k5_relat_1(A_44, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_38, c_590])).
% 3.80/1.62  tff(c_644, plain, (![A_121]: (k5_relat_1(A_121, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_600])).
% 3.80/1.62  tff(c_666, plain, (![A_43]: (k5_relat_1(k4_relat_1(A_43), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_36, c_644])).
% 3.80/1.62  tff(c_40, plain, (![A_46]: (k4_relat_1(k4_relat_1(A_46))=A_46 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.80/1.62  tff(c_396, plain, (![B_99, A_100]: (k5_relat_1(k4_relat_1(B_99), k4_relat_1(A_100))=k4_relat_1(k5_relat_1(A_100, B_99)) | ~v1_relat_1(B_99) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.80/1.62  tff(c_408, plain, (![A_100]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_100))=k4_relat_1(k5_relat_1(A_100, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_371, c_396])).
% 3.80/1.62  tff(c_468, plain, (![A_108]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_108))=k4_relat_1(k5_relat_1(A_108, k1_xboole_0)) | ~v1_relat_1(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_408])).
% 3.80/1.62  tff(c_1348, plain, (![A_146]: (k4_relat_1(k5_relat_1(k4_relat_1(A_146), k1_xboole_0))=k5_relat_1(k1_xboole_0, A_146) | ~v1_relat_1(k4_relat_1(A_146)) | ~v1_relat_1(A_146))), inference(superposition, [status(thm), theory('equality')], [c_40, c_468])).
% 3.80/1.62  tff(c_1420, plain, (![A_43]: (k5_relat_1(k1_xboole_0, A_43)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_43)) | ~v1_relat_1(A_43) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_666, c_1348])).
% 3.80/1.62  tff(c_1440, plain, (![A_147]: (k5_relat_1(k1_xboole_0, A_147)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_147)) | ~v1_relat_1(A_147) | ~v1_relat_1(A_147))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_1420])).
% 3.80/1.62  tff(c_1476, plain, (![A_148]: (k5_relat_1(k1_xboole_0, A_148)=k1_xboole_0 | ~v1_relat_1(A_148))), inference(resolution, [status(thm)], [c_36, c_1440])).
% 3.80/1.62  tff(c_1500, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_1476])).
% 3.80/1.62  tff(c_1512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_1500])).
% 3.80/1.62  tff(c_1513, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.80/1.62  tff(c_1556, plain, (![A_154, B_155]: (v1_xboole_0(k2_zfmisc_1(A_154, B_155)) | ~v1_xboole_0(B_155))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.80/1.62  tff(c_1566, plain, (![A_158, B_159]: (k2_zfmisc_1(A_158, B_159)=k1_xboole_0 | ~v1_xboole_0(B_159))), inference(resolution, [status(thm)], [c_1556, c_6])).
% 3.80/1.62  tff(c_1572, plain, (![A_158]: (k2_zfmisc_1(A_158, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1566])).
% 3.80/1.62  tff(c_1818, plain, (![B_193, A_194]: (k2_relat_1(k5_relat_1(B_193, A_194))=k2_relat_1(A_194) | ~r1_tarski(k1_relat_1(A_194), k2_relat_1(B_193)) | ~v1_relat_1(B_193) | ~v1_relat_1(A_194))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.80/1.62  tff(c_1821, plain, (![B_193]: (k2_relat_1(k5_relat_1(B_193, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_193)) | ~v1_relat_1(B_193) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1818])).
% 3.80/1.62  tff(c_1863, plain, (![B_195]: (k2_relat_1(k5_relat_1(B_195, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_195))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_12, c_50, c_1821])).
% 3.80/1.62  tff(c_1875, plain, (![B_195]: (k3_xboole_0(k5_relat_1(B_195, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_195, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_195, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_195, k1_xboole_0)) | ~v1_relat_1(B_195))), inference(superposition, [status(thm), theory('equality')], [c_1863, c_42])).
% 3.80/1.62  tff(c_1884, plain, (![B_196]: (k5_relat_1(B_196, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_196, k1_xboole_0)) | ~v1_relat_1(B_196))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1572, c_1875])).
% 3.80/1.62  tff(c_1888, plain, (![A_44]: (k5_relat_1(A_44, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_38, c_1884])).
% 3.80/1.62  tff(c_1892, plain, (![A_197]: (k5_relat_1(A_197, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_197))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1888])).
% 3.80/1.62  tff(c_1907, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_1892])).
% 3.80/1.62  tff(c_1915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1513, c_1907])).
% 3.80/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.62  
% 3.80/1.62  Inference rules
% 3.80/1.62  ----------------------
% 3.80/1.62  #Ref     : 0
% 3.80/1.62  #Sup     : 446
% 3.80/1.62  #Fact    : 0
% 3.80/1.62  #Define  : 0
% 3.80/1.62  #Split   : 3
% 3.80/1.62  #Chain   : 0
% 3.80/1.62  #Close   : 0
% 3.80/1.62  
% 3.80/1.62  Ordering : KBO
% 3.80/1.62  
% 3.80/1.62  Simplification rules
% 3.80/1.62  ----------------------
% 3.80/1.62  #Subsume      : 16
% 3.80/1.62  #Demod        : 387
% 3.80/1.62  #Tautology    : 258
% 3.80/1.62  #SimpNegUnit  : 2
% 3.80/1.62  #BackRed      : 2
% 3.80/1.62  
% 3.80/1.62  #Partial instantiations: 0
% 3.80/1.62  #Strategies tried      : 1
% 3.80/1.62  
% 3.80/1.62  Timing (in seconds)
% 3.80/1.62  ----------------------
% 3.80/1.62  Preprocessing        : 0.34
% 3.80/1.62  Parsing              : 0.19
% 3.80/1.62  CNF conversion       : 0.02
% 3.80/1.62  Main loop            : 0.51
% 3.80/1.62  Inferencing          : 0.19
% 3.80/1.62  Reduction            : 0.15
% 3.80/1.62  Demodulation         : 0.11
% 3.80/1.62  BG Simplification    : 0.03
% 3.80/1.62  Subsumption          : 0.10
% 3.80/1.62  Abstraction          : 0.03
% 3.80/1.62  MUC search           : 0.00
% 3.80/1.62  Cooper               : 0.00
% 3.80/1.62  Total                : 0.89
% 3.80/1.62  Index Insertion      : 0.00
% 3.80/1.62  Index Deletion       : 0.00
% 3.80/1.62  Index Matching       : 0.00
% 3.80/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
