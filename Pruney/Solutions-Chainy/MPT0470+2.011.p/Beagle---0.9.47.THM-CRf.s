%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:02 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 234 expanded)
%              Number of leaves         :   37 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          :  179 ( 411 expanded)
%              Number of equality atoms :   56 ( 115 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_103,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_52,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_77,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_54,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_66,plain,(
    ! [A_41] :
      ( v1_relat_1(A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_66])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( v1_relat_1(k5_relat_1(A_28,B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,(
    ! [A_48,B_49] :
      ( v1_xboole_0(k2_zfmisc_1(A_48,B_49))
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_173,plain,(
    ! [A_58,B_59] :
      ( k2_zfmisc_1(A_58,B_59) = k1_xboole_0
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_115,c_4])).

tff(c_182,plain,(
    ! [B_59] : k2_zfmisc_1(k1_xboole_0,B_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_173])).

tff(c_50,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_609,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_91,B_92)),k1_relat_1(A_91))
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_617,plain,(
    ! [B_92] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_92)),k1_xboole_0)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_609])).

tff(c_621,plain,(
    ! [B_93] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_93)),k1_xboole_0)
      | ~ v1_relat_1(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_617])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_247,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_256,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_247])).

tff(c_652,plain,(
    ! [B_96] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_96)) = k1_xboole_0
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_621,c_256])).

tff(c_38,plain,(
    ! [A_31] :
      ( k3_xboole_0(A_31,k2_zfmisc_1(k1_relat_1(A_31),k2_relat_1(A_31))) = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_667,plain,(
    ! [B_96] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_96),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_96)))) = k5_relat_1(k1_xboole_0,B_96)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_38])).

tff(c_677,plain,(
    ! [B_97] :
      ( k5_relat_1(k1_xboole_0,B_97) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_97))
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_182,c_667])).

tff(c_681,plain,(
    ! [B_29] :
      ( k5_relat_1(k1_xboole_0,B_29) = k1_xboole_0
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_677])).

tff(c_685,plain,(
    ! [B_98] :
      ( k5_relat_1(k1_xboole_0,B_98) = k1_xboole_0
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_681])).

tff(c_703,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_685])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_703])).

tff(c_713,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_32,plain,(
    ! [A_27] :
      ( v1_relat_1(k4_relat_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_48,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    ! [A_32] :
      ( k1_relat_1(k4_relat_1(A_32)) = k2_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1246,plain,(
    ! [A_143,B_144] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_143,B_144)),k1_relat_1(A_143))
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1655,plain,(
    ! [A_169,B_170] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(A_169),B_170)),k2_relat_1(A_169))
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(k4_relat_1(A_169))
      | ~ v1_relat_1(A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1246])).

tff(c_1669,plain,(
    ! [B_170] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),B_170)),k1_xboole_0)
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1655])).

tff(c_1672,plain,(
    ! [B_170] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),B_170)),k1_xboole_0)
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1669])).

tff(c_1673,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1672])).

tff(c_1676,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_1673])).

tff(c_1680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1676])).

tff(c_1682,plain,(
    v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1672])).

tff(c_756,plain,(
    ! [A_104,B_105] :
      ( v1_xboole_0(k2_zfmisc_1(A_104,B_105))
      | ~ v1_xboole_0(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_811,plain,(
    ! [A_115,B_116] :
      ( k2_zfmisc_1(A_115,B_116) = k1_xboole_0
      | ~ v1_xboole_0(B_116) ) ),
    inference(resolution,[status(thm)],[c_756,c_4])).

tff(c_820,plain,(
    ! [A_115] : k2_zfmisc_1(A_115,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_811])).

tff(c_40,plain,(
    ! [A_32] :
      ( k2_relat_1(k4_relat_1(A_32)) = k1_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1221,plain,(
    ! [A_142] :
      ( k3_xboole_0(A_142,k2_zfmisc_1(k1_relat_1(A_142),k2_relat_1(A_142))) = A_142
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1833,plain,(
    ! [A_175] :
      ( k3_xboole_0(k4_relat_1(A_175),k2_zfmisc_1(k1_relat_1(k4_relat_1(A_175)),k1_relat_1(A_175))) = k4_relat_1(A_175)
      | ~ v1_relat_1(k4_relat_1(A_175))
      | ~ v1_relat_1(A_175) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1221])).

tff(c_1866,plain,
    ( k3_xboole_0(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)) = k4_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1833])).

tff(c_1872,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1682,c_12,c_820,c_1866])).

tff(c_727,plain,(
    ! [A_101,B_102] :
      ( v1_xboole_0(k2_zfmisc_1(A_101,B_102))
      | ~ v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_765,plain,(
    ! [A_106,B_107] :
      ( k2_zfmisc_1(A_106,B_107) = k1_xboole_0
      | ~ v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_727,c_4])).

tff(c_774,plain,(
    ! [B_107] : k2_zfmisc_1(k1_xboole_0,B_107) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_765])).

tff(c_1257,plain,(
    ! [B_144] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_144)),k1_xboole_0)
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1246])).

tff(c_1263,plain,(
    ! [B_145] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_145)),k1_xboole_0)
      | ~ v1_relat_1(B_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1257])).

tff(c_893,plain,(
    ! [B_124,A_125] :
      ( B_124 = A_125
      | ~ r1_tarski(B_124,A_125)
      | ~ r1_tarski(A_125,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_902,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_893])).

tff(c_1278,plain,(
    ! [B_146] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_146)) = k1_xboole_0
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_1263,c_902])).

tff(c_1293,plain,(
    ! [B_146] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_146),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_146)))) = k5_relat_1(k1_xboole_0,B_146)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_146))
      | ~ v1_relat_1(B_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_38])).

tff(c_1317,plain,(
    ! [B_151] :
      ( k5_relat_1(k1_xboole_0,B_151) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_151))
      | ~ v1_relat_1(B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_774,c_1293])).

tff(c_1321,plain,(
    ! [B_29] :
      ( k5_relat_1(k1_xboole_0,B_29) = k1_xboole_0
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_1317])).

tff(c_1330,plain,(
    ! [B_152] :
      ( k5_relat_1(k1_xboole_0,B_152) = k1_xboole_0
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1321])).

tff(c_1352,plain,(
    ! [A_27] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_27)) = k1_xboole_0
      | ~ v1_relat_1(A_27) ) ),
    inference(resolution,[status(thm)],[c_32,c_1330])).

tff(c_36,plain,(
    ! [A_30] :
      ( k4_relat_1(k4_relat_1(A_30)) = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1380,plain,(
    ! [B_153,A_154] :
      ( k5_relat_1(k4_relat_1(B_153),k4_relat_1(A_154)) = k4_relat_1(k5_relat_1(A_154,B_153))
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2268,plain,(
    ! [A_182,A_183] :
      ( k4_relat_1(k5_relat_1(A_182,k4_relat_1(A_183))) = k5_relat_1(A_183,k4_relat_1(A_182))
      | ~ v1_relat_1(k4_relat_1(A_183))
      | ~ v1_relat_1(A_182)
      | ~ v1_relat_1(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1380])).

tff(c_2362,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_27))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1352,c_2268])).

tff(c_2383,plain,(
    ! [A_184] :
      ( k5_relat_1(A_184,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_184))
      | ~ v1_relat_1(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1872,c_1872,c_2362])).

tff(c_2422,plain,(
    ! [A_185] :
      ( k5_relat_1(A_185,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_185) ) ),
    inference(resolution,[status(thm)],[c_32,c_2383])).

tff(c_2449,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_2422])).

tff(c_2462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_2449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.60  
% 3.44/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.60  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.44/1.60  
% 3.44/1.60  %Foreground sorts:
% 3.44/1.60  
% 3.44/1.60  
% 3.44/1.60  %Background operators:
% 3.44/1.60  
% 3.44/1.60  
% 3.44/1.60  %Foreground operators:
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.60  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.44/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.44/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.44/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.44/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.44/1.60  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.44/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.44/1.60  
% 3.44/1.62  tff(f_110, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.44/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.44/1.62  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.44/1.62  tff(f_72, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.44/1.62  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.44/1.62  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.44/1.62  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.44/1.62  tff(f_103, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.44/1.62  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 3.44/1.62  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.44/1.62  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.62  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.44/1.62  tff(f_66, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.44/1.62  tff(f_86, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.44/1.62  tff(f_52, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.44/1.62  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.44/1.62  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.44/1.62  tff(c_52, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.44/1.62  tff(c_77, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 3.44/1.62  tff(c_54, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.44/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.44/1.62  tff(c_66, plain, (![A_41]: (v1_relat_1(A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.44/1.62  tff(c_70, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_66])).
% 3.44/1.62  tff(c_34, plain, (![A_28, B_29]: (v1_relat_1(k5_relat_1(A_28, B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.44/1.62  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.44/1.62  tff(c_115, plain, (![A_48, B_49]: (v1_xboole_0(k2_zfmisc_1(A_48, B_49)) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.44/1.62  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.44/1.62  tff(c_173, plain, (![A_58, B_59]: (k2_zfmisc_1(A_58, B_59)=k1_xboole_0 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_115, c_4])).
% 3.44/1.62  tff(c_182, plain, (![B_59]: (k2_zfmisc_1(k1_xboole_0, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_173])).
% 3.44/1.62  tff(c_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.44/1.62  tff(c_609, plain, (![A_91, B_92]: (r1_tarski(k1_relat_1(k5_relat_1(A_91, B_92)), k1_relat_1(A_91)) | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.44/1.62  tff(c_617, plain, (![B_92]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_92)), k1_xboole_0) | ~v1_relat_1(B_92) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_609])).
% 3.44/1.62  tff(c_621, plain, (![B_93]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_93)), k1_xboole_0) | ~v1_relat_1(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_617])).
% 3.44/1.62  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.44/1.62  tff(c_247, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.44/1.62  tff(c_256, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_247])).
% 3.44/1.62  tff(c_652, plain, (![B_96]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_96))=k1_xboole_0 | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_621, c_256])).
% 3.44/1.62  tff(c_38, plain, (![A_31]: (k3_xboole_0(A_31, k2_zfmisc_1(k1_relat_1(A_31), k2_relat_1(A_31)))=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.44/1.62  tff(c_667, plain, (![B_96]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_96), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_96))))=k5_relat_1(k1_xboole_0, B_96) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_96)) | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_652, c_38])).
% 3.44/1.62  tff(c_677, plain, (![B_97]: (k5_relat_1(k1_xboole_0, B_97)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_97)) | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_182, c_667])).
% 3.44/1.62  tff(c_681, plain, (![B_29]: (k5_relat_1(k1_xboole_0, B_29)=k1_xboole_0 | ~v1_relat_1(B_29) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_677])).
% 3.44/1.62  tff(c_685, plain, (![B_98]: (k5_relat_1(k1_xboole_0, B_98)=k1_xboole_0 | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_681])).
% 3.44/1.62  tff(c_703, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_685])).
% 3.44/1.62  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_703])).
% 3.44/1.62  tff(c_713, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 3.44/1.62  tff(c_32, plain, (![A_27]: (v1_relat_1(k4_relat_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.44/1.62  tff(c_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.44/1.62  tff(c_42, plain, (![A_32]: (k1_relat_1(k4_relat_1(A_32))=k2_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.44/1.62  tff(c_1246, plain, (![A_143, B_144]: (r1_tarski(k1_relat_1(k5_relat_1(A_143, B_144)), k1_relat_1(A_143)) | ~v1_relat_1(B_144) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.44/1.62  tff(c_1655, plain, (![A_169, B_170]: (r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(A_169), B_170)), k2_relat_1(A_169)) | ~v1_relat_1(B_170) | ~v1_relat_1(k4_relat_1(A_169)) | ~v1_relat_1(A_169))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1246])).
% 3.44/1.62  tff(c_1669, plain, (![B_170]: (r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0), B_170)), k1_xboole_0) | ~v1_relat_1(B_170) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1655])).
% 3.44/1.62  tff(c_1672, plain, (![B_170]: (r1_tarski(k1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0), B_170)), k1_xboole_0) | ~v1_relat_1(B_170) | ~v1_relat_1(k4_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1669])).
% 3.44/1.62  tff(c_1673, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1672])).
% 3.44/1.62  tff(c_1676, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_1673])).
% 3.44/1.62  tff(c_1680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1676])).
% 3.44/1.62  tff(c_1682, plain, (v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1672])).
% 3.44/1.62  tff(c_756, plain, (![A_104, B_105]: (v1_xboole_0(k2_zfmisc_1(A_104, B_105)) | ~v1_xboole_0(B_105))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.44/1.62  tff(c_811, plain, (![A_115, B_116]: (k2_zfmisc_1(A_115, B_116)=k1_xboole_0 | ~v1_xboole_0(B_116))), inference(resolution, [status(thm)], [c_756, c_4])).
% 3.44/1.62  tff(c_820, plain, (![A_115]: (k2_zfmisc_1(A_115, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_811])).
% 3.44/1.62  tff(c_40, plain, (![A_32]: (k2_relat_1(k4_relat_1(A_32))=k1_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.44/1.62  tff(c_1221, plain, (![A_142]: (k3_xboole_0(A_142, k2_zfmisc_1(k1_relat_1(A_142), k2_relat_1(A_142)))=A_142 | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.44/1.62  tff(c_1833, plain, (![A_175]: (k3_xboole_0(k4_relat_1(A_175), k2_zfmisc_1(k1_relat_1(k4_relat_1(A_175)), k1_relat_1(A_175)))=k4_relat_1(A_175) | ~v1_relat_1(k4_relat_1(A_175)) | ~v1_relat_1(A_175))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1221])).
% 3.44/1.62  tff(c_1866, plain, (k3_xboole_0(k4_relat_1(k1_xboole_0), k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)), k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_1833])).
% 3.44/1.62  tff(c_1872, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1682, c_12, c_820, c_1866])).
% 3.44/1.62  tff(c_727, plain, (![A_101, B_102]: (v1_xboole_0(k2_zfmisc_1(A_101, B_102)) | ~v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.44/1.62  tff(c_765, plain, (![A_106, B_107]: (k2_zfmisc_1(A_106, B_107)=k1_xboole_0 | ~v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_727, c_4])).
% 3.44/1.62  tff(c_774, plain, (![B_107]: (k2_zfmisc_1(k1_xboole_0, B_107)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_765])).
% 3.44/1.62  tff(c_1257, plain, (![B_144]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_144)), k1_xboole_0) | ~v1_relat_1(B_144) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1246])).
% 3.44/1.62  tff(c_1263, plain, (![B_145]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_145)), k1_xboole_0) | ~v1_relat_1(B_145))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1257])).
% 3.44/1.62  tff(c_893, plain, (![B_124, A_125]: (B_124=A_125 | ~r1_tarski(B_124, A_125) | ~r1_tarski(A_125, B_124))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.44/1.62  tff(c_902, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_893])).
% 3.44/1.62  tff(c_1278, plain, (![B_146]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_146))=k1_xboole_0 | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_1263, c_902])).
% 3.44/1.62  tff(c_1293, plain, (![B_146]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_146), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_146))))=k5_relat_1(k1_xboole_0, B_146) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_146)) | ~v1_relat_1(B_146))), inference(superposition, [status(thm), theory('equality')], [c_1278, c_38])).
% 3.44/1.62  tff(c_1317, plain, (![B_151]: (k5_relat_1(k1_xboole_0, B_151)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_151)) | ~v1_relat_1(B_151))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_774, c_1293])).
% 3.44/1.62  tff(c_1321, plain, (![B_29]: (k5_relat_1(k1_xboole_0, B_29)=k1_xboole_0 | ~v1_relat_1(B_29) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_1317])).
% 3.44/1.62  tff(c_1330, plain, (![B_152]: (k5_relat_1(k1_xboole_0, B_152)=k1_xboole_0 | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1321])).
% 3.44/1.62  tff(c_1352, plain, (![A_27]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_27))=k1_xboole_0 | ~v1_relat_1(A_27))), inference(resolution, [status(thm)], [c_32, c_1330])).
% 3.44/1.62  tff(c_36, plain, (![A_30]: (k4_relat_1(k4_relat_1(A_30))=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.44/1.62  tff(c_1380, plain, (![B_153, A_154]: (k5_relat_1(k4_relat_1(B_153), k4_relat_1(A_154))=k4_relat_1(k5_relat_1(A_154, B_153)) | ~v1_relat_1(B_153) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.44/1.62  tff(c_2268, plain, (![A_182, A_183]: (k4_relat_1(k5_relat_1(A_182, k4_relat_1(A_183)))=k5_relat_1(A_183, k4_relat_1(A_182)) | ~v1_relat_1(k4_relat_1(A_183)) | ~v1_relat_1(A_182) | ~v1_relat_1(A_183))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1380])).
% 3.44/1.62  tff(c_2362, plain, (![A_27]: (k5_relat_1(A_27, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_27)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_1352, c_2268])).
% 3.44/1.62  tff(c_2383, plain, (![A_184]: (k5_relat_1(A_184, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_184)) | ~v1_relat_1(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1872, c_1872, c_2362])).
% 3.44/1.62  tff(c_2422, plain, (![A_185]: (k5_relat_1(A_185, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_185))), inference(resolution, [status(thm)], [c_32, c_2383])).
% 3.44/1.62  tff(c_2449, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_2422])).
% 3.44/1.62  tff(c_2462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_713, c_2449])).
% 3.44/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.62  
% 3.44/1.62  Inference rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Ref     : 0
% 3.44/1.62  #Sup     : 579
% 3.44/1.62  #Fact    : 0
% 3.44/1.62  #Define  : 0
% 3.44/1.62  #Split   : 2
% 3.44/1.62  #Chain   : 0
% 3.44/1.62  #Close   : 0
% 3.44/1.62  
% 3.44/1.62  Ordering : KBO
% 3.44/1.62  
% 3.44/1.62  Simplification rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Subsume      : 26
% 3.44/1.62  #Demod        : 450
% 3.44/1.62  #Tautology    : 369
% 3.44/1.62  #SimpNegUnit  : 2
% 3.44/1.62  #BackRed      : 4
% 3.44/1.62  
% 3.44/1.62  #Partial instantiations: 0
% 3.44/1.62  #Strategies tried      : 1
% 3.44/1.62  
% 3.44/1.62  Timing (in seconds)
% 3.44/1.62  ----------------------
% 3.44/1.62  Preprocessing        : 0.32
% 3.44/1.62  Parsing              : 0.18
% 3.44/1.62  CNF conversion       : 0.02
% 3.44/1.62  Main loop            : 0.52
% 3.44/1.62  Inferencing          : 0.19
% 3.44/1.62  Reduction            : 0.16
% 3.44/1.62  Demodulation         : 0.12
% 3.44/1.62  BG Simplification    : 0.03
% 3.44/1.62  Subsumption          : 0.10
% 3.44/1.62  Abstraction          : 0.03
% 3.44/1.62  MUC search           : 0.00
% 3.44/1.62  Cooper               : 0.00
% 3.44/1.62  Total                : 0.88
% 3.44/1.62  Index Insertion      : 0.00
% 3.44/1.62  Index Deletion       : 0.00
% 3.44/1.62  Index Matching       : 0.00
% 3.44/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
