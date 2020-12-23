%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:10 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 223 expanded)
%              Number of leaves         :   42 (  92 expanded)
%              Depth                    :   14
%              Number of atoms          :  163 ( 338 expanded)
%              Number of equality atoms :   64 ( 148 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_36,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_104,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_50,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_84,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_52,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_70,plain,(
    ! [A_46] :
      ( v1_relat_1(A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_70])).

tff(c_34,plain,(
    ! [A_31,B_32] :
      ( v1_relat_1(k5_relat_1(A_31,B_32))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_109,plain,(
    ! [A_51,B_52] :
      ( v1_xboole_0(k2_zfmisc_1(A_51,B_52))
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_147,plain,(
    ! [A_56,B_57] :
      ( k2_zfmisc_1(A_56,B_57) = k1_xboole_0
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_109,c_6])).

tff(c_153,plain,(
    ! [B_57] : k2_zfmisc_1(k1_xboole_0,B_57) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_147])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_552,plain,(
    ! [A_98,B_99] :
      ( k1_relat_1(k5_relat_1(A_98,B_99)) = k1_relat_1(A_98)
      | ~ r1_tarski(k2_relat_1(A_98),k1_relat_1(B_99))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_558,plain,(
    ! [B_99] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_99)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_99))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_552])).

tff(c_563,plain,(
    ! [B_100] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_100)) = k1_xboole_0
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12,c_48,c_558])).

tff(c_38,plain,(
    ! [A_34] :
      ( k3_xboole_0(A_34,k2_zfmisc_1(k1_relat_1(A_34),k2_relat_1(A_34))) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_575,plain,(
    ! [B_100] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_100),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_100)))) = k5_relat_1(k1_xboole_0,B_100)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_100))
      | ~ v1_relat_1(B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_38])).

tff(c_586,plain,(
    ! [B_101] :
      ( k5_relat_1(k1_xboole_0,B_101) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_101))
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_153,c_575])).

tff(c_596,plain,(
    ! [B_32] :
      ( k5_relat_1(k1_xboole_0,B_32) = k1_xboole_0
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_586])).

tff(c_687,plain,(
    ! [B_103] :
      ( k5_relat_1(k1_xboole_0,B_103) = k1_xboole_0
      | ~ v1_relat_1(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_596])).

tff(c_705,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_687])).

tff(c_715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_705])).

tff(c_716,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_32,plain,(
    ! [A_30] :
      ( v1_relat_1(k4_relat_1(A_30))
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_833,plain,(
    ! [A_123,B_124] : k5_xboole_0(A_123,k3_xboole_0(A_123,B_124)) = k4_xboole_0(A_123,B_124) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_845,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_833])).

tff(c_848,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_845])).

tff(c_26,plain,(
    ! [A_25,B_26] : k6_subset_1(A_25,B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ! [A_35,B_37] :
      ( k6_subset_1(k4_relat_1(A_35),k4_relat_1(B_37)) = k4_relat_1(k6_subset_1(A_35,B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_965,plain,(
    ! [A_139,B_140] :
      ( k4_xboole_0(k4_relat_1(A_139),k4_relat_1(B_140)) = k4_relat_1(k4_xboole_0(A_139,B_140))
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_40])).

tff(c_972,plain,(
    ! [B_140] :
      ( k4_relat_1(k4_xboole_0(B_140,B_140)) = k1_xboole_0
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_965,c_848])).

tff(c_987,plain,(
    ! [B_140] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_972])).

tff(c_1000,plain,(
    ! [B_146] :
      ( ~ v1_relat_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(splitLeft,[status(thm)],[c_987])).

tff(c_1008,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_74,c_1000])).

tff(c_1017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1008])).

tff(c_1018,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_987])).

tff(c_775,plain,(
    ! [A_110,B_111] :
      ( v1_xboole_0(k2_zfmisc_1(A_110,B_111))
      | ~ v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_793,plain,(
    ! [A_114,B_115] :
      ( k2_zfmisc_1(A_114,B_115) = k1_xboole_0
      | ~ v1_xboole_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_775,c_6])).

tff(c_799,plain,(
    ! [B_115] : k2_zfmisc_1(k1_xboole_0,B_115) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_793])).

tff(c_1169,plain,(
    ! [A_157,B_158] :
      ( k1_relat_1(k5_relat_1(A_157,B_158)) = k1_relat_1(A_157)
      | ~ r1_tarski(k2_relat_1(A_157),k1_relat_1(B_158))
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1175,plain,(
    ! [B_158] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_158)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_158))
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1169])).

tff(c_1180,plain,(
    ! [B_159] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_159)) = k1_xboole_0
      | ~ v1_relat_1(B_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12,c_48,c_1175])).

tff(c_1192,plain,(
    ! [B_159] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_159),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_159)))) = k5_relat_1(k1_xboole_0,B_159)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_159))
      | ~ v1_relat_1(B_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1180,c_38])).

tff(c_1208,plain,(
    ! [B_160] :
      ( k5_relat_1(k1_xboole_0,B_160) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_160))
      | ~ v1_relat_1(B_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_799,c_1192])).

tff(c_1215,plain,(
    ! [B_32] :
      ( k5_relat_1(k1_xboole_0,B_32) = k1_xboole_0
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_1208])).

tff(c_1224,plain,(
    ! [B_161] :
      ( k5_relat_1(k1_xboole_0,B_161) = k1_xboole_0
      | ~ v1_relat_1(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1215])).

tff(c_1242,plain,(
    ! [A_30] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_30)) = k1_xboole_0
      | ~ v1_relat_1(A_30) ) ),
    inference(resolution,[status(thm)],[c_32,c_1224])).

tff(c_36,plain,(
    ! [A_33] :
      ( k4_relat_1(k4_relat_1(A_33)) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1087,plain,(
    ! [B_154,A_155] :
      ( k5_relat_1(k4_relat_1(B_154),k4_relat_1(A_155)) = k4_relat_1(k5_relat_1(A_155,B_154))
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1102,plain,(
    ! [B_154] :
      ( k5_relat_1(k4_relat_1(B_154),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_154))
      | ~ v1_relat_1(B_154)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_1087])).

tff(c_1381,plain,(
    ! [B_167] :
      ( k5_relat_1(k4_relat_1(B_167),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_167))
      | ~ v1_relat_1(B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1102])).

tff(c_1937,plain,(
    ! [A_181] :
      ( k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(A_181))) = k5_relat_1(A_181,k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_181))
      | ~ v1_relat_1(A_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1381])).

tff(c_2009,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k1_xboole_0) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_30))
      | ~ v1_relat_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1242,c_1937])).

tff(c_2029,plain,(
    ! [A_182] :
      ( k5_relat_1(A_182,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_182))
      | ~ v1_relat_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_2009])).

tff(c_2065,plain,(
    ! [A_183] :
      ( k5_relat_1(A_183,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_183) ) ),
    inference(resolution,[status(thm)],[c_32,c_2029])).

tff(c_2089,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_2065])).

tff(c_2101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_716,c_2089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:55:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.56  
% 3.55/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.56  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.55/1.56  
% 3.55/1.56  %Foreground sorts:
% 3.55/1.56  
% 3.55/1.56  
% 3.55/1.56  %Background operators:
% 3.55/1.56  
% 3.55/1.56  
% 3.55/1.56  %Foreground operators:
% 3.55/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.55/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.55/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.55/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.55/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.56  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.55/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.55/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.55/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.55/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.56  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.55/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.55/1.56  
% 3.55/1.58  tff(f_111, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.55/1.58  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.55/1.58  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.55/1.58  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.55/1.58  tff(f_36, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.55/1.58  tff(f_52, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.55/1.58  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.55/1.58  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.55/1.58  tff(f_104, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.55/1.58  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.55/1.58  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.55/1.58  tff(f_64, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.55/1.58  tff(f_40, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.55/1.58  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.55/1.58  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.55/1.58  tff(f_54, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.55/1.58  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 3.55/1.58  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.55/1.58  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.55/1.58  tff(c_50, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.55/1.58  tff(c_84, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_50])).
% 3.55/1.58  tff(c_52, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.55/1.58  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.55/1.58  tff(c_70, plain, (![A_46]: (v1_relat_1(A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.55/1.58  tff(c_74, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_70])).
% 3.55/1.58  tff(c_34, plain, (![A_31, B_32]: (v1_relat_1(k5_relat_1(A_31, B_32)) | ~v1_relat_1(B_32) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.55/1.58  tff(c_10, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.55/1.58  tff(c_109, plain, (![A_51, B_52]: (v1_xboole_0(k2_zfmisc_1(A_51, B_52)) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.55/1.58  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.58  tff(c_147, plain, (![A_56, B_57]: (k2_zfmisc_1(A_56, B_57)=k1_xboole_0 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_109, c_6])).
% 3.55/1.58  tff(c_153, plain, (![B_57]: (k2_zfmisc_1(k1_xboole_0, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_147])).
% 3.55/1.58  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.55/1.58  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.55/1.58  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.55/1.58  tff(c_552, plain, (![A_98, B_99]: (k1_relat_1(k5_relat_1(A_98, B_99))=k1_relat_1(A_98) | ~r1_tarski(k2_relat_1(A_98), k1_relat_1(B_99)) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.55/1.58  tff(c_558, plain, (![B_99]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_99))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_99)) | ~v1_relat_1(B_99) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_552])).
% 3.55/1.58  tff(c_563, plain, (![B_100]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_100))=k1_xboole_0 | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_12, c_48, c_558])).
% 3.55/1.58  tff(c_38, plain, (![A_34]: (k3_xboole_0(A_34, k2_zfmisc_1(k1_relat_1(A_34), k2_relat_1(A_34)))=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.55/1.58  tff(c_575, plain, (![B_100]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_100), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_100))))=k5_relat_1(k1_xboole_0, B_100) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_100)) | ~v1_relat_1(B_100))), inference(superposition, [status(thm), theory('equality')], [c_563, c_38])).
% 3.55/1.58  tff(c_586, plain, (![B_101]: (k5_relat_1(k1_xboole_0, B_101)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_101)) | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_153, c_575])).
% 3.55/1.58  tff(c_596, plain, (![B_32]: (k5_relat_1(k1_xboole_0, B_32)=k1_xboole_0 | ~v1_relat_1(B_32) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_586])).
% 3.55/1.58  tff(c_687, plain, (![B_103]: (k5_relat_1(k1_xboole_0, B_103)=k1_xboole_0 | ~v1_relat_1(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_596])).
% 3.55/1.58  tff(c_705, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_687])).
% 3.55/1.58  tff(c_715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_705])).
% 3.55/1.58  tff(c_716, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_50])).
% 3.55/1.58  tff(c_32, plain, (![A_30]: (v1_relat_1(k4_relat_1(A_30)) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.55/1.58  tff(c_14, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.58  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.55/1.58  tff(c_833, plain, (![A_123, B_124]: (k5_xboole_0(A_123, k3_xboole_0(A_123, B_124))=k4_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.55/1.58  tff(c_845, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_833])).
% 3.55/1.58  tff(c_848, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_845])).
% 3.55/1.58  tff(c_26, plain, (![A_25, B_26]: (k6_subset_1(A_25, B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.55/1.58  tff(c_40, plain, (![A_35, B_37]: (k6_subset_1(k4_relat_1(A_35), k4_relat_1(B_37))=k4_relat_1(k6_subset_1(A_35, B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.55/1.58  tff(c_965, plain, (![A_139, B_140]: (k4_xboole_0(k4_relat_1(A_139), k4_relat_1(B_140))=k4_relat_1(k4_xboole_0(A_139, B_140)) | ~v1_relat_1(B_140) | ~v1_relat_1(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_40])).
% 3.55/1.58  tff(c_972, plain, (![B_140]: (k4_relat_1(k4_xboole_0(B_140, B_140))=k1_xboole_0 | ~v1_relat_1(B_140) | ~v1_relat_1(B_140))), inference(superposition, [status(thm), theory('equality')], [c_965, c_848])).
% 3.55/1.58  tff(c_987, plain, (![B_140]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_140) | ~v1_relat_1(B_140))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_972])).
% 3.55/1.58  tff(c_1000, plain, (![B_146]: (~v1_relat_1(B_146) | ~v1_relat_1(B_146))), inference(splitLeft, [status(thm)], [c_987])).
% 3.55/1.58  tff(c_1008, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_1000])).
% 3.55/1.58  tff(c_1017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1008])).
% 3.55/1.58  tff(c_1018, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_987])).
% 3.55/1.58  tff(c_775, plain, (![A_110, B_111]: (v1_xboole_0(k2_zfmisc_1(A_110, B_111)) | ~v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.55/1.58  tff(c_793, plain, (![A_114, B_115]: (k2_zfmisc_1(A_114, B_115)=k1_xboole_0 | ~v1_xboole_0(A_114))), inference(resolution, [status(thm)], [c_775, c_6])).
% 3.55/1.58  tff(c_799, plain, (![B_115]: (k2_zfmisc_1(k1_xboole_0, B_115)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_793])).
% 3.55/1.58  tff(c_1169, plain, (![A_157, B_158]: (k1_relat_1(k5_relat_1(A_157, B_158))=k1_relat_1(A_157) | ~r1_tarski(k2_relat_1(A_157), k1_relat_1(B_158)) | ~v1_relat_1(B_158) | ~v1_relat_1(A_157))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.55/1.58  tff(c_1175, plain, (![B_158]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_158))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_158)) | ~v1_relat_1(B_158) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1169])).
% 3.55/1.58  tff(c_1180, plain, (![B_159]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_159))=k1_xboole_0 | ~v1_relat_1(B_159))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_12, c_48, c_1175])).
% 3.55/1.58  tff(c_1192, plain, (![B_159]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_159), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_159))))=k5_relat_1(k1_xboole_0, B_159) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_159)) | ~v1_relat_1(B_159))), inference(superposition, [status(thm), theory('equality')], [c_1180, c_38])).
% 3.55/1.58  tff(c_1208, plain, (![B_160]: (k5_relat_1(k1_xboole_0, B_160)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_160)) | ~v1_relat_1(B_160))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_799, c_1192])).
% 3.55/1.58  tff(c_1215, plain, (![B_32]: (k5_relat_1(k1_xboole_0, B_32)=k1_xboole_0 | ~v1_relat_1(B_32) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_1208])).
% 3.55/1.58  tff(c_1224, plain, (![B_161]: (k5_relat_1(k1_xboole_0, B_161)=k1_xboole_0 | ~v1_relat_1(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1215])).
% 3.55/1.58  tff(c_1242, plain, (![A_30]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_30))=k1_xboole_0 | ~v1_relat_1(A_30))), inference(resolution, [status(thm)], [c_32, c_1224])).
% 3.55/1.58  tff(c_36, plain, (![A_33]: (k4_relat_1(k4_relat_1(A_33))=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.55/1.58  tff(c_1087, plain, (![B_154, A_155]: (k5_relat_1(k4_relat_1(B_154), k4_relat_1(A_155))=k4_relat_1(k5_relat_1(A_155, B_154)) | ~v1_relat_1(B_154) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.55/1.58  tff(c_1102, plain, (![B_154]: (k5_relat_1(k4_relat_1(B_154), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_154)) | ~v1_relat_1(B_154) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1018, c_1087])).
% 3.55/1.58  tff(c_1381, plain, (![B_167]: (k5_relat_1(k4_relat_1(B_167), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_167)) | ~v1_relat_1(B_167))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1102])).
% 3.55/1.58  tff(c_1937, plain, (![A_181]: (k4_relat_1(k5_relat_1(k1_xboole_0, k4_relat_1(A_181)))=k5_relat_1(A_181, k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_181)) | ~v1_relat_1(A_181))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1381])).
% 3.55/1.58  tff(c_2009, plain, (![A_30]: (k5_relat_1(A_30, k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_30)) | ~v1_relat_1(A_30) | ~v1_relat_1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_1242, c_1937])).
% 3.55/1.58  tff(c_2029, plain, (![A_182]: (k5_relat_1(A_182, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_182)) | ~v1_relat_1(A_182) | ~v1_relat_1(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_2009])).
% 3.55/1.58  tff(c_2065, plain, (![A_183]: (k5_relat_1(A_183, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_183))), inference(resolution, [status(thm)], [c_32, c_2029])).
% 3.55/1.58  tff(c_2089, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_2065])).
% 3.55/1.58  tff(c_2101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_716, c_2089])).
% 3.55/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.58  
% 3.55/1.58  Inference rules
% 3.55/1.58  ----------------------
% 3.55/1.58  #Ref     : 0
% 3.55/1.58  #Sup     : 495
% 3.55/1.58  #Fact    : 0
% 3.55/1.58  #Define  : 0
% 3.55/1.58  #Split   : 3
% 3.55/1.58  #Chain   : 0
% 3.55/1.58  #Close   : 0
% 3.55/1.58  
% 3.55/1.58  Ordering : KBO
% 3.55/1.58  
% 3.55/1.58  Simplification rules
% 3.55/1.58  ----------------------
% 3.55/1.58  #Subsume      : 14
% 3.55/1.58  #Demod        : 421
% 3.55/1.58  #Tautology    : 282
% 3.55/1.58  #SimpNegUnit  : 2
% 3.55/1.58  #BackRed      : 3
% 3.55/1.58  
% 3.55/1.58  #Partial instantiations: 0
% 3.55/1.58  #Strategies tried      : 1
% 3.55/1.58  
% 3.55/1.58  Timing (in seconds)
% 3.55/1.58  ----------------------
% 3.55/1.58  Preprocessing        : 0.32
% 3.55/1.58  Parsing              : 0.18
% 3.55/1.58  CNF conversion       : 0.02
% 3.55/1.58  Main loop            : 0.50
% 3.55/1.58  Inferencing          : 0.19
% 3.55/1.58  Reduction            : 0.15
% 3.55/1.58  Demodulation         : 0.11
% 3.55/1.58  BG Simplification    : 0.03
% 3.55/1.58  Subsumption          : 0.10
% 3.55/1.58  Abstraction          : 0.03
% 3.55/1.58  MUC search           : 0.00
% 3.55/1.58  Cooper               : 0.00
% 3.55/1.58  Total                : 0.86
% 3.55/1.58  Index Insertion      : 0.00
% 3.55/1.58  Index Deletion       : 0.00
% 3.55/1.58  Index Matching       : 0.00
% 3.55/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
