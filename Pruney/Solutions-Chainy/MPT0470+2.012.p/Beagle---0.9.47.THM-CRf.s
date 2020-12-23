%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:02 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 447 expanded)
%              Number of leaves         :   38 ( 166 expanded)
%              Depth                    :   15
%              Number of atoms          :  172 ( 838 expanded)
%              Number of equality atoms :   54 ( 200 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_110,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_103,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_54,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_79,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_34,plain,(
    ! [A_38] :
      ( v1_relat_1(k4_relat_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_74,plain,(
    ! [A_53] :
      ( v1_relat_1(A_53)
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_78,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_74])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    ! [A_43] :
      ( k2_relat_1(k4_relat_1(A_43)) = k1_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_281,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_86,B_87)),k2_relat_1(B_87))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_570,plain,(
    ! [A_110,A_111] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_110,k4_relat_1(A_111))),k1_relat_1(A_111))
      | ~ v1_relat_1(k4_relat_1(A_111))
      | ~ v1_relat_1(A_110)
      | ~ v1_relat_1(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_281])).

tff(c_584,plain,(
    ! [A_110] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_110,k4_relat_1(k1_xboole_0))),k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_110)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_570])).

tff(c_587,plain,(
    ! [A_110] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_110,k4_relat_1(k1_xboole_0))),k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_relat_1(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_584])).

tff(c_597,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_587])).

tff(c_600,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_597])).

tff(c_604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_600])).

tff(c_606,plain,(
    v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_587])).

tff(c_36,plain,(
    ! [A_39,B_40] :
      ( v1_relat_1(k5_relat_1(A_39,B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    ! [A_56,B_57] :
      ( v1_xboole_0(k2_zfmisc_1(A_56,B_57))
      | ~ v1_xboole_0(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_130,plain,(
    ! [A_62,B_63] :
      ( k2_zfmisc_1(A_62,B_63) = k1_xboole_0
      | ~ v1_xboole_0(B_63) ) ),
    inference(resolution,[status(thm)],[c_88,c_4])).

tff(c_136,plain,(
    ! [A_62] : k2_zfmisc_1(A_62,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_130])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_289,plain,(
    ! [A_86] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_86,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_281])).

tff(c_293,plain,(
    ! [A_88] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_88,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_289])).

tff(c_14,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_185,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_194,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_185])).

tff(c_303,plain,(
    ! [A_89] :
      ( k2_relat_1(k5_relat_1(A_89,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_293,c_194])).

tff(c_40,plain,(
    ! [A_42] :
      ( k3_xboole_0(A_42,k2_zfmisc_1(k1_relat_1(A_42),k2_relat_1(A_42))) = A_42
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_318,plain,(
    ! [A_89] :
      ( k3_xboole_0(k5_relat_1(A_89,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_89,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_89,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_89,k1_xboole_0))
      | ~ v1_relat_1(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_40])).

tff(c_328,plain,(
    ! [A_90] :
      ( k5_relat_1(A_90,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_90,k1_xboole_0))
      | ~ v1_relat_1(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_136,c_318])).

tff(c_332,plain,(
    ! [A_39] :
      ( k5_relat_1(A_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_36,c_328])).

tff(c_335,plain,(
    ! [A_39] :
      ( k5_relat_1(A_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_332])).

tff(c_610,plain,(
    k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_606,c_335])).

tff(c_38,plain,(
    ! [A_41] :
      ( k4_relat_1(k4_relat_1(A_41)) = A_41
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_414,plain,(
    ! [B_97,A_98] :
      ( k5_relat_1(k4_relat_1(B_97),k4_relat_1(A_98)) = k4_relat_1(k5_relat_1(A_98,B_97))
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_769,plain,(
    ! [A_124,B_125] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_124),B_125)) = k5_relat_1(k4_relat_1(B_125),A_124)
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(k4_relat_1(A_124))
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_414])).

tff(c_811,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_769])).

tff(c_824,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_606,c_78,c_610,c_811])).

tff(c_345,plain,(
    ! [A_96] :
      ( k5_relat_1(A_96,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_332])).

tff(c_363,plain,(
    ! [A_38] :
      ( k5_relat_1(k4_relat_1(A_38),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_34,c_345])).

tff(c_814,plain,(
    ! [A_38] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_38) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_38))
      | ~ v1_relat_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_769])).

tff(c_826,plain,(
    ! [A_38] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_38) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_814])).

tff(c_1319,plain,(
    ! [A_134] :
      ( k5_relat_1(k1_xboole_0,A_134) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_134))
      | ~ v1_relat_1(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_824,c_826])).

tff(c_1358,plain,(
    ! [A_135] :
      ( k5_relat_1(k1_xboole_0,A_135) = k1_xboole_0
      | ~ v1_relat_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_34,c_1319])).

tff(c_1382,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_1358])).

tff(c_1394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_1382])).

tff(c_1395,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1409,plain,(
    ! [A_138,B_139] :
      ( v1_xboole_0(k2_zfmisc_1(A_138,B_139))
      | ~ v1_xboole_0(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1451,plain,(
    ! [A_144,B_145] :
      ( k2_zfmisc_1(A_144,B_145) = k1_xboole_0
      | ~ v1_xboole_0(B_145) ) ),
    inference(resolution,[status(thm)],[c_1409,c_4])).

tff(c_1457,plain,(
    ! [A_144] : k2_zfmisc_1(A_144,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1451])).

tff(c_1598,plain,(
    ! [A_164,B_165] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_164,B_165)),k2_relat_1(B_165))
      | ~ v1_relat_1(B_165)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1609,plain,(
    ! [A_164] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_164,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1598])).

tff(c_1615,plain,(
    ! [A_166] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_166,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1609])).

tff(c_1505,plain,(
    ! [B_152,A_153] :
      ( B_152 = A_153
      | ~ r1_tarski(B_152,A_153)
      | ~ r1_tarski(A_153,B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1514,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_1505])).

tff(c_1625,plain,(
    ! [A_167] :
      ( k2_relat_1(k5_relat_1(A_167,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_167) ) ),
    inference(resolution,[status(thm)],[c_1615,c_1514])).

tff(c_1640,plain,(
    ! [A_167] :
      ( k3_xboole_0(k5_relat_1(A_167,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_167,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_167,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_167,k1_xboole_0))
      | ~ v1_relat_1(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1625,c_40])).

tff(c_1650,plain,(
    ! [A_168] :
      ( k5_relat_1(A_168,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_168,k1_xboole_0))
      | ~ v1_relat_1(A_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1457,c_1640])).

tff(c_1654,plain,(
    ! [A_39] :
      ( k5_relat_1(A_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_36,c_1650])).

tff(c_1658,plain,(
    ! [A_169] :
      ( k5_relat_1(A_169,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1654])).

tff(c_1673,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_1658])).

tff(c_1681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1395,c_1673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/2.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/2.55  
% 4.37/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/2.56  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 4.37/2.56  
% 4.37/2.56  %Foreground sorts:
% 4.37/2.56  
% 4.37/2.56  
% 4.37/2.56  %Background operators:
% 4.37/2.56  
% 4.37/2.56  
% 4.37/2.56  %Foreground operators:
% 4.37/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/2.56  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.37/2.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.37/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/2.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.37/2.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.37/2.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.37/2.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.37/2.56  tff('#skF_1', type, '#skF_1': $i).
% 4.37/2.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.37/2.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.37/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.37/2.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.37/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/2.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.37/2.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.37/2.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.37/2.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.37/2.56  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.37/2.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.37/2.56  
% 4.37/2.58  tff(f_110, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 4.37/2.58  tff(f_66, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.37/2.58  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.37/2.58  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.37/2.58  tff(f_103, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.37/2.58  tff(f_86, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 4.37/2.58  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 4.37/2.58  tff(f_72, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.37/2.58  tff(f_38, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.37/2.58  tff(f_56, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 4.37/2.58  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.37/2.58  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.37/2.58  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.37/2.58  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 4.37/2.58  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 4.37/2.58  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 4.37/2.58  tff(c_54, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.37/2.58  tff(c_79, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 4.37/2.58  tff(c_56, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.37/2.58  tff(c_34, plain, (![A_38]: (v1_relat_1(k4_relat_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.37/2.58  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.37/2.58  tff(c_74, plain, (![A_53]: (v1_relat_1(A_53) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.37/2.58  tff(c_78, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_74])).
% 4.37/2.58  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.37/2.58  tff(c_42, plain, (![A_43]: (k2_relat_1(k4_relat_1(A_43))=k1_relat_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.37/2.58  tff(c_281, plain, (![A_86, B_87]: (r1_tarski(k2_relat_1(k5_relat_1(A_86, B_87)), k2_relat_1(B_87)) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.37/2.58  tff(c_570, plain, (![A_110, A_111]: (r1_tarski(k2_relat_1(k5_relat_1(A_110, k4_relat_1(A_111))), k1_relat_1(A_111)) | ~v1_relat_1(k4_relat_1(A_111)) | ~v1_relat_1(A_110) | ~v1_relat_1(A_111))), inference(superposition, [status(thm), theory('equality')], [c_42, c_281])).
% 4.37/2.58  tff(c_584, plain, (![A_110]: (r1_tarski(k2_relat_1(k5_relat_1(A_110, k4_relat_1(k1_xboole_0))), k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_110) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_570])).
% 4.37/2.58  tff(c_587, plain, (![A_110]: (r1_tarski(k2_relat_1(k5_relat_1(A_110, k4_relat_1(k1_xboole_0))), k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_584])).
% 4.37/2.58  tff(c_597, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_587])).
% 4.37/2.58  tff(c_600, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_597])).
% 4.37/2.58  tff(c_604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_600])).
% 4.37/2.58  tff(c_606, plain, (v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_587])).
% 4.37/2.58  tff(c_36, plain, (![A_39, B_40]: (v1_relat_1(k5_relat_1(A_39, B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.37/2.58  tff(c_12, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.37/2.58  tff(c_88, plain, (![A_56, B_57]: (v1_xboole_0(k2_zfmisc_1(A_56, B_57)) | ~v1_xboole_0(B_57))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.37/2.58  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.37/2.58  tff(c_130, plain, (![A_62, B_63]: (k2_zfmisc_1(A_62, B_63)=k1_xboole_0 | ~v1_xboole_0(B_63))), inference(resolution, [status(thm)], [c_88, c_4])).
% 4.37/2.58  tff(c_136, plain, (![A_62]: (k2_zfmisc_1(A_62, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_130])).
% 4.37/2.58  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.37/2.58  tff(c_289, plain, (![A_86]: (r1_tarski(k2_relat_1(k5_relat_1(A_86, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_50, c_281])).
% 4.37/2.58  tff(c_293, plain, (![A_88]: (r1_tarski(k2_relat_1(k5_relat_1(A_88, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_289])).
% 4.37/2.58  tff(c_14, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.37/2.58  tff(c_185, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.37/2.58  tff(c_194, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_185])).
% 4.37/2.58  tff(c_303, plain, (![A_89]: (k2_relat_1(k5_relat_1(A_89, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_89))), inference(resolution, [status(thm)], [c_293, c_194])).
% 4.37/2.58  tff(c_40, plain, (![A_42]: (k3_xboole_0(A_42, k2_zfmisc_1(k1_relat_1(A_42), k2_relat_1(A_42)))=A_42 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.37/2.58  tff(c_318, plain, (![A_89]: (k3_xboole_0(k5_relat_1(A_89, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_89, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_89, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_89, k1_xboole_0)) | ~v1_relat_1(A_89))), inference(superposition, [status(thm), theory('equality')], [c_303, c_40])).
% 4.37/2.58  tff(c_328, plain, (![A_90]: (k5_relat_1(A_90, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_90, k1_xboole_0)) | ~v1_relat_1(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_136, c_318])).
% 4.37/2.58  tff(c_332, plain, (![A_39]: (k5_relat_1(A_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_36, c_328])).
% 4.37/2.58  tff(c_335, plain, (![A_39]: (k5_relat_1(A_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_332])).
% 4.37/2.58  tff(c_610, plain, (k5_relat_1(k4_relat_1(k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_606, c_335])).
% 4.37/2.58  tff(c_38, plain, (![A_41]: (k4_relat_1(k4_relat_1(A_41))=A_41 | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.37/2.58  tff(c_414, plain, (![B_97, A_98]: (k5_relat_1(k4_relat_1(B_97), k4_relat_1(A_98))=k4_relat_1(k5_relat_1(A_98, B_97)) | ~v1_relat_1(B_97) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.37/2.58  tff(c_769, plain, (![A_124, B_125]: (k4_relat_1(k5_relat_1(k4_relat_1(A_124), B_125))=k5_relat_1(k4_relat_1(B_125), A_124) | ~v1_relat_1(B_125) | ~v1_relat_1(k4_relat_1(A_124)) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_38, c_414])).
% 4.37/2.58  tff(c_811, plain, (k5_relat_1(k4_relat_1(k1_xboole_0), k1_xboole_0)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_610, c_769])).
% 4.37/2.58  tff(c_824, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78, c_606, c_78, c_610, c_811])).
% 4.37/2.58  tff(c_345, plain, (![A_96]: (k5_relat_1(A_96, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_332])).
% 4.37/2.58  tff(c_363, plain, (![A_38]: (k5_relat_1(k4_relat_1(A_38), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_34, c_345])).
% 4.37/2.58  tff(c_814, plain, (![A_38]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_38)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_38)) | ~v1_relat_1(A_38) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_363, c_769])).
% 4.37/2.58  tff(c_826, plain, (![A_38]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_38)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_38)) | ~v1_relat_1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_814])).
% 4.37/2.58  tff(c_1319, plain, (![A_134]: (k5_relat_1(k1_xboole_0, A_134)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_134)) | ~v1_relat_1(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_824, c_824, c_826])).
% 4.37/2.58  tff(c_1358, plain, (![A_135]: (k5_relat_1(k1_xboole_0, A_135)=k1_xboole_0 | ~v1_relat_1(A_135))), inference(resolution, [status(thm)], [c_34, c_1319])).
% 4.37/2.58  tff(c_1382, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_1358])).
% 4.37/2.58  tff(c_1394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_1382])).
% 4.37/2.58  tff(c_1395, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 4.37/2.58  tff(c_1409, plain, (![A_138, B_139]: (v1_xboole_0(k2_zfmisc_1(A_138, B_139)) | ~v1_xboole_0(B_139))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.37/2.58  tff(c_1451, plain, (![A_144, B_145]: (k2_zfmisc_1(A_144, B_145)=k1_xboole_0 | ~v1_xboole_0(B_145))), inference(resolution, [status(thm)], [c_1409, c_4])).
% 4.37/2.58  tff(c_1457, plain, (![A_144]: (k2_zfmisc_1(A_144, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1451])).
% 4.37/2.58  tff(c_1598, plain, (![A_164, B_165]: (r1_tarski(k2_relat_1(k5_relat_1(A_164, B_165)), k2_relat_1(B_165)) | ~v1_relat_1(B_165) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.37/2.58  tff(c_1609, plain, (![A_164]: (r1_tarski(k2_relat_1(k5_relat_1(A_164, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_164))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1598])).
% 4.37/2.58  tff(c_1615, plain, (![A_166]: (r1_tarski(k2_relat_1(k5_relat_1(A_166, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1609])).
% 4.37/2.58  tff(c_1505, plain, (![B_152, A_153]: (B_152=A_153 | ~r1_tarski(B_152, A_153) | ~r1_tarski(A_153, B_152))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.37/2.58  tff(c_1514, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_1505])).
% 4.37/2.58  tff(c_1625, plain, (![A_167]: (k2_relat_1(k5_relat_1(A_167, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_167))), inference(resolution, [status(thm)], [c_1615, c_1514])).
% 4.37/2.58  tff(c_1640, plain, (![A_167]: (k3_xboole_0(k5_relat_1(A_167, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_167, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_167, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_167, k1_xboole_0)) | ~v1_relat_1(A_167))), inference(superposition, [status(thm), theory('equality')], [c_1625, c_40])).
% 4.37/2.58  tff(c_1650, plain, (![A_168]: (k5_relat_1(A_168, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_168, k1_xboole_0)) | ~v1_relat_1(A_168))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1457, c_1640])).
% 4.37/2.58  tff(c_1654, plain, (![A_39]: (k5_relat_1(A_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_36, c_1650])).
% 4.37/2.58  tff(c_1658, plain, (![A_169]: (k5_relat_1(A_169, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_169))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1654])).
% 4.37/2.58  tff(c_1673, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_1658])).
% 4.37/2.58  tff(c_1681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1395, c_1673])).
% 4.37/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/2.58  
% 4.37/2.58  Inference rules
% 4.37/2.58  ----------------------
% 4.37/2.58  #Ref     : 0
% 4.37/2.58  #Sup     : 386
% 4.37/2.58  #Fact    : 0
% 4.37/2.58  #Define  : 0
% 4.37/2.58  #Split   : 2
% 4.37/2.59  #Chain   : 0
% 4.37/2.59  #Close   : 0
% 4.37/2.59  
% 4.37/2.59  Ordering : KBO
% 4.37/2.59  
% 4.37/2.59  Simplification rules
% 4.37/2.59  ----------------------
% 4.37/2.59  #Subsume      : 30
% 4.37/2.59  #Demod        : 325
% 4.37/2.59  #Tautology    : 200
% 4.37/2.59  #SimpNegUnit  : 2
% 4.37/2.59  #BackRed      : 4
% 4.37/2.59  
% 4.37/2.59  #Partial instantiations: 0
% 4.37/2.59  #Strategies tried      : 1
% 4.37/2.59  
% 4.37/2.59  Timing (in seconds)
% 4.37/2.59  ----------------------
% 4.37/2.59  Preprocessing        : 0.63
% 4.37/2.59  Parsing              : 0.37
% 4.37/2.59  CNF conversion       : 0.03
% 4.37/2.59  Main loop            : 1.01
% 4.37/2.59  Inferencing          : 0.38
% 4.37/2.59  Reduction            : 0.29
% 4.37/2.59  Demodulation         : 0.21
% 4.37/2.59  BG Simplification    : 0.05
% 4.37/2.59  Subsumption          : 0.22
% 4.37/2.59  Abstraction          : 0.07
% 4.37/2.59  MUC search           : 0.00
% 4.37/2.59  Cooper               : 0.00
% 4.37/2.59  Total                : 1.70
% 4.37/2.59  Index Insertion      : 0.00
% 4.37/2.59  Index Deletion       : 0.00
% 4.37/2.59  Index Matching       : 0.00
% 4.37/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
