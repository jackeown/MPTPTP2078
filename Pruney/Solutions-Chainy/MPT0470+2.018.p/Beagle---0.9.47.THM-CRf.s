%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:03 EST 2020

% Result     : Theorem 5.40s
% Output     : CNFRefutation 5.40s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 492 expanded)
%              Number of leaves         :   41 ( 182 expanded)
%              Depth                    :   26
%              Number of atoms          :  234 ( 755 expanded)
%              Number of equality atoms :   78 ( 319 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

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

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_58,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_86,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_60,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_81,plain,(
    ! [A_57] :
      ( v1_relat_1(A_57)
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_85,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_81])).

tff(c_40,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k5_relat_1(A_43,B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_157,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_166,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_157])).

tff(c_169,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_166])).

tff(c_285,plain,(
    ! [A_87,C_88,B_89] : k4_xboole_0(k2_zfmisc_1(A_87,C_88),k2_zfmisc_1(B_89,C_88)) = k2_zfmisc_1(k4_xboole_0(A_87,B_89),C_88) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_292,plain,(
    ! [B_89,C_88] : k2_zfmisc_1(k4_xboole_0(B_89,B_89),C_88) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_169])).

tff(c_301,plain,(
    ! [C_88] : k2_zfmisc_1(k1_xboole_0,C_88) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_292])).

tff(c_38,plain,(
    ! [A_42] :
      ( v1_relat_1(k4_relat_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_48,plain,(
    ! [A_47] :
      ( k1_relat_1(k4_relat_1(A_47)) = k2_relat_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_210,plain,(
    ! [A_78] :
      ( r1_tarski(A_78,k2_zfmisc_1(k1_relat_1(A_78),k2_relat_1(A_78)))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_578,plain,(
    ! [A_112] :
      ( r1_tarski(k4_relat_1(A_112),k2_zfmisc_1(k2_relat_1(A_112),k2_relat_1(k4_relat_1(A_112))))
      | ~ v1_relat_1(k4_relat_1(A_112))
      | ~ v1_relat_1(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_210])).

tff(c_598,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k1_xboole_0))))
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_578])).

tff(c_602,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_301,c_598])).

tff(c_603,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_602])).

tff(c_606,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_603])).

tff(c_610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_606])).

tff(c_611,plain,(
    r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_602])).

tff(c_14,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_178,plain,(
    ! [B_72,A_73] :
      ( B_72 = A_73
      | ~ r1_tarski(B_72,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_187,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_178])).

tff(c_627,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_611,c_187])).

tff(c_52,plain,(
    ! [B_53,A_51] :
      ( k5_relat_1(k4_relat_1(B_53),k4_relat_1(A_51)) = k4_relat_1(k5_relat_1(A_51,B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_647,plain,(
    ! [B_53] :
      ( k5_relat_1(k4_relat_1(B_53),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_52])).

tff(c_680,plain,(
    ! [B_119] :
      ( k5_relat_1(k4_relat_1(B_119),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_119))
      | ~ v1_relat_1(B_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_647])).

tff(c_230,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_79,B_80)),k2_relat_1(B_80))
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_238,plain,(
    ! [A_79] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_79,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_230])).

tff(c_242,plain,(
    ! [A_81] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_81,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_238])).

tff(c_248,plain,(
    ! [A_81] :
      ( k2_relat_1(k5_relat_1(A_81,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_242,c_187])).

tff(c_1091,plain,(
    ! [B_133] :
      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,B_133))) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(B_133))
      | ~ v1_relat_1(B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_248])).

tff(c_46,plain,(
    ! [A_47] :
      ( k2_relat_1(k4_relat_1(A_47)) = k1_relat_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1906,plain,(
    ! [B_157] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_157)) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_157))
      | ~ v1_relat_1(k4_relat_1(B_157))
      | ~ v1_relat_1(B_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_46])).

tff(c_1923,plain,(
    ! [B_44] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_44)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_1906])).

tff(c_1933,plain,(
    ! [B_158] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_158)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(B_158))
      | ~ v1_relat_1(B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1923])).

tff(c_1970,plain,(
    ! [A_159] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,A_159)) = k1_xboole_0
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_38,c_1933])).

tff(c_44,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,k2_zfmisc_1(k1_relat_1(A_46),k2_relat_1(A_46)))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1988,plain,(
    ! [A_159] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,A_159),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,A_159))))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,A_159))
      | ~ v1_relat_1(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1970,c_44])).

tff(c_2006,plain,(
    ! [A_160] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,A_160),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,A_160))
      | ~ v1_relat_1(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_1988])).

tff(c_2024,plain,(
    ! [A_161] :
      ( k5_relat_1(k1_xboole_0,A_161) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,A_161))
      | ~ v1_relat_1(A_161) ) ),
    inference(resolution,[status(thm)],[c_2006,c_187])).

tff(c_2041,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_2024])).

tff(c_2051,plain,(
    ! [B_162] :
      ( k5_relat_1(k1_xboole_0,B_162) = k1_xboole_0
      | ~ v1_relat_1(B_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2041])).

tff(c_2078,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_2051])).

tff(c_2091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2078])).

tff(c_2092,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2174,plain,(
    ! [A_174,B_175] : k5_xboole_0(A_174,k3_xboole_0(A_174,B_175)) = k4_xboole_0(A_174,B_175) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2183,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2174])).

tff(c_2186,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2183])).

tff(c_2306,plain,(
    ! [C_192,A_193,B_194] : k4_xboole_0(k2_zfmisc_1(C_192,A_193),k2_zfmisc_1(C_192,B_194)) = k2_zfmisc_1(C_192,k4_xboole_0(A_193,B_194)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2313,plain,(
    ! [C_192,B_194] : k2_zfmisc_1(C_192,k4_xboole_0(B_194,B_194)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2306,c_2186])).

tff(c_2322,plain,(
    ! [C_192] : k2_zfmisc_1(C_192,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_2313])).

tff(c_56,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2217,plain,(
    ! [A_180] :
      ( r1_tarski(A_180,k2_zfmisc_1(k1_relat_1(A_180),k2_relat_1(A_180)))
      | ~ v1_relat_1(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2616,plain,(
    ! [A_219] :
      ( r1_tarski(k4_relat_1(A_219),k2_zfmisc_1(k1_relat_1(k4_relat_1(A_219)),k1_relat_1(A_219)))
      | ~ v1_relat_1(k4_relat_1(A_219))
      | ~ v1_relat_1(A_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2217])).

tff(c_2633,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0))
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2616])).

tff(c_2636,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2322,c_2633])).

tff(c_2637,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_2636])).

tff(c_2640,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_2637])).

tff(c_2644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2640])).

tff(c_2645,plain,(
    r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2636])).

tff(c_2187,plain,(
    ! [B_176,A_177] :
      ( B_176 = A_177
      | ~ r1_tarski(B_176,A_177)
      | ~ r1_tarski(A_177,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2196,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_2187])).

tff(c_2661,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2645,c_2196])).

tff(c_2339,plain,(
    ! [A_196,C_197,B_198] : k4_xboole_0(k2_zfmisc_1(A_196,C_197),k2_zfmisc_1(B_198,C_197)) = k2_zfmisc_1(k4_xboole_0(A_196,B_198),C_197) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [C_38,A_36,B_37] : k4_xboole_0(k2_zfmisc_1(C_38,A_36),k2_zfmisc_1(C_38,B_37)) = k2_zfmisc_1(C_38,k4_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2346,plain,(
    ! [B_198,C_197] : k2_zfmisc_1(k4_xboole_0(B_198,B_198),C_197) = k2_zfmisc_1(B_198,k4_xboole_0(C_197,C_197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2339,c_32])).

tff(c_2369,plain,(
    ! [C_197] : k2_zfmisc_1(k1_xboole_0,C_197) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2322,c_2186,c_2186,c_2346])).

tff(c_2681,plain,(
    ! [B_53] :
      ( k5_relat_1(k4_relat_1(B_53),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2661,c_52])).

tff(c_2723,plain,(
    ! [B_233] :
      ( k5_relat_1(k4_relat_1(B_233),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_233))
      | ~ v1_relat_1(B_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2681])).

tff(c_2246,plain,(
    ! [A_184,B_185] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_184,B_185)),k2_relat_1(B_185))
      | ~ v1_relat_1(B_185)
      | ~ v1_relat_1(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2257,plain,(
    ! [A_184] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_184,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2246])).

tff(c_2263,plain,(
    ! [A_186] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_186,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2257])).

tff(c_2269,plain,(
    ! [A_186] :
      ( k2_relat_1(k5_relat_1(A_186,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_186) ) ),
    inference(resolution,[status(thm)],[c_2263,c_2196])).

tff(c_2886,plain,(
    ! [B_238] :
      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,B_238))) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(B_238))
      | ~ v1_relat_1(B_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2723,c_2269])).

tff(c_3970,plain,(
    ! [B_264] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_264)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(B_264))
      | ~ v1_relat_1(B_264)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_264)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2886])).

tff(c_3987,plain,(
    ! [B_44] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_44)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_3970])).

tff(c_4002,plain,(
    ! [B_265] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_265)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(B_265))
      | ~ v1_relat_1(B_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_3987])).

tff(c_4039,plain,(
    ! [A_266] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,A_266)) = k1_xboole_0
      | ~ v1_relat_1(A_266) ) ),
    inference(resolution,[status(thm)],[c_38,c_4002])).

tff(c_4057,plain,(
    ! [A_266] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,A_266),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,A_266))))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,A_266))
      | ~ v1_relat_1(A_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4039,c_44])).

tff(c_4080,plain,(
    ! [A_267] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,A_267),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,A_267))
      | ~ v1_relat_1(A_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2369,c_4057])).

tff(c_4243,plain,(
    ! [A_270] :
      ( k5_relat_1(k1_xboole_0,A_270) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,A_270))
      | ~ v1_relat_1(A_270) ) ),
    inference(resolution,[status(thm)],[c_4080,c_2196])).

tff(c_4260,plain,(
    ! [B_44] :
      ( k5_relat_1(k1_xboole_0,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_4243])).

tff(c_4275,plain,(
    ! [B_271] :
      ( k5_relat_1(k1_xboole_0,B_271) = k1_xboole_0
      | ~ v1_relat_1(B_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_4260])).

tff(c_4314,plain,(
    ! [A_272] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_272)) = k1_xboole_0
      | ~ v1_relat_1(A_272) ) ),
    inference(resolution,[status(thm)],[c_38,c_4275])).

tff(c_42,plain,(
    ! [A_45] :
      ( k4_relat_1(k4_relat_1(A_45)) = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2425,plain,(
    ! [B_202,A_203] :
      ( k5_relat_1(k4_relat_1(B_202),k4_relat_1(A_203)) = k4_relat_1(k5_relat_1(A_203,B_202))
      | ~ v1_relat_1(B_202)
      | ~ v1_relat_1(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2440,plain,(
    ! [A_203,A_45] :
      ( k4_relat_1(k5_relat_1(A_203,k4_relat_1(A_45))) = k5_relat_1(A_45,k4_relat_1(A_203))
      | ~ v1_relat_1(k4_relat_1(A_45))
      | ~ v1_relat_1(A_203)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2425])).

tff(c_4326,plain,(
    ! [A_272] :
      ( k5_relat_1(A_272,k4_relat_1(k1_xboole_0)) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_272))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_272)
      | ~ v1_relat_1(A_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4314,c_2440])).

tff(c_4636,plain,(
    ! [A_276] :
      ( k5_relat_1(A_276,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_276))
      | ~ v1_relat_1(A_276) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_2661,c_2661,c_4326])).

tff(c_4681,plain,(
    ! [A_277] :
      ( k5_relat_1(A_277,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_277) ) ),
    inference(resolution,[status(thm)],[c_38,c_4636])).

tff(c_4708,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_4681])).

tff(c_4721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2092,c_4708])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.40/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.01  
% 5.40/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.01  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 5.40/2.01  
% 5.40/2.01  %Foreground sorts:
% 5.40/2.01  
% 5.40/2.01  
% 5.40/2.01  %Background operators:
% 5.40/2.01  
% 5.40/2.01  
% 5.40/2.01  %Foreground operators:
% 5.40/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.40/2.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.40/2.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.40/2.01  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.40/2.01  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.40/2.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.40/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.40/2.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.40/2.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.40/2.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.40/2.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.40/2.01  tff('#skF_1', type, '#skF_1': $i).
% 5.40/2.01  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.40/2.01  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.40/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.40/2.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.40/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.40/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.40/2.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.40/2.01  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.40/2.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.40/2.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.40/2.01  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.40/2.01  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.40/2.01  
% 5.40/2.03  tff(f_110, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 5.40/2.03  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.40/2.03  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 5.40/2.03  tff(f_72, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.40/2.03  tff(f_40, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.40/2.03  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.40/2.03  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.40/2.03  tff(f_56, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 5.40/2.03  tff(f_66, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 5.40/2.03  tff(f_103, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.40/2.03  tff(f_86, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 5.40/2.03  tff(f_80, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 5.40/2.03  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.40/2.03  tff(f_34, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.40/2.03  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 5.40/2.03  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 5.40/2.03  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 5.40/2.03  tff(c_58, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.40/2.03  tff(c_86, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_58])).
% 5.40/2.03  tff(c_60, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.40/2.03  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.40/2.03  tff(c_81, plain, (![A_57]: (v1_relat_1(A_57) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.40/2.03  tff(c_85, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_81])).
% 5.40/2.03  tff(c_40, plain, (![A_43, B_44]: (v1_relat_1(k5_relat_1(A_43, B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.40/2.03  tff(c_16, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.40/2.03  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.40/2.03  tff(c_157, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.40/2.03  tff(c_166, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_157])).
% 5.40/2.03  tff(c_169, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_166])).
% 5.40/2.03  tff(c_285, plain, (![A_87, C_88, B_89]: (k4_xboole_0(k2_zfmisc_1(A_87, C_88), k2_zfmisc_1(B_89, C_88))=k2_zfmisc_1(k4_xboole_0(A_87, B_89), C_88))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.40/2.03  tff(c_292, plain, (![B_89, C_88]: (k2_zfmisc_1(k4_xboole_0(B_89, B_89), C_88)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_285, c_169])).
% 5.40/2.03  tff(c_301, plain, (![C_88]: (k2_zfmisc_1(k1_xboole_0, C_88)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_169, c_292])).
% 5.40/2.03  tff(c_38, plain, (![A_42]: (v1_relat_1(k4_relat_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.40/2.03  tff(c_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.40/2.03  tff(c_48, plain, (![A_47]: (k1_relat_1(k4_relat_1(A_47))=k2_relat_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.40/2.03  tff(c_210, plain, (![A_78]: (r1_tarski(A_78, k2_zfmisc_1(k1_relat_1(A_78), k2_relat_1(A_78))) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.40/2.03  tff(c_578, plain, (![A_112]: (r1_tarski(k4_relat_1(A_112), k2_zfmisc_1(k2_relat_1(A_112), k2_relat_1(k4_relat_1(A_112)))) | ~v1_relat_1(k4_relat_1(A_112)) | ~v1_relat_1(A_112))), inference(superposition, [status(thm), theory('equality')], [c_48, c_210])).
% 5.40/2.03  tff(c_598, plain, (r1_tarski(k4_relat_1(k1_xboole_0), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k4_relat_1(k1_xboole_0)))) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_578])).
% 5.40/2.03  tff(c_602, plain, (r1_tarski(k4_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_301, c_598])).
% 5.40/2.03  tff(c_603, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_602])).
% 5.40/2.03  tff(c_606, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_603])).
% 5.40/2.03  tff(c_610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_606])).
% 5.40/2.03  tff(c_611, plain, (r1_tarski(k4_relat_1(k1_xboole_0), k1_xboole_0)), inference(splitRight, [status(thm)], [c_602])).
% 5.40/2.03  tff(c_14, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.40/2.03  tff(c_178, plain, (![B_72, A_73]: (B_72=A_73 | ~r1_tarski(B_72, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.40/2.03  tff(c_187, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_178])).
% 5.40/2.03  tff(c_627, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_611, c_187])).
% 5.40/2.03  tff(c_52, plain, (![B_53, A_51]: (k5_relat_1(k4_relat_1(B_53), k4_relat_1(A_51))=k4_relat_1(k5_relat_1(A_51, B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.40/2.03  tff(c_647, plain, (![B_53]: (k5_relat_1(k4_relat_1(B_53), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_627, c_52])).
% 5.40/2.03  tff(c_680, plain, (![B_119]: (k5_relat_1(k4_relat_1(B_119), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_119)) | ~v1_relat_1(B_119))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_647])).
% 5.40/2.03  tff(c_230, plain, (![A_79, B_80]: (r1_tarski(k2_relat_1(k5_relat_1(A_79, B_80)), k2_relat_1(B_80)) | ~v1_relat_1(B_80) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.40/2.03  tff(c_238, plain, (![A_79]: (r1_tarski(k2_relat_1(k5_relat_1(A_79, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_79))), inference(superposition, [status(thm), theory('equality')], [c_54, c_230])).
% 5.40/2.03  tff(c_242, plain, (![A_81]: (r1_tarski(k2_relat_1(k5_relat_1(A_81, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_238])).
% 5.40/2.03  tff(c_248, plain, (![A_81]: (k2_relat_1(k5_relat_1(A_81, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_242, c_187])).
% 5.40/2.03  tff(c_1091, plain, (![B_133]: (k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0, B_133)))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(B_133)) | ~v1_relat_1(B_133))), inference(superposition, [status(thm), theory('equality')], [c_680, c_248])).
% 5.40/2.03  tff(c_46, plain, (![A_47]: (k2_relat_1(k4_relat_1(A_47))=k1_relat_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.40/2.03  tff(c_1906, plain, (![B_157]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_157))=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_157)) | ~v1_relat_1(k4_relat_1(B_157)) | ~v1_relat_1(B_157))), inference(superposition, [status(thm), theory('equality')], [c_1091, c_46])).
% 5.40/2.03  tff(c_1923, plain, (![B_44]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_44))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_1906])).
% 5.40/2.03  tff(c_1933, plain, (![B_158]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_158))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(B_158)) | ~v1_relat_1(B_158))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1923])).
% 5.40/2.03  tff(c_1970, plain, (![A_159]: (k1_relat_1(k5_relat_1(k1_xboole_0, A_159))=k1_xboole_0 | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_38, c_1933])).
% 5.40/2.03  tff(c_44, plain, (![A_46]: (r1_tarski(A_46, k2_zfmisc_1(k1_relat_1(A_46), k2_relat_1(A_46))) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.40/2.03  tff(c_1988, plain, (![A_159]: (r1_tarski(k5_relat_1(k1_xboole_0, A_159), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, A_159)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0, A_159)) | ~v1_relat_1(A_159))), inference(superposition, [status(thm), theory('equality')], [c_1970, c_44])).
% 5.40/2.03  tff(c_2006, plain, (![A_160]: (r1_tarski(k5_relat_1(k1_xboole_0, A_160), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, A_160)) | ~v1_relat_1(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_1988])).
% 5.40/2.03  tff(c_2024, plain, (![A_161]: (k5_relat_1(k1_xboole_0, A_161)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, A_161)) | ~v1_relat_1(A_161))), inference(resolution, [status(thm)], [c_2006, c_187])).
% 5.40/2.03  tff(c_2041, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_2024])).
% 5.40/2.03  tff(c_2051, plain, (![B_162]: (k5_relat_1(k1_xboole_0, B_162)=k1_xboole_0 | ~v1_relat_1(B_162))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2041])).
% 5.40/2.03  tff(c_2078, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_2051])).
% 5.40/2.03  tff(c_2091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_2078])).
% 5.40/2.03  tff(c_2092, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_58])).
% 5.40/2.03  tff(c_2174, plain, (![A_174, B_175]: (k5_xboole_0(A_174, k3_xboole_0(A_174, B_175))=k4_xboole_0(A_174, B_175))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.40/2.03  tff(c_2183, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2174])).
% 5.40/2.03  tff(c_2186, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2183])).
% 5.40/2.03  tff(c_2306, plain, (![C_192, A_193, B_194]: (k4_xboole_0(k2_zfmisc_1(C_192, A_193), k2_zfmisc_1(C_192, B_194))=k2_zfmisc_1(C_192, k4_xboole_0(A_193, B_194)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.40/2.03  tff(c_2313, plain, (![C_192, B_194]: (k2_zfmisc_1(C_192, k4_xboole_0(B_194, B_194))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2306, c_2186])).
% 5.40/2.03  tff(c_2322, plain, (![C_192]: (k2_zfmisc_1(C_192, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_2313])).
% 5.40/2.03  tff(c_56, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.40/2.03  tff(c_2217, plain, (![A_180]: (r1_tarski(A_180, k2_zfmisc_1(k1_relat_1(A_180), k2_relat_1(A_180))) | ~v1_relat_1(A_180))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.40/2.03  tff(c_2616, plain, (![A_219]: (r1_tarski(k4_relat_1(A_219), k2_zfmisc_1(k1_relat_1(k4_relat_1(A_219)), k1_relat_1(A_219))) | ~v1_relat_1(k4_relat_1(A_219)) | ~v1_relat_1(A_219))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2217])).
% 5.40/2.03  tff(c_2633, plain, (r1_tarski(k4_relat_1(k1_xboole_0), k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_2616])).
% 5.40/2.03  tff(c_2636, plain, (r1_tarski(k4_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2322, c_2633])).
% 5.40/2.03  tff(c_2637, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2636])).
% 5.40/2.03  tff(c_2640, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_2637])).
% 5.40/2.03  tff(c_2644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_2640])).
% 5.40/2.03  tff(c_2645, plain, (r1_tarski(k4_relat_1(k1_xboole_0), k1_xboole_0)), inference(splitRight, [status(thm)], [c_2636])).
% 5.40/2.03  tff(c_2187, plain, (![B_176, A_177]: (B_176=A_177 | ~r1_tarski(B_176, A_177) | ~r1_tarski(A_177, B_176))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.40/2.03  tff(c_2196, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_2187])).
% 5.40/2.03  tff(c_2661, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2645, c_2196])).
% 5.40/2.03  tff(c_2339, plain, (![A_196, C_197, B_198]: (k4_xboole_0(k2_zfmisc_1(A_196, C_197), k2_zfmisc_1(B_198, C_197))=k2_zfmisc_1(k4_xboole_0(A_196, B_198), C_197))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.40/2.03  tff(c_32, plain, (![C_38, A_36, B_37]: (k4_xboole_0(k2_zfmisc_1(C_38, A_36), k2_zfmisc_1(C_38, B_37))=k2_zfmisc_1(C_38, k4_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.40/2.03  tff(c_2346, plain, (![B_198, C_197]: (k2_zfmisc_1(k4_xboole_0(B_198, B_198), C_197)=k2_zfmisc_1(B_198, k4_xboole_0(C_197, C_197)))), inference(superposition, [status(thm), theory('equality')], [c_2339, c_32])).
% 5.40/2.03  tff(c_2369, plain, (![C_197]: (k2_zfmisc_1(k1_xboole_0, C_197)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2322, c_2186, c_2186, c_2346])).
% 5.40/2.03  tff(c_2681, plain, (![B_53]: (k5_relat_1(k4_relat_1(B_53), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2661, c_52])).
% 5.40/2.03  tff(c_2723, plain, (![B_233]: (k5_relat_1(k4_relat_1(B_233), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_233)) | ~v1_relat_1(B_233))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2681])).
% 5.40/2.03  tff(c_2246, plain, (![A_184, B_185]: (r1_tarski(k2_relat_1(k5_relat_1(A_184, B_185)), k2_relat_1(B_185)) | ~v1_relat_1(B_185) | ~v1_relat_1(A_184))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.40/2.03  tff(c_2257, plain, (![A_184]: (r1_tarski(k2_relat_1(k5_relat_1(A_184, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_184))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2246])).
% 5.40/2.03  tff(c_2263, plain, (![A_186]: (r1_tarski(k2_relat_1(k5_relat_1(A_186, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2257])).
% 5.40/2.03  tff(c_2269, plain, (![A_186]: (k2_relat_1(k5_relat_1(A_186, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_186))), inference(resolution, [status(thm)], [c_2263, c_2196])).
% 5.40/2.03  tff(c_2886, plain, (![B_238]: (k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0, B_238)))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(B_238)) | ~v1_relat_1(B_238))), inference(superposition, [status(thm), theory('equality')], [c_2723, c_2269])).
% 5.40/2.03  tff(c_3970, plain, (![B_264]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_264))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(B_264)) | ~v1_relat_1(B_264) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_264)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2886])).
% 5.40/2.03  tff(c_3987, plain, (![B_44]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_44))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_3970])).
% 5.40/2.03  tff(c_4002, plain, (![B_265]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_265))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(B_265)) | ~v1_relat_1(B_265))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_3987])).
% 5.40/2.03  tff(c_4039, plain, (![A_266]: (k1_relat_1(k5_relat_1(k1_xboole_0, A_266))=k1_xboole_0 | ~v1_relat_1(A_266))), inference(resolution, [status(thm)], [c_38, c_4002])).
% 5.40/2.03  tff(c_4057, plain, (![A_266]: (r1_tarski(k5_relat_1(k1_xboole_0, A_266), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, A_266)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0, A_266)) | ~v1_relat_1(A_266))), inference(superposition, [status(thm), theory('equality')], [c_4039, c_44])).
% 5.40/2.03  tff(c_4080, plain, (![A_267]: (r1_tarski(k5_relat_1(k1_xboole_0, A_267), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, A_267)) | ~v1_relat_1(A_267))), inference(demodulation, [status(thm), theory('equality')], [c_2369, c_4057])).
% 5.40/2.03  tff(c_4243, plain, (![A_270]: (k5_relat_1(k1_xboole_0, A_270)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, A_270)) | ~v1_relat_1(A_270))), inference(resolution, [status(thm)], [c_4080, c_2196])).
% 5.40/2.03  tff(c_4260, plain, (![B_44]: (k5_relat_1(k1_xboole_0, B_44)=k1_xboole_0 | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_4243])).
% 5.40/2.03  tff(c_4275, plain, (![B_271]: (k5_relat_1(k1_xboole_0, B_271)=k1_xboole_0 | ~v1_relat_1(B_271))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_4260])).
% 5.40/2.03  tff(c_4314, plain, (![A_272]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_272))=k1_xboole_0 | ~v1_relat_1(A_272))), inference(resolution, [status(thm)], [c_38, c_4275])).
% 5.40/2.03  tff(c_42, plain, (![A_45]: (k4_relat_1(k4_relat_1(A_45))=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.40/2.03  tff(c_2425, plain, (![B_202, A_203]: (k5_relat_1(k4_relat_1(B_202), k4_relat_1(A_203))=k4_relat_1(k5_relat_1(A_203, B_202)) | ~v1_relat_1(B_202) | ~v1_relat_1(A_203))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.40/2.03  tff(c_2440, plain, (![A_203, A_45]: (k4_relat_1(k5_relat_1(A_203, k4_relat_1(A_45)))=k5_relat_1(A_45, k4_relat_1(A_203)) | ~v1_relat_1(k4_relat_1(A_45)) | ~v1_relat_1(A_203) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2425])).
% 5.40/2.03  tff(c_4326, plain, (![A_272]: (k5_relat_1(A_272, k4_relat_1(k1_xboole_0))=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_272)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_272) | ~v1_relat_1(A_272))), inference(superposition, [status(thm), theory('equality')], [c_4314, c_2440])).
% 5.40/2.03  tff(c_4636, plain, (![A_276]: (k5_relat_1(A_276, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_276)) | ~v1_relat_1(A_276))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_2661, c_2661, c_4326])).
% 5.40/2.03  tff(c_4681, plain, (![A_277]: (k5_relat_1(A_277, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_277))), inference(resolution, [status(thm)], [c_38, c_4636])).
% 5.40/2.03  tff(c_4708, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_4681])).
% 5.40/2.03  tff(c_4721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2092, c_4708])).
% 5.40/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.40/2.03  
% 5.40/2.03  Inference rules
% 5.40/2.03  ----------------------
% 5.40/2.03  #Ref     : 0
% 5.40/2.03  #Sup     : 1132
% 5.40/2.03  #Fact    : 0
% 5.40/2.03  #Define  : 0
% 5.40/2.03  #Split   : 4
% 5.40/2.03  #Chain   : 0
% 5.40/2.03  #Close   : 0
% 5.40/2.03  
% 5.40/2.03  Ordering : KBO
% 5.40/2.03  
% 5.40/2.03  Simplification rules
% 5.40/2.03  ----------------------
% 5.40/2.03  #Subsume      : 86
% 5.40/2.03  #Demod        : 1329
% 5.40/2.03  #Tautology    : 509
% 5.40/2.03  #SimpNegUnit  : 2
% 5.40/2.03  #BackRed      : 19
% 5.40/2.03  
% 5.40/2.03  #Partial instantiations: 0
% 5.40/2.03  #Strategies tried      : 1
% 5.40/2.03  
% 5.40/2.03  Timing (in seconds)
% 5.40/2.03  ----------------------
% 5.40/2.03  Preprocessing        : 0.33
% 5.40/2.03  Parsing              : 0.18
% 5.40/2.03  CNF conversion       : 0.02
% 5.40/2.03  Main loop            : 0.93
% 5.40/2.03  Inferencing          : 0.31
% 5.40/2.03  Reduction            : 0.35
% 5.40/2.03  Demodulation         : 0.26
% 5.40/2.03  BG Simplification    : 0.05
% 5.40/2.03  Subsumption          : 0.17
% 5.40/2.04  Abstraction          : 0.05
% 5.40/2.04  MUC search           : 0.00
% 5.40/2.04  Cooper               : 0.00
% 5.40/2.04  Total                : 1.30
% 5.40/2.04  Index Insertion      : 0.00
% 5.40/2.04  Index Deletion       : 0.00
% 5.40/2.04  Index Matching       : 0.00
% 5.40/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
