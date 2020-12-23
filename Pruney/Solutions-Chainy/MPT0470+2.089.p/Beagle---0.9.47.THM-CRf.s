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
% DateTime   : Thu Dec  3 09:59:13 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 181 expanded)
%              Number of leaves         :   37 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  114 ( 232 expanded)
%              Number of equality atoms :   59 ( 142 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_36,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_89,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_46,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_89,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_58,plain,(
    ! [A_51] :
      ( v1_relat_1(A_51)
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_58])).

tff(c_34,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(k5_relat_1(A_41,B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_116,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_128,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_116])).

tff(c_131,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_128])).

tff(c_231,plain,(
    ! [C_74,A_75,B_76] : k4_xboole_0(k2_zfmisc_1(C_74,A_75),k2_zfmisc_1(C_74,B_76)) = k2_zfmisc_1(C_74,k4_xboole_0(A_75,B_76)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_238,plain,(
    ! [C_74,B_76] : k2_zfmisc_1(C_74,k4_xboole_0(B_76,B_76)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_131])).

tff(c_247,plain,(
    ! [C_74] : k2_zfmisc_1(C_74,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_238])).

tff(c_293,plain,(
    ! [A_80,C_81,B_82] : k4_xboole_0(k2_zfmisc_1(A_80,C_81),k2_zfmisc_1(B_82,C_81)) = k2_zfmisc_1(k4_xboole_0(A_80,B_82),C_81) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [C_37,A_35,B_36] : k4_xboole_0(k2_zfmisc_1(C_37,A_35),k2_zfmisc_1(C_37,B_36)) = k2_zfmisc_1(C_37,k4_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_300,plain,(
    ! [B_82,C_81] : k2_zfmisc_1(k4_xboole_0(B_82,B_82),C_81) = k2_zfmisc_1(B_82,k4_xboole_0(C_81,C_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_28])).

tff(c_323,plain,(
    ! [C_81] : k2_zfmisc_1(k1_xboole_0,C_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_131,c_131,c_300])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_609,plain,(
    ! [A_102,B_103] :
      ( k1_relat_1(k5_relat_1(A_102,B_103)) = k1_relat_1(A_102)
      | ~ r1_tarski(k2_relat_1(A_102),k1_relat_1(B_103))
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_618,plain,(
    ! [B_103] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_103)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_103))
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_609])).

tff(c_625,plain,(
    ! [B_104] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_104)) = k1_xboole_0
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10,c_44,c_618])).

tff(c_36,plain,(
    ! [A_43] :
      ( k3_xboole_0(A_43,k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43))) = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_640,plain,(
    ! [B_104] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_104),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_104)))) = k5_relat_1(k1_xboole_0,B_104)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_104))
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_36])).

tff(c_655,plain,(
    ! [B_105] :
      ( k5_relat_1(k1_xboole_0,B_105) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_105))
      | ~ v1_relat_1(B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_323,c_640])).

tff(c_662,plain,(
    ! [B_42] :
      ( k5_relat_1(k1_xboole_0,B_42) = k1_xboole_0
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_655])).

tff(c_668,plain,(
    ! [B_106] :
      ( k5_relat_1(k1_xboole_0,B_106) = k1_xboole_0
      | ~ v1_relat_1(B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_662])).

tff(c_677,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_668])).

tff(c_684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_677])).

tff(c_685,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_722,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k3_xboole_0(A_114,B_115)) = k4_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_734,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_722])).

tff(c_737,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_734])).

tff(c_837,plain,(
    ! [A_127,C_128,B_129] : k4_xboole_0(k2_zfmisc_1(A_127,C_128),k2_zfmisc_1(B_129,C_128)) = k2_zfmisc_1(k4_xboole_0(A_127,B_129),C_128) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_844,plain,(
    ! [B_129,C_128] : k2_zfmisc_1(k4_xboole_0(B_129,B_129),C_128) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_737])).

tff(c_853,plain,(
    ! [C_128] : k2_zfmisc_1(k1_xboole_0,C_128) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_844])).

tff(c_899,plain,(
    ! [C_133,A_134,B_135] : k4_xboole_0(k2_zfmisc_1(C_133,A_134),k2_zfmisc_1(C_133,B_135)) = k2_zfmisc_1(C_133,k4_xboole_0(A_134,B_135)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_35,C_37,B_36] : k4_xboole_0(k2_zfmisc_1(A_35,C_37),k2_zfmisc_1(B_36,C_37)) = k2_zfmisc_1(k4_xboole_0(A_35,B_36),C_37) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_906,plain,(
    ! [C_133,B_135] : k2_zfmisc_1(k4_xboole_0(C_133,C_133),B_135) = k2_zfmisc_1(C_133,k4_xboole_0(B_135,B_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_26])).

tff(c_929,plain,(
    ! [C_133] : k2_zfmisc_1(C_133,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_737,c_737,c_906])).

tff(c_1323,plain,(
    ! [B_166,A_167] :
      ( k2_relat_1(k5_relat_1(B_166,A_167)) = k2_relat_1(A_167)
      | ~ r1_tarski(k1_relat_1(A_167),k2_relat_1(B_166))
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1329,plain,(
    ! [B_166] :
      ( k2_relat_1(k5_relat_1(B_166,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_166))
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1323])).

tff(c_1339,plain,(
    ! [B_168] :
      ( k2_relat_1(k5_relat_1(B_168,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10,c_42,c_1329])).

tff(c_1357,plain,(
    ! [B_168] :
      ( k3_xboole_0(k5_relat_1(B_168,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_168,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_168,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_168,k1_xboole_0))
      | ~ v1_relat_1(B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1339,c_36])).

tff(c_1374,plain,(
    ! [B_169] :
      ( k5_relat_1(B_169,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_169,k1_xboole_0))
      | ~ v1_relat_1(B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_929,c_1357])).

tff(c_1381,plain,(
    ! [A_41] :
      ( k5_relat_1(A_41,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_34,c_1374])).

tff(c_1387,plain,(
    ! [A_170] :
      ( k5_relat_1(A_170,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1381])).

tff(c_1396,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_1387])).

tff(c_1403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_1396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:34:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.55  
% 3.16/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.55  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.16/1.55  
% 3.16/1.55  %Foreground sorts:
% 3.16/1.55  
% 3.16/1.55  
% 3.16/1.55  %Background operators:
% 3.16/1.55  
% 3.16/1.55  
% 3.16/1.55  %Foreground operators:
% 3.16/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.55  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.55  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.16/1.55  
% 3.16/1.56  tff(f_96, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.16/1.56  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.16/1.56  tff(f_58, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.16/1.56  tff(f_64, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.16/1.56  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.16/1.56  tff(f_36, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.16/1.56  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.16/1.56  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.16/1.56  tff(f_52, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 3.16/1.56  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.16/1.56  tff(f_89, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.16/1.56  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.16/1.56  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.16/1.56  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.16/1.56  tff(c_46, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.56  tff(c_89, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 3.16/1.56  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.56  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.16/1.56  tff(c_58, plain, (![A_51]: (v1_relat_1(A_51) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.16/1.56  tff(c_62, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_58])).
% 3.16/1.57  tff(c_34, plain, (![A_41, B_42]: (v1_relat_1(k5_relat_1(A_41, B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.16/1.57  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.57  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.16/1.57  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.16/1.57  tff(c_116, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.16/1.57  tff(c_128, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_116])).
% 3.16/1.57  tff(c_131, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_128])).
% 3.16/1.57  tff(c_231, plain, (![C_74, A_75, B_76]: (k4_xboole_0(k2_zfmisc_1(C_74, A_75), k2_zfmisc_1(C_74, B_76))=k2_zfmisc_1(C_74, k4_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.57  tff(c_238, plain, (![C_74, B_76]: (k2_zfmisc_1(C_74, k4_xboole_0(B_76, B_76))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_231, c_131])).
% 3.16/1.57  tff(c_247, plain, (![C_74]: (k2_zfmisc_1(C_74, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_238])).
% 3.16/1.57  tff(c_293, plain, (![A_80, C_81, B_82]: (k4_xboole_0(k2_zfmisc_1(A_80, C_81), k2_zfmisc_1(B_82, C_81))=k2_zfmisc_1(k4_xboole_0(A_80, B_82), C_81))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.57  tff(c_28, plain, (![C_37, A_35, B_36]: (k4_xboole_0(k2_zfmisc_1(C_37, A_35), k2_zfmisc_1(C_37, B_36))=k2_zfmisc_1(C_37, k4_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.57  tff(c_300, plain, (![B_82, C_81]: (k2_zfmisc_1(k4_xboole_0(B_82, B_82), C_81)=k2_zfmisc_1(B_82, k4_xboole_0(C_81, C_81)))), inference(superposition, [status(thm), theory('equality')], [c_293, c_28])).
% 3.16/1.57  tff(c_323, plain, (![C_81]: (k2_zfmisc_1(k1_xboole_0, C_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_247, c_131, c_131, c_300])).
% 3.16/1.57  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.16/1.57  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.16/1.57  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.16/1.57  tff(c_609, plain, (![A_102, B_103]: (k1_relat_1(k5_relat_1(A_102, B_103))=k1_relat_1(A_102) | ~r1_tarski(k2_relat_1(A_102), k1_relat_1(B_103)) | ~v1_relat_1(B_103) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.57  tff(c_618, plain, (![B_103]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_103))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_103)) | ~v1_relat_1(B_103) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_42, c_609])).
% 3.16/1.57  tff(c_625, plain, (![B_104]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_104))=k1_xboole_0 | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10, c_44, c_618])).
% 3.16/1.57  tff(c_36, plain, (![A_43]: (k3_xboole_0(A_43, k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43)))=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.16/1.57  tff(c_640, plain, (![B_104]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_104), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_104))))=k5_relat_1(k1_xboole_0, B_104) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_104)) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_625, c_36])).
% 3.16/1.57  tff(c_655, plain, (![B_105]: (k5_relat_1(k1_xboole_0, B_105)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_105)) | ~v1_relat_1(B_105))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_323, c_640])).
% 3.16/1.57  tff(c_662, plain, (![B_42]: (k5_relat_1(k1_xboole_0, B_42)=k1_xboole_0 | ~v1_relat_1(B_42) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_655])).
% 3.16/1.57  tff(c_668, plain, (![B_106]: (k5_relat_1(k1_xboole_0, B_106)=k1_xboole_0 | ~v1_relat_1(B_106))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_662])).
% 3.16/1.57  tff(c_677, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_668])).
% 3.16/1.57  tff(c_684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_677])).
% 3.16/1.57  tff(c_685, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 3.16/1.57  tff(c_722, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k3_xboole_0(A_114, B_115))=k4_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.16/1.57  tff(c_734, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_722])).
% 3.16/1.57  tff(c_737, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_734])).
% 3.16/1.57  tff(c_837, plain, (![A_127, C_128, B_129]: (k4_xboole_0(k2_zfmisc_1(A_127, C_128), k2_zfmisc_1(B_129, C_128))=k2_zfmisc_1(k4_xboole_0(A_127, B_129), C_128))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.57  tff(c_844, plain, (![B_129, C_128]: (k2_zfmisc_1(k4_xboole_0(B_129, B_129), C_128)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_837, c_737])).
% 3.16/1.57  tff(c_853, plain, (![C_128]: (k2_zfmisc_1(k1_xboole_0, C_128)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_737, c_844])).
% 3.16/1.57  tff(c_899, plain, (![C_133, A_134, B_135]: (k4_xboole_0(k2_zfmisc_1(C_133, A_134), k2_zfmisc_1(C_133, B_135))=k2_zfmisc_1(C_133, k4_xboole_0(A_134, B_135)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.57  tff(c_26, plain, (![A_35, C_37, B_36]: (k4_xboole_0(k2_zfmisc_1(A_35, C_37), k2_zfmisc_1(B_36, C_37))=k2_zfmisc_1(k4_xboole_0(A_35, B_36), C_37))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.57  tff(c_906, plain, (![C_133, B_135]: (k2_zfmisc_1(k4_xboole_0(C_133, C_133), B_135)=k2_zfmisc_1(C_133, k4_xboole_0(B_135, B_135)))), inference(superposition, [status(thm), theory('equality')], [c_899, c_26])).
% 3.16/1.57  tff(c_929, plain, (![C_133]: (k2_zfmisc_1(C_133, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_853, c_737, c_737, c_906])).
% 3.16/1.57  tff(c_1323, plain, (![B_166, A_167]: (k2_relat_1(k5_relat_1(B_166, A_167))=k2_relat_1(A_167) | ~r1_tarski(k1_relat_1(A_167), k2_relat_1(B_166)) | ~v1_relat_1(B_166) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.16/1.57  tff(c_1329, plain, (![B_166]: (k2_relat_1(k5_relat_1(B_166, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_166)) | ~v1_relat_1(B_166) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1323])).
% 3.16/1.57  tff(c_1339, plain, (![B_168]: (k2_relat_1(k5_relat_1(B_168, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_168))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10, c_42, c_1329])).
% 3.16/1.57  tff(c_1357, plain, (![B_168]: (k3_xboole_0(k5_relat_1(B_168, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_168, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_168, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_168, k1_xboole_0)) | ~v1_relat_1(B_168))), inference(superposition, [status(thm), theory('equality')], [c_1339, c_36])).
% 3.16/1.57  tff(c_1374, plain, (![B_169]: (k5_relat_1(B_169, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_169, k1_xboole_0)) | ~v1_relat_1(B_169))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_929, c_1357])).
% 3.16/1.57  tff(c_1381, plain, (![A_41]: (k5_relat_1(A_41, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_34, c_1374])).
% 3.16/1.57  tff(c_1387, plain, (![A_170]: (k5_relat_1(A_170, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_170))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1381])).
% 3.16/1.57  tff(c_1396, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_1387])).
% 3.16/1.57  tff(c_1403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_1396])).
% 3.16/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.57  
% 3.16/1.57  Inference rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Ref     : 0
% 3.16/1.57  #Sup     : 307
% 3.16/1.57  #Fact    : 0
% 3.16/1.57  #Define  : 0
% 3.16/1.57  #Split   : 1
% 3.16/1.57  #Chain   : 0
% 3.16/1.57  #Close   : 0
% 3.16/1.57  
% 3.16/1.57  Ordering : KBO
% 3.16/1.57  
% 3.16/1.57  Simplification rules
% 3.16/1.57  ----------------------
% 3.16/1.57  #Subsume      : 5
% 3.16/1.57  #Demod        : 348
% 3.16/1.57  #Tautology    : 222
% 3.16/1.57  #SimpNegUnit  : 2
% 3.16/1.57  #BackRed      : 6
% 3.16/1.57  
% 3.16/1.57  #Partial instantiations: 0
% 3.16/1.57  #Strategies tried      : 1
% 3.16/1.57  
% 3.16/1.57  Timing (in seconds)
% 3.16/1.57  ----------------------
% 3.16/1.57  Preprocessing        : 0.35
% 3.16/1.57  Parsing              : 0.19
% 3.16/1.57  CNF conversion       : 0.02
% 3.16/1.57  Main loop            : 0.41
% 3.16/1.57  Inferencing          : 0.16
% 3.16/1.57  Reduction            : 0.14
% 3.16/1.57  Demodulation         : 0.11
% 3.16/1.57  BG Simplification    : 0.02
% 3.16/1.57  Subsumption          : 0.06
% 3.16/1.57  Abstraction          : 0.03
% 3.16/1.57  MUC search           : 0.00
% 3.16/1.57  Cooper               : 0.00
% 3.16/1.57  Total                : 0.79
% 3.16/1.57  Index Insertion      : 0.00
% 3.16/1.57  Index Deletion       : 0.00
% 3.16/1.57  Index Matching       : 0.00
% 3.16/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
