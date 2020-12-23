%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:06 EST 2020

% Result     : Theorem 10.74s
% Output     : CNFRefutation 10.96s
% Verified   : 
% Statistics : Number of formulae       :  129 (1290 expanded)
%              Number of leaves         :   39 ( 465 expanded)
%              Depth                    :   23
%              Number of atoms          :  207 (2030 expanded)
%              Number of equality atoms :   92 ( 922 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_36,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_60,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_103,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_89,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_84,plain,(
    ! [A_48] :
      ( v1_relat_1(A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_84])).

tff(c_40,plain,(
    ! [A_28,B_29] :
      ( v1_relat_1(k5_relat_1(A_28,B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [A_24] : k1_setfam_1(k1_tarski(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_106,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = k1_setfam_1(k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_106])).

tff(c_118,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_115])).

tff(c_148,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_157,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_148])).

tff(c_163,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_157])).

tff(c_332,plain,(
    ! [C_78,A_79,B_80] : k4_xboole_0(k2_zfmisc_1(C_78,A_79),k2_zfmisc_1(C_78,B_80)) = k2_zfmisc_1(C_78,k4_xboole_0(A_79,B_80)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_339,plain,(
    ! [C_78,B_80] : k2_zfmisc_1(C_78,k4_xboole_0(B_80,B_80)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_163])).

tff(c_348,plain,(
    ! [C_78] : k2_zfmisc_1(C_78,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_339])).

tff(c_424,plain,(
    ! [A_87,C_88,B_89] : k4_xboole_0(k2_zfmisc_1(A_87,C_88),k2_zfmisc_1(B_89,C_88)) = k2_zfmisc_1(k4_xboole_0(A_87,B_89),C_88) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [C_23,A_21,B_22] : k4_xboole_0(k2_zfmisc_1(C_23,A_21),k2_zfmisc_1(C_23,B_22)) = k2_zfmisc_1(C_23,k4_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_431,plain,(
    ! [B_89,C_88] : k2_zfmisc_1(k4_xboole_0(B_89,B_89),C_88) = k2_zfmisc_1(B_89,k4_xboole_0(C_88,C_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_32])).

tff(c_454,plain,(
    ! [C_88] : k2_zfmisc_1(k1_xboole_0,C_88) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_163,c_163,c_431])).

tff(c_14,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_754,plain,(
    ! [A_102,B_103] :
      ( k1_relat_1(k5_relat_1(A_102,B_103)) = k1_relat_1(A_102)
      | ~ r1_tarski(k2_relat_1(A_102),k1_relat_1(B_103))
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_763,plain,(
    ! [B_103] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_103)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_103))
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_754])).

tff(c_770,plain,(
    ! [B_104] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_104)) = k1_xboole_0
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_14,c_52,c_763])).

tff(c_42,plain,(
    ! [A_30] :
      ( k3_xboole_0(A_30,k2_zfmisc_1(k1_relat_1(A_30),k2_relat_1(A_30))) = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_782,plain,(
    ! [B_104] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_104),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_104)))) = k5_relat_1(k1_xboole_0,B_104)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_104))
      | ~ v1_relat_1(B_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_42])).

tff(c_790,plain,(
    ! [B_105] :
      ( k5_relat_1(k1_xboole_0,B_105) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_105))
      | ~ v1_relat_1(B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_454,c_782])).

tff(c_794,plain,(
    ! [B_29] :
      ( k5_relat_1(k1_xboole_0,B_29) = k1_xboole_0
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_790])).

tff(c_798,plain,(
    ! [B_106] :
      ( k5_relat_1(k1_xboole_0,B_106) = k1_xboole_0
      | ~ v1_relat_1(B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_794])).

tff(c_807,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_798])).

tff(c_813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_807])).

tff(c_814,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_845,plain,(
    ! [A_111,B_112] : k1_setfam_1(k2_tarski(A_111,B_112)) = k3_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_854,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = k1_setfam_1(k1_tarski(A_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_845])).

tff(c_857,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_854])).

tff(c_877,plain,(
    ! [A_114,B_115] : k5_xboole_0(A_114,k3_xboole_0(A_114,B_115)) = k4_xboole_0(A_114,B_115) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_886,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k4_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_877])).

tff(c_892,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_886])).

tff(c_1091,plain,(
    ! [A_139,C_140,B_141] : k4_xboole_0(k2_zfmisc_1(A_139,C_140),k2_zfmisc_1(B_141,C_140)) = k2_zfmisc_1(k4_xboole_0(A_139,B_141),C_140) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1102,plain,(
    ! [B_141,C_140] : k2_zfmisc_1(k4_xboole_0(B_141,B_141),C_140) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_892])).

tff(c_1116,plain,(
    ! [C_140] : k2_zfmisc_1(k1_xboole_0,C_140) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_1102])).

tff(c_1623,plain,(
    ! [A_164,B_165] :
      ( k1_relat_1(k5_relat_1(A_164,B_165)) = k1_relat_1(A_164)
      | ~ r1_tarski(k2_relat_1(A_164),k1_relat_1(B_165))
      | ~ v1_relat_1(B_165)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1632,plain,(
    ! [B_165] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_165)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_165))
      | ~ v1_relat_1(B_165)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1623])).

tff(c_1639,plain,(
    ! [B_166] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_166)) = k1_xboole_0
      | ~ v1_relat_1(B_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_14,c_52,c_1632])).

tff(c_1651,plain,(
    ! [B_166] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_166),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_166)))) = k5_relat_1(k1_xboole_0,B_166)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_166))
      | ~ v1_relat_1(B_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1639,c_42])).

tff(c_1664,plain,(
    ! [B_167] :
      ( k5_relat_1(k1_xboole_0,B_167) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_167))
      | ~ v1_relat_1(B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1116,c_1651])).

tff(c_1668,plain,(
    ! [B_29] :
      ( k5_relat_1(k1_xboole_0,B_29) = k1_xboole_0
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_1664])).

tff(c_1677,plain,(
    ! [B_168] :
      ( k5_relat_1(k1_xboole_0,B_168) = k1_xboole_0
      | ~ v1_relat_1(B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1668])).

tff(c_1688,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_88,c_1677])).

tff(c_815,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1691,plain,(
    ! [A_169,B_170,C_171] :
      ( k5_relat_1(k5_relat_1(A_169,B_170),C_171) = k5_relat_1(A_169,k5_relat_1(B_170,C_171))
      | ~ v1_relat_1(C_171)
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1720,plain,(
    ! [C_171] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_171)) = k5_relat_1(k1_xboole_0,C_171)
      | ~ v1_relat_1(C_171)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_1691])).

tff(c_1728,plain,(
    ! [C_171] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_171)) = k5_relat_1(k1_xboole_0,C_171)
      | ~ v1_relat_1(C_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_56,c_1720])).

tff(c_48,plain,(
    ! [A_37,B_41,C_43] :
      ( k5_relat_1(k5_relat_1(A_37,B_41),C_43) = k5_relat_1(A_37,k5_relat_1(B_41,C_43))
      | ~ v1_relat_1(C_43)
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1732,plain,(
    ! [C_43] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_43)) = k5_relat_1(k1_xboole_0,C_43)
      | ~ v1_relat_1(C_43)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_48])).

tff(c_1879,plain,(
    ! [C_176] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_176)) = k5_relat_1(k1_xboole_0,C_176)
      | ~ v1_relat_1(C_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_88,c_1732])).

tff(c_2113,plain,(
    ! [C_182] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,C_182)) = k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_182))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_182))
      | ~ v1_relat_1(C_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_1879])).

tff(c_2117,plain,(
    ! [B_29] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,B_29)) = k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_2113])).

tff(c_3134,plain,(
    ! [B_208] :
      ( k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,B_208)) = k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',B_208))
      | ~ v1_relat_1(B_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2117])).

tff(c_3222,plain,
    ( k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',k1_xboole_0)) = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_3134])).

tff(c_3243,plain,(
    k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1688,c_3222])).

tff(c_980,plain,(
    ! [A_127,B_128] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_127,B_128)),k2_relat_1(B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_988,plain,(
    ! [A_127] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_127,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_980])).

tff(c_1007,plain,(
    ! [A_129] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_129,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_988])).

tff(c_925,plain,(
    ! [B_120,A_121] :
      ( B_120 = A_121
      | ~ r1_tarski(B_120,A_121)
      | ~ r1_tarski(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_934,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_925])).

tff(c_1013,plain,(
    ! [A_129] :
      ( k2_relat_1(k5_relat_1(A_129,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_129) ) ),
    inference(resolution,[status(thm)],[c_1007,c_934])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3542,plain,(
    ! [A_210,B_211] :
      ( k2_relat_1(k5_relat_1(A_210,B_211)) = k2_relat_1(B_211)
      | ~ r1_tarski(k2_relat_1(B_211),k2_relat_1(k5_relat_1(A_210,B_211)))
      | ~ v1_relat_1(B_211)
      | ~ v1_relat_1(A_210) ) ),
    inference(resolution,[status(thm)],[c_980,c_4])).

tff(c_3566,plain,(
    ! [C_171] :
      ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_171))) = k2_relat_1(k5_relat_1('#skF_1',C_171))
      | ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_1',C_171)),k2_relat_1(k5_relat_1(k1_xboole_0,C_171)))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_171))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(C_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_3542])).

tff(c_21162,plain,(
    ! [C_451] :
      ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',C_451))) = k2_relat_1(k5_relat_1('#skF_1',C_451))
      | ~ r1_tarski(k2_relat_1(k5_relat_1('#skF_1',C_451)),k2_relat_1(k5_relat_1(k1_xboole_0,C_451)))
      | ~ v1_relat_1(k5_relat_1('#skF_1',C_451))
      | ~ v1_relat_1(C_451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3566])).

tff(c_21214,plain,
    ( k2_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1('#skF_1',k1_xboole_0))) = k2_relat_1(k5_relat_1('#skF_1',k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1013,c_21162])).

tff(c_21232,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_88,c_14,c_1688,c_50,c_3243,c_21214])).

tff(c_21237,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_21232])).

tff(c_21240,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_21237])).

tff(c_21244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_88,c_21240])).

tff(c_21246,plain,(
    v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_21232])).

tff(c_1072,plain,(
    ! [C_136,A_137,B_138] : k4_xboole_0(k2_zfmisc_1(C_136,A_137),k2_zfmisc_1(C_136,B_138)) = k2_zfmisc_1(C_136,k4_xboole_0(A_137,B_138)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1079,plain,(
    ! [C_136,B_138] : k2_zfmisc_1(C_136,k4_xboole_0(B_138,B_138)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1072,c_892])).

tff(c_1088,plain,(
    ! [C_136] : k2_zfmisc_1(C_136,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_1079])).

tff(c_21245,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_21232])).

tff(c_21379,plain,
    ( k3_xboole_0(k5_relat_1('#skF_1',k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)),k1_xboole_0)) = k5_relat_1('#skF_1',k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1('#skF_1',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_21245,c_42])).

tff(c_21449,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21246,c_12,c_1088,c_21379])).

tff(c_21451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_814,c_21449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.74/4.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/4.46  
% 10.74/4.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.74/4.46  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 10.74/4.46  
% 10.74/4.46  %Foreground sorts:
% 10.74/4.46  
% 10.74/4.46  
% 10.74/4.46  %Background operators:
% 10.74/4.46  
% 10.74/4.46  
% 10.74/4.46  %Foreground operators:
% 10.74/4.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.74/4.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.74/4.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.74/4.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.74/4.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.74/4.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.74/4.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.74/4.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.74/4.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.74/4.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.74/4.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.74/4.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.74/4.46  tff('#skF_1', type, '#skF_1': $i).
% 10.74/4.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.74/4.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.74/4.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.74/4.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.74/4.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.74/4.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.74/4.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.74/4.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.74/4.46  
% 10.96/4.48  tff(f_110, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 10.96/4.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.96/4.48  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 10.96/4.48  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 10.96/4.48  tff(f_36, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 10.96/4.48  tff(f_40, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 10.96/4.48  tff(f_58, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 10.96/4.48  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 10.96/4.48  tff(f_60, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.96/4.48  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 10.96/4.48  tff(f_56, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 10.96/4.48  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.96/4.48  tff(f_103, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 10.96/4.48  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 10.96/4.48  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 10.96/4.48  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 10.96/4.48  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 10.96/4.48  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.96/4.48  tff(c_54, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.96/4.48  tff(c_89, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 10.96/4.48  tff(c_56, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.96/4.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.96/4.48  tff(c_84, plain, (![A_48]: (v1_relat_1(A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.96/4.48  tff(c_88, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_84])).
% 10.96/4.48  tff(c_40, plain, (![A_28, B_29]: (v1_relat_1(k5_relat_1(A_28, B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.96/4.48  tff(c_12, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.96/4.48  tff(c_16, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.96/4.48  tff(c_34, plain, (![A_24]: (k1_setfam_1(k1_tarski(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.96/4.48  tff(c_18, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.96/4.48  tff(c_106, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.96/4.48  tff(c_115, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=k1_setfam_1(k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_106])).
% 10.96/4.48  tff(c_118, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_115])).
% 10.96/4.48  tff(c_148, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.96/4.48  tff(c_157, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_118, c_148])).
% 10.96/4.48  tff(c_163, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_157])).
% 10.96/4.48  tff(c_332, plain, (![C_78, A_79, B_80]: (k4_xboole_0(k2_zfmisc_1(C_78, A_79), k2_zfmisc_1(C_78, B_80))=k2_zfmisc_1(C_78, k4_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.96/4.48  tff(c_339, plain, (![C_78, B_80]: (k2_zfmisc_1(C_78, k4_xboole_0(B_80, B_80))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_332, c_163])).
% 10.96/4.48  tff(c_348, plain, (![C_78]: (k2_zfmisc_1(C_78, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_339])).
% 10.96/4.48  tff(c_424, plain, (![A_87, C_88, B_89]: (k4_xboole_0(k2_zfmisc_1(A_87, C_88), k2_zfmisc_1(B_89, C_88))=k2_zfmisc_1(k4_xboole_0(A_87, B_89), C_88))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.96/4.48  tff(c_32, plain, (![C_23, A_21, B_22]: (k4_xboole_0(k2_zfmisc_1(C_23, A_21), k2_zfmisc_1(C_23, B_22))=k2_zfmisc_1(C_23, k4_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.96/4.48  tff(c_431, plain, (![B_89, C_88]: (k2_zfmisc_1(k4_xboole_0(B_89, B_89), C_88)=k2_zfmisc_1(B_89, k4_xboole_0(C_88, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_424, c_32])).
% 10.96/4.48  tff(c_454, plain, (![C_88]: (k2_zfmisc_1(k1_xboole_0, C_88)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_348, c_163, c_163, c_431])).
% 10.96/4.48  tff(c_14, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.96/4.48  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.96/4.48  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.96/4.48  tff(c_754, plain, (![A_102, B_103]: (k1_relat_1(k5_relat_1(A_102, B_103))=k1_relat_1(A_102) | ~r1_tarski(k2_relat_1(A_102), k1_relat_1(B_103)) | ~v1_relat_1(B_103) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.96/4.48  tff(c_763, plain, (![B_103]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_103))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_103)) | ~v1_relat_1(B_103) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_754])).
% 10.96/4.48  tff(c_770, plain, (![B_104]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_104))=k1_xboole_0 | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_14, c_52, c_763])).
% 10.96/4.48  tff(c_42, plain, (![A_30]: (k3_xboole_0(A_30, k2_zfmisc_1(k1_relat_1(A_30), k2_relat_1(A_30)))=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.96/4.48  tff(c_782, plain, (![B_104]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_104), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_104))))=k5_relat_1(k1_xboole_0, B_104) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_104)) | ~v1_relat_1(B_104))), inference(superposition, [status(thm), theory('equality')], [c_770, c_42])).
% 10.96/4.48  tff(c_790, plain, (![B_105]: (k5_relat_1(k1_xboole_0, B_105)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_105)) | ~v1_relat_1(B_105))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_454, c_782])).
% 10.96/4.48  tff(c_794, plain, (![B_29]: (k5_relat_1(k1_xboole_0, B_29)=k1_xboole_0 | ~v1_relat_1(B_29) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_790])).
% 10.96/4.48  tff(c_798, plain, (![B_106]: (k5_relat_1(k1_xboole_0, B_106)=k1_xboole_0 | ~v1_relat_1(B_106))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_794])).
% 10.96/4.48  tff(c_807, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_798])).
% 10.96/4.48  tff(c_813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_807])).
% 10.96/4.48  tff(c_814, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 10.96/4.48  tff(c_845, plain, (![A_111, B_112]: (k1_setfam_1(k2_tarski(A_111, B_112))=k3_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.96/4.48  tff(c_854, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=k1_setfam_1(k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_845])).
% 10.96/4.48  tff(c_857, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_854])).
% 10.96/4.48  tff(c_877, plain, (![A_114, B_115]: (k5_xboole_0(A_114, k3_xboole_0(A_114, B_115))=k4_xboole_0(A_114, B_115))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.96/4.48  tff(c_886, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k4_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_857, c_877])).
% 10.96/4.48  tff(c_892, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_886])).
% 10.96/4.48  tff(c_1091, plain, (![A_139, C_140, B_141]: (k4_xboole_0(k2_zfmisc_1(A_139, C_140), k2_zfmisc_1(B_141, C_140))=k2_zfmisc_1(k4_xboole_0(A_139, B_141), C_140))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.96/4.48  tff(c_1102, plain, (![B_141, C_140]: (k2_zfmisc_1(k4_xboole_0(B_141, B_141), C_140)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1091, c_892])).
% 10.96/4.48  tff(c_1116, plain, (![C_140]: (k2_zfmisc_1(k1_xboole_0, C_140)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_892, c_1102])).
% 10.96/4.48  tff(c_1623, plain, (![A_164, B_165]: (k1_relat_1(k5_relat_1(A_164, B_165))=k1_relat_1(A_164) | ~r1_tarski(k2_relat_1(A_164), k1_relat_1(B_165)) | ~v1_relat_1(B_165) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.96/4.48  tff(c_1632, plain, (![B_165]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_165))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_165)) | ~v1_relat_1(B_165) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1623])).
% 10.96/4.48  tff(c_1639, plain, (![B_166]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_166))=k1_xboole_0 | ~v1_relat_1(B_166))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_14, c_52, c_1632])).
% 10.96/4.48  tff(c_1651, plain, (![B_166]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_166), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_166))))=k5_relat_1(k1_xboole_0, B_166) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_166)) | ~v1_relat_1(B_166))), inference(superposition, [status(thm), theory('equality')], [c_1639, c_42])).
% 10.96/4.48  tff(c_1664, plain, (![B_167]: (k5_relat_1(k1_xboole_0, B_167)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_167)) | ~v1_relat_1(B_167))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1116, c_1651])).
% 10.96/4.48  tff(c_1668, plain, (![B_29]: (k5_relat_1(k1_xboole_0, B_29)=k1_xboole_0 | ~v1_relat_1(B_29) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_1664])).
% 10.96/4.48  tff(c_1677, plain, (![B_168]: (k5_relat_1(k1_xboole_0, B_168)=k1_xboole_0 | ~v1_relat_1(B_168))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1668])).
% 10.96/4.48  tff(c_1688, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_88, c_1677])).
% 10.96/4.48  tff(c_815, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 10.96/4.48  tff(c_1691, plain, (![A_169, B_170, C_171]: (k5_relat_1(k5_relat_1(A_169, B_170), C_171)=k5_relat_1(A_169, k5_relat_1(B_170, C_171)) | ~v1_relat_1(C_171) | ~v1_relat_1(B_170) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.96/4.48  tff(c_1720, plain, (![C_171]: (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_171))=k5_relat_1(k1_xboole_0, C_171) | ~v1_relat_1(C_171) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_815, c_1691])).
% 10.96/4.48  tff(c_1728, plain, (![C_171]: (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_171))=k5_relat_1(k1_xboole_0, C_171) | ~v1_relat_1(C_171))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_56, c_1720])).
% 10.96/4.48  tff(c_48, plain, (![A_37, B_41, C_43]: (k5_relat_1(k5_relat_1(A_37, B_41), C_43)=k5_relat_1(A_37, k5_relat_1(B_41, C_43)) | ~v1_relat_1(C_43) | ~v1_relat_1(B_41) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_100])).
% 10.96/4.48  tff(c_1732, plain, (![C_43]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_43))=k5_relat_1(k1_xboole_0, C_43) | ~v1_relat_1(C_43) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1688, c_48])).
% 10.96/4.48  tff(c_1879, plain, (![C_176]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_176))=k5_relat_1(k1_xboole_0, C_176) | ~v1_relat_1(C_176))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_88, c_1732])).
% 10.96/4.48  tff(c_2113, plain, (![C_182]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, C_182))=k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_182)) | ~v1_relat_1(k5_relat_1('#skF_1', C_182)) | ~v1_relat_1(C_182))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_1879])).
% 10.96/4.48  tff(c_2117, plain, (![B_29]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, B_29))=k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_40, c_2113])).
% 10.96/4.48  tff(c_3134, plain, (![B_208]: (k5_relat_1(k1_xboole_0, k5_relat_1(k1_xboole_0, B_208))=k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', B_208)) | ~v1_relat_1(B_208))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2117])).
% 10.96/4.48  tff(c_3222, plain, (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', k1_xboole_0))=k5_relat_1(k1_xboole_0, k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1688, c_3134])).
% 10.96/4.48  tff(c_3243, plain, (k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1688, c_3222])).
% 10.96/4.48  tff(c_980, plain, (![A_127, B_128]: (r1_tarski(k2_relat_1(k5_relat_1(A_127, B_128)), k2_relat_1(B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.96/4.48  tff(c_988, plain, (![A_127]: (r1_tarski(k2_relat_1(k5_relat_1(A_127, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_50, c_980])).
% 10.96/4.48  tff(c_1007, plain, (![A_129]: (r1_tarski(k2_relat_1(k5_relat_1(A_129, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_988])).
% 10.96/4.48  tff(c_925, plain, (![B_120, A_121]: (B_120=A_121 | ~r1_tarski(B_120, A_121) | ~r1_tarski(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.96/4.48  tff(c_934, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_925])).
% 10.96/4.48  tff(c_1013, plain, (![A_129]: (k2_relat_1(k5_relat_1(A_129, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_129))), inference(resolution, [status(thm)], [c_1007, c_934])).
% 10.96/4.48  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.96/4.48  tff(c_3542, plain, (![A_210, B_211]: (k2_relat_1(k5_relat_1(A_210, B_211))=k2_relat_1(B_211) | ~r1_tarski(k2_relat_1(B_211), k2_relat_1(k5_relat_1(A_210, B_211))) | ~v1_relat_1(B_211) | ~v1_relat_1(A_210))), inference(resolution, [status(thm)], [c_980, c_4])).
% 10.96/4.48  tff(c_3566, plain, (![C_171]: (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_171)))=k2_relat_1(k5_relat_1('#skF_1', C_171)) | ~r1_tarski(k2_relat_1(k5_relat_1('#skF_1', C_171)), k2_relat_1(k5_relat_1(k1_xboole_0, C_171))) | ~v1_relat_1(k5_relat_1('#skF_1', C_171)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(C_171))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_3542])).
% 10.96/4.48  tff(c_21162, plain, (![C_451]: (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', C_451)))=k2_relat_1(k5_relat_1('#skF_1', C_451)) | ~r1_tarski(k2_relat_1(k5_relat_1('#skF_1', C_451)), k2_relat_1(k5_relat_1(k1_xboole_0, C_451))) | ~v1_relat_1(k5_relat_1('#skF_1', C_451)) | ~v1_relat_1(C_451))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3566])).
% 10.96/4.48  tff(c_21214, plain, (k2_relat_1(k5_relat_1(k1_xboole_0, k5_relat_1('#skF_1', k1_xboole_0)))=k2_relat_1(k5_relat_1('#skF_1', k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, k1_xboole_0))) | ~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1013, c_21162])).
% 10.96/4.48  tff(c_21232, plain, (k2_relat_1(k5_relat_1('#skF_1', k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_88, c_14, c_1688, c_50, c_3243, c_21214])).
% 10.96/4.48  tff(c_21237, plain, (~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_21232])).
% 10.96/4.48  tff(c_21240, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_40, c_21237])).
% 10.96/4.48  tff(c_21244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_88, c_21240])).
% 10.96/4.48  tff(c_21246, plain, (v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(splitRight, [status(thm)], [c_21232])).
% 10.96/4.48  tff(c_1072, plain, (![C_136, A_137, B_138]: (k4_xboole_0(k2_zfmisc_1(C_136, A_137), k2_zfmisc_1(C_136, B_138))=k2_zfmisc_1(C_136, k4_xboole_0(A_137, B_138)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.96/4.48  tff(c_1079, plain, (![C_136, B_138]: (k2_zfmisc_1(C_136, k4_xboole_0(B_138, B_138))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1072, c_892])).
% 10.96/4.48  tff(c_1088, plain, (![C_136]: (k2_zfmisc_1(C_136, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_892, c_1079])).
% 10.96/4.48  tff(c_21245, plain, (k2_relat_1(k5_relat_1('#skF_1', k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_21232])).
% 10.96/4.48  tff(c_21379, plain, (k3_xboole_0(k5_relat_1('#skF_1', k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1('#skF_1', k1_xboole_0)), k1_xboole_0))=k5_relat_1('#skF_1', k1_xboole_0) | ~v1_relat_1(k5_relat_1('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_21245, c_42])).
% 10.96/4.48  tff(c_21449, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_21246, c_12, c_1088, c_21379])).
% 10.96/4.48  tff(c_21451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_814, c_21449])).
% 10.96/4.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.96/4.48  
% 10.96/4.48  Inference rules
% 10.96/4.48  ----------------------
% 10.96/4.48  #Ref     : 0
% 10.96/4.48  #Sup     : 5181
% 10.96/4.48  #Fact    : 0
% 10.96/4.48  #Define  : 0
% 10.96/4.48  #Split   : 3
% 10.96/4.48  #Chain   : 0
% 10.96/4.48  #Close   : 0
% 10.96/4.48  
% 10.96/4.48  Ordering : KBO
% 10.96/4.48  
% 10.96/4.48  Simplification rules
% 10.96/4.48  ----------------------
% 10.96/4.48  #Subsume      : 682
% 10.96/4.48  #Demod        : 6670
% 10.96/4.48  #Tautology    : 2162
% 10.96/4.48  #SimpNegUnit  : 2
% 10.96/4.48  #BackRed      : 4
% 10.96/4.48  
% 10.96/4.48  #Partial instantiations: 0
% 10.96/4.48  #Strategies tried      : 1
% 10.96/4.48  
% 10.96/4.48  Timing (in seconds)
% 10.96/4.48  ----------------------
% 10.96/4.49  Preprocessing        : 0.32
% 10.96/4.49  Parsing              : 0.17
% 10.96/4.49  CNF conversion       : 0.02
% 10.96/4.49  Main loop            : 3.31
% 10.96/4.49  Inferencing          : 0.83
% 10.96/4.49  Reduction            : 1.47
% 10.96/4.49  Demodulation         : 1.20
% 10.96/4.49  BG Simplification    : 0.13
% 10.96/4.49  Subsumption          : 0.72
% 10.96/4.49  Abstraction          : 0.22
% 10.96/4.49  MUC search           : 0.00
% 10.96/4.49  Cooper               : 0.00
% 10.96/4.49  Total                : 3.67
% 10.96/4.49  Index Insertion      : 0.00
% 10.96/4.49  Index Deletion       : 0.00
% 10.96/4.49  Index Matching       : 0.00
% 10.96/4.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
