%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:41 EST 2020

% Result     : Theorem 47.33s
% Output     : CNFRefutation 47.44s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 454 expanded)
%              Number of leaves         :   26 ( 163 expanded)
%              Depth                    :   17
%              Number of atoms          :  148 ( 803 expanded)
%              Number of equality atoms :   47 ( 278 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,k3_xboole_0(B_9,C_10))
      | ~ r1_tarski(A_8,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_254,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_464,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = A_72
      | ~ r1_tarski(A_72,k3_xboole_0(A_72,B_73)) ) ),
    inference(resolution,[status(thm)],[c_8,c_254])).

tff(c_468,plain,(
    ! [B_9,C_10] :
      ( k3_xboole_0(B_9,C_10) = B_9
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(B_9,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_464])).

tff(c_481,plain,(
    ! [B_74,C_75] :
      ( k3_xboole_0(B_74,C_75) = B_74
      | ~ r1_tarski(B_74,C_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_468])).

tff(c_527,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_481])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_526,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_481])).

tff(c_14,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_85,plain,(
    ! [B_34,A_35] : k1_setfam_1(k2_tarski(B_34,A_35)) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_70])).

tff(c_16,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_91,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_16])).

tff(c_117,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_16])).

tff(c_132,plain,(
    ! [B_37,A_38] : r1_tarski(k3_xboole_0(B_37,A_38),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_8])).

tff(c_910,plain,(
    ! [B_85,A_86] : k3_xboole_0(k3_xboole_0(B_85,A_86),A_86) = k3_xboole_0(B_85,A_86) ),
    inference(resolution,[status(thm)],[c_132,c_481])).

tff(c_2329,plain,(
    ! [A_106,B_107] : k3_xboole_0(k3_xboole_0(A_106,B_107),A_106) = k3_xboole_0(B_107,A_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_910])).

tff(c_2502,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_2329])).

tff(c_2563,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_2502])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( k3_xboole_0(k1_relat_1(B_21),A_20) = k1_relat_1(k7_relat_1(B_21,A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2662,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2563,c_24])).

tff(c_2714,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2662])).

tff(c_528,plain,(
    ! [B_76] : k3_xboole_0(B_76,B_76) = B_76 ),
    inference(resolution,[status(thm)],[c_6,c_481])).

tff(c_5966,plain,(
    ! [B_171] :
      ( k1_relat_1(k7_relat_1(B_171,k1_relat_1(B_171))) = k1_relat_1(B_171)
      | ~ v1_relat_1(B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_528])).

tff(c_6013,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2714,c_5966])).

tff(c_6022,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2714,c_6013])).

tff(c_168522,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6022])).

tff(c_168525,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_168522])).

tff(c_168529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_168525])).

tff(c_168531,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6022])).

tff(c_324,plain,(
    ! [B_60,A_61] :
      ( k3_xboole_0(k1_relat_1(B_60),A_61) = k1_relat_1(k7_relat_1(B_60,A_61))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_359,plain,(
    ! [A_61,B_60] :
      ( k3_xboole_0(A_61,k1_relat_1(B_60)) = k1_relat_1(k7_relat_1(B_60,A_61))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_91])).

tff(c_22,plain,(
    ! [A_19] :
      ( k10_relat_1(A_19,k2_relat_1(A_19)) = k1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_704,plain,(
    ! [A_80,C_81,B_82] :
      ( k3_xboole_0(A_80,k10_relat_1(C_81,B_82)) = k10_relat_1(k7_relat_1(C_81,A_80),B_82)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_785,plain,(
    ! [A_19,A_80] :
      ( k10_relat_1(k7_relat_1(A_19,A_80),k2_relat_1(A_19)) = k3_xboole_0(A_80,k1_relat_1(A_19))
      | ~ v1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_704])).

tff(c_1579,plain,(
    ! [C_94,A_95,B_96] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_94,A_95),B_96),A_95)
      | ~ v1_relat_1(C_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13102,plain,(
    ! [C_278,A_279,B_280] :
      ( k10_relat_1(k7_relat_1(C_278,A_279),B_280) = A_279
      | ~ r1_tarski(A_279,k10_relat_1(k7_relat_1(C_278,A_279),B_280))
      | ~ v1_relat_1(C_278) ) ),
    inference(resolution,[status(thm)],[c_1579,c_2])).

tff(c_124069,plain,(
    ! [A_1051,A_1052] :
      ( k10_relat_1(k7_relat_1(A_1051,A_1052),k2_relat_1(A_1051)) = A_1052
      | ~ r1_tarski(A_1052,k3_xboole_0(A_1052,k1_relat_1(A_1051)))
      | ~ v1_relat_1(A_1051)
      | ~ v1_relat_1(A_1051)
      | ~ v1_relat_1(A_1051) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_13102])).

tff(c_124220,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_124069])).

tff(c_124304,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_32,c_6,c_124220])).

tff(c_754,plain,(
    ! [C_81,A_80,B_82] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_81,A_80),B_82),k10_relat_1(C_81,B_82))
      | ~ v1_relat_1(C_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_132])).

tff(c_124356,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124304,c_754])).

tff(c_124443,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_124356])).

tff(c_5385,plain,(
    ! [A_158,C_159,A_160,B_161] :
      ( r1_tarski(A_158,k10_relat_1(k7_relat_1(C_159,A_160),B_161))
      | ~ r1_tarski(A_158,k10_relat_1(C_159,B_161))
      | ~ r1_tarski(A_158,A_160)
      | ~ v1_relat_1(C_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_12])).

tff(c_5410,plain,(
    ! [A_158,A_80,A_19] :
      ( r1_tarski(A_158,k3_xboole_0(A_80,k1_relat_1(A_19)))
      | ~ r1_tarski(A_158,k10_relat_1(A_19,k2_relat_1(A_19)))
      | ~ r1_tarski(A_158,A_80)
      | ~ v1_relat_1(A_19)
      | ~ v1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_785,c_5385])).

tff(c_124491,plain,(
    ! [A_80] :
      ( r1_tarski('#skF_1',k3_xboole_0(A_80,k1_relat_1('#skF_2')))
      | ~ r1_tarski('#skF_1',A_80)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_124443,c_5410])).

tff(c_127199,plain,(
    ! [A_1067] :
      ( r1_tarski('#skF_1',k3_xboole_0(A_1067,k1_relat_1('#skF_2')))
      | ~ r1_tarski('#skF_1',A_1067) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_124491])).

tff(c_127368,plain,(
    ! [A_61] :
      ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2',A_61)))
      | ~ r1_tarski('#skF_1',A_61)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_127199])).

tff(c_127504,plain,(
    ! [A_61] :
      ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2',A_61)))
      | ~ r1_tarski('#skF_1',A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_127368])).

tff(c_309,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(k7_relat_1(B_58,A_59)) = k9_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_315,plain,(
    ! [B_58,A_59] :
      ( k10_relat_1(k7_relat_1(B_58,A_59),k9_relat_1(B_58,A_59)) = k1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_22])).

tff(c_273,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_254])).

tff(c_12295,plain,(
    ! [A_260,C_261,B_262] :
      ( k3_xboole_0(A_260,k10_relat_1(C_261,B_262)) = A_260
      | ~ r1_tarski(A_260,k10_relat_1(k7_relat_1(C_261,A_260),B_262))
      | ~ v1_relat_1(C_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_273])).

tff(c_180263,plain,(
    ! [A_1288,B_1289] :
      ( k3_xboole_0(A_1288,k10_relat_1(B_1289,k9_relat_1(B_1289,A_1288))) = A_1288
      | ~ r1_tarski(A_1288,k1_relat_1(k7_relat_1(B_1289,A_1288)))
      | ~ v1_relat_1(B_1289)
      | ~ v1_relat_1(k7_relat_1(B_1289,A_1288))
      | ~ v1_relat_1(B_1289) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_12295])).

tff(c_180279,plain,
    ( k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_127504,c_180263])).

tff(c_180361,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32,c_168531,c_180279])).

tff(c_181006,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_180361,c_132])).

tff(c_181193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_181006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:56:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 47.33/36.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.44/36.57  
% 47.44/36.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.44/36.57  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 47.44/36.57  
% 47.44/36.57  %Foreground sorts:
% 47.44/36.57  
% 47.44/36.57  
% 47.44/36.57  %Background operators:
% 47.44/36.57  
% 47.44/36.57  
% 47.44/36.57  %Foreground operators:
% 47.44/36.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 47.44/36.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 47.44/36.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 47.44/36.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 47.44/36.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 47.44/36.57  tff('#skF_2', type, '#skF_2': $i).
% 47.44/36.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 47.44/36.57  tff('#skF_1', type, '#skF_1': $i).
% 47.44/36.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 47.44/36.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 47.44/36.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 47.44/36.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 47.44/36.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 47.44/36.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 47.44/36.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 47.44/36.57  
% 47.44/36.59  tff(f_74, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 47.44/36.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 47.44/36.59  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 47.44/36.59  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 47.44/36.59  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 47.44/36.59  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 47.44/36.59  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 47.44/36.59  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 47.44/36.59  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 47.44/36.59  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 47.44/36.59  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 47.44/36.59  tff(c_28, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 47.44/36.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 47.44/36.59  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 47.44/36.59  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 47.44/36.59  tff(c_12, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, k3_xboole_0(B_9, C_10)) | ~r1_tarski(A_8, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 47.44/36.59  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 47.44/36.59  tff(c_254, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 47.44/36.59  tff(c_464, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=A_72 | ~r1_tarski(A_72, k3_xboole_0(A_72, B_73)))), inference(resolution, [status(thm)], [c_8, c_254])).
% 47.44/36.59  tff(c_468, plain, (![B_9, C_10]: (k3_xboole_0(B_9, C_10)=B_9 | ~r1_tarski(B_9, C_10) | ~r1_tarski(B_9, B_9))), inference(resolution, [status(thm)], [c_12, c_464])).
% 47.44/36.59  tff(c_481, plain, (![B_74, C_75]: (k3_xboole_0(B_74, C_75)=B_74 | ~r1_tarski(B_74, C_75))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_468])).
% 47.44/36.59  tff(c_527, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_481])).
% 47.44/36.59  tff(c_30, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 47.44/36.59  tff(c_526, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_30, c_481])).
% 47.44/36.59  tff(c_14, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 47.44/36.59  tff(c_70, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_47])).
% 47.44/36.59  tff(c_85, plain, (![B_34, A_35]: (k1_setfam_1(k2_tarski(B_34, A_35))=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_14, c_70])).
% 47.44/36.59  tff(c_16, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 47.44/36.59  tff(c_91, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_85, c_16])).
% 47.44/36.59  tff(c_117, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_85, c_16])).
% 47.44/36.59  tff(c_132, plain, (![B_37, A_38]: (r1_tarski(k3_xboole_0(B_37, A_38), A_38))), inference(superposition, [status(thm), theory('equality')], [c_117, c_8])).
% 47.44/36.59  tff(c_910, plain, (![B_85, A_86]: (k3_xboole_0(k3_xboole_0(B_85, A_86), A_86)=k3_xboole_0(B_85, A_86))), inference(resolution, [status(thm)], [c_132, c_481])).
% 47.44/36.59  tff(c_2329, plain, (![A_106, B_107]: (k3_xboole_0(k3_xboole_0(A_106, B_107), A_106)=k3_xboole_0(B_107, A_106))), inference(superposition, [status(thm), theory('equality')], [c_91, c_910])).
% 47.44/36.59  tff(c_2502, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_526, c_2329])).
% 47.44/36.59  tff(c_2563, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_527, c_2502])).
% 47.44/36.59  tff(c_24, plain, (![B_21, A_20]: (k3_xboole_0(k1_relat_1(B_21), A_20)=k1_relat_1(k7_relat_1(B_21, A_20)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 47.44/36.59  tff(c_2662, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2563, c_24])).
% 47.44/36.59  tff(c_2714, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2662])).
% 47.44/36.59  tff(c_528, plain, (![B_76]: (k3_xboole_0(B_76, B_76)=B_76)), inference(resolution, [status(thm)], [c_6, c_481])).
% 47.44/36.59  tff(c_5966, plain, (![B_171]: (k1_relat_1(k7_relat_1(B_171, k1_relat_1(B_171)))=k1_relat_1(B_171) | ~v1_relat_1(B_171))), inference(superposition, [status(thm), theory('equality')], [c_24, c_528])).
% 47.44/36.59  tff(c_6013, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2714, c_5966])).
% 47.44/36.59  tff(c_6022, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2714, c_6013])).
% 47.44/36.59  tff(c_168522, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_6022])).
% 47.44/36.59  tff(c_168525, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_168522])).
% 47.44/36.59  tff(c_168529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_168525])).
% 47.44/36.59  tff(c_168531, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_6022])).
% 47.44/36.59  tff(c_324, plain, (![B_60, A_61]: (k3_xboole_0(k1_relat_1(B_60), A_61)=k1_relat_1(k7_relat_1(B_60, A_61)) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 47.44/36.59  tff(c_359, plain, (![A_61, B_60]: (k3_xboole_0(A_61, k1_relat_1(B_60))=k1_relat_1(k7_relat_1(B_60, A_61)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_324, c_91])).
% 47.44/36.59  tff(c_22, plain, (![A_19]: (k10_relat_1(A_19, k2_relat_1(A_19))=k1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 47.44/36.59  tff(c_704, plain, (![A_80, C_81, B_82]: (k3_xboole_0(A_80, k10_relat_1(C_81, B_82))=k10_relat_1(k7_relat_1(C_81, A_80), B_82) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_67])).
% 47.44/36.59  tff(c_785, plain, (![A_19, A_80]: (k10_relat_1(k7_relat_1(A_19, A_80), k2_relat_1(A_19))=k3_xboole_0(A_80, k1_relat_1(A_19)) | ~v1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_22, c_704])).
% 47.44/36.59  tff(c_1579, plain, (![C_94, A_95, B_96]: (r1_tarski(k10_relat_1(k7_relat_1(C_94, A_95), B_96), A_95) | ~v1_relat_1(C_94))), inference(superposition, [status(thm), theory('equality')], [c_704, c_8])).
% 47.44/36.59  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 47.44/36.59  tff(c_13102, plain, (![C_278, A_279, B_280]: (k10_relat_1(k7_relat_1(C_278, A_279), B_280)=A_279 | ~r1_tarski(A_279, k10_relat_1(k7_relat_1(C_278, A_279), B_280)) | ~v1_relat_1(C_278))), inference(resolution, [status(thm)], [c_1579, c_2])).
% 47.44/36.59  tff(c_124069, plain, (![A_1051, A_1052]: (k10_relat_1(k7_relat_1(A_1051, A_1052), k2_relat_1(A_1051))=A_1052 | ~r1_tarski(A_1052, k3_xboole_0(A_1052, k1_relat_1(A_1051))) | ~v1_relat_1(A_1051) | ~v1_relat_1(A_1051) | ~v1_relat_1(A_1051))), inference(superposition, [status(thm), theory('equality')], [c_785, c_13102])).
% 47.44/36.59  tff(c_124220, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_526, c_124069])).
% 47.44/36.59  tff(c_124304, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_32, c_6, c_124220])).
% 47.44/36.59  tff(c_754, plain, (![C_81, A_80, B_82]: (r1_tarski(k10_relat_1(k7_relat_1(C_81, A_80), B_82), k10_relat_1(C_81, B_82)) | ~v1_relat_1(C_81))), inference(superposition, [status(thm), theory('equality')], [c_704, c_132])).
% 47.44/36.59  tff(c_124356, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124304, c_754])).
% 47.44/36.59  tff(c_124443, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_124356])).
% 47.44/36.59  tff(c_5385, plain, (![A_158, C_159, A_160, B_161]: (r1_tarski(A_158, k10_relat_1(k7_relat_1(C_159, A_160), B_161)) | ~r1_tarski(A_158, k10_relat_1(C_159, B_161)) | ~r1_tarski(A_158, A_160) | ~v1_relat_1(C_159))), inference(superposition, [status(thm), theory('equality')], [c_704, c_12])).
% 47.44/36.59  tff(c_5410, plain, (![A_158, A_80, A_19]: (r1_tarski(A_158, k3_xboole_0(A_80, k1_relat_1(A_19))) | ~r1_tarski(A_158, k10_relat_1(A_19, k2_relat_1(A_19))) | ~r1_tarski(A_158, A_80) | ~v1_relat_1(A_19) | ~v1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(superposition, [status(thm), theory('equality')], [c_785, c_5385])).
% 47.44/36.59  tff(c_124491, plain, (![A_80]: (r1_tarski('#skF_1', k3_xboole_0(A_80, k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_1', A_80) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_124443, c_5410])).
% 47.44/36.59  tff(c_127199, plain, (![A_1067]: (r1_tarski('#skF_1', k3_xboole_0(A_1067, k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_1', A_1067))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_124491])).
% 47.44/36.59  tff(c_127368, plain, (![A_61]: (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', A_61))) | ~r1_tarski('#skF_1', A_61) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_359, c_127199])).
% 47.44/36.59  tff(c_127504, plain, (![A_61]: (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', A_61))) | ~r1_tarski('#skF_1', A_61))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_127368])).
% 47.44/36.59  tff(c_309, plain, (![B_58, A_59]: (k2_relat_1(k7_relat_1(B_58, A_59))=k9_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 47.44/36.59  tff(c_315, plain, (![B_58, A_59]: (k10_relat_1(k7_relat_1(B_58, A_59), k9_relat_1(B_58, A_59))=k1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_309, c_22])).
% 47.44/36.59  tff(c_273, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_254])).
% 47.44/36.59  tff(c_12295, plain, (![A_260, C_261, B_262]: (k3_xboole_0(A_260, k10_relat_1(C_261, B_262))=A_260 | ~r1_tarski(A_260, k10_relat_1(k7_relat_1(C_261, A_260), B_262)) | ~v1_relat_1(C_261))), inference(superposition, [status(thm), theory('equality')], [c_704, c_273])).
% 47.44/36.59  tff(c_180263, plain, (![A_1288, B_1289]: (k3_xboole_0(A_1288, k10_relat_1(B_1289, k9_relat_1(B_1289, A_1288)))=A_1288 | ~r1_tarski(A_1288, k1_relat_1(k7_relat_1(B_1289, A_1288))) | ~v1_relat_1(B_1289) | ~v1_relat_1(k7_relat_1(B_1289, A_1288)) | ~v1_relat_1(B_1289))), inference(superposition, [status(thm), theory('equality')], [c_315, c_12295])).
% 47.44/36.59  tff(c_180279, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_127504, c_180263])).
% 47.44/36.59  tff(c_180361, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32, c_168531, c_180279])).
% 47.44/36.59  tff(c_181006, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_180361, c_132])).
% 47.44/36.59  tff(c_181193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_181006])).
% 47.44/36.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.44/36.59  
% 47.44/36.59  Inference rules
% 47.44/36.59  ----------------------
% 47.44/36.59  #Ref     : 0
% 47.44/36.59  #Sup     : 45607
% 47.44/36.59  #Fact    : 0
% 47.44/36.59  #Define  : 0
% 47.44/36.59  #Split   : 3
% 47.44/36.59  #Chain   : 0
% 47.44/36.59  #Close   : 0
% 47.44/36.59  
% 47.44/36.59  Ordering : KBO
% 47.44/36.59  
% 47.44/36.59  Simplification rules
% 47.44/36.59  ----------------------
% 47.44/36.59  #Subsume      : 10291
% 47.44/36.59  #Demod        : 27207
% 47.44/36.59  #Tautology    : 12974
% 47.44/36.59  #SimpNegUnit  : 7
% 47.44/36.59  #BackRed      : 0
% 47.44/36.59  
% 47.44/36.59  #Partial instantiations: 0
% 47.44/36.59  #Strategies tried      : 1
% 47.44/36.59  
% 47.44/36.59  Timing (in seconds)
% 47.44/36.59  ----------------------
% 47.44/36.59  Preprocessing        : 0.30
% 47.44/36.59  Parsing              : 0.16
% 47.44/36.59  CNF conversion       : 0.02
% 47.44/36.59  Main loop            : 35.52
% 47.44/36.59  Inferencing          : 3.20
% 47.44/36.59  Reduction            : 18.07
% 47.44/36.59  Demodulation         : 16.66
% 47.44/36.60  BG Simplification    : 0.48
% 47.44/36.60  Subsumption          : 12.07
% 47.44/36.60  Abstraction          : 0.71
% 47.44/36.60  MUC search           : 0.00
% 47.44/36.60  Cooper               : 0.00
% 47.44/36.60  Total                : 35.86
% 47.44/36.60  Index Insertion      : 0.00
% 47.44/36.60  Index Deletion       : 0.00
% 47.44/36.60  Index Matching       : 0.00
% 47.44/36.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
