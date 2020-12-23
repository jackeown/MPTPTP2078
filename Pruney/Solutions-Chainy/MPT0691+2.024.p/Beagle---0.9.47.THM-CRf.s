%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:42 EST 2020

% Result     : Theorem 23.03s
% Output     : CNFRefutation 23.08s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 184 expanded)
%              Number of leaves         :   30 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  132 ( 336 expanded)
%              Number of equality atoms :   30 (  69 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_548,plain,(
    ! [B_89,A_90] :
      ( k1_relat_1(k7_relat_1(B_89,A_90)) = A_90
      | ~ r1_tarski(A_90,k1_relat_1(B_89))
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_558,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_548])).

tff(c_567,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_558])).

tff(c_28,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k10_relat_1(B_25,A_24),k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_578,plain,(
    ! [A_24] :
      ( r1_tarski(k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_24),'#skF_2')
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_28])).

tff(c_1072,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_578])).

tff(c_1075,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1072])).

tff(c_1079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1075])).

tff(c_1081,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_87,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_433,plain,(
    ! [B_79,A_80] :
      ( k2_relat_1(k7_relat_1(B_79,A_80)) = k9_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_26] :
      ( k10_relat_1(A_26,k2_relat_1(A_26)) = k1_relat_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_439,plain,(
    ! [B_79,A_80] :
      ( k10_relat_1(k7_relat_1(B_79,A_80),k9_relat_1(B_79,A_80)) = k1_relat_1(k7_relat_1(B_79,A_80))
      | ~ v1_relat_1(k7_relat_1(B_79,A_80))
      | ~ v1_relat_1(B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(k10_relat_1(B_47,A_48),k1_relat_1(B_47))
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    ! [B_47,A_48] :
      ( k3_xboole_0(k10_relat_1(B_47,A_48),k1_relat_1(B_47)) = k10_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_133,c_20])).

tff(c_2582,plain,(
    ! [B_151,A_152] :
      ( k3_xboole_0(k1_relat_1(B_151),k10_relat_1(B_151,A_152)) = k10_relat_1(B_151,A_152)
      | ~ v1_relat_1(B_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_139])).

tff(c_2623,plain,(
    ! [A_152] :
      ( k3_xboole_0('#skF_2',k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_152)) = k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_152)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_2582])).

tff(c_14844,plain,(
    ! [A_378] : k3_xboole_0('#skF_2',k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_378)) = k10_relat_1(k7_relat_1('#skF_3','#skF_2'),A_378) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_2623])).

tff(c_14857,plain,
    ( k3_xboole_0('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) = k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_14844])).

tff(c_14883,plain,(
    k10_relat_1(k7_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1081,c_87,c_567,c_14857])).

tff(c_1284,plain,(
    ! [A_120,C_121,B_122] :
      ( k3_xboole_0(A_120,k10_relat_1(C_121,B_122)) = k10_relat_1(k7_relat_1(C_121,A_120),B_122)
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1297,plain,(
    ! [C_121,B_122,A_120] :
      ( k3_xboole_0(k10_relat_1(C_121,B_122),A_120) = k10_relat_1(k7_relat_1(C_121,A_120),B_122)
      | ~ v1_relat_1(C_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_2])).

tff(c_8850,plain,(
    ! [A_270,A_271] :
      ( k10_relat_1(k7_relat_1(A_270,A_271),k2_relat_1(A_270)) = k3_xboole_0(A_271,k1_relat_1(A_270))
      | ~ v1_relat_1(A_270)
      | ~ v1_relat_1(A_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1284])).

tff(c_32086,plain,(
    ! [A_609,A_610] :
      ( r1_tarski(k3_xboole_0(A_609,k1_relat_1(A_610)),k1_relat_1(k7_relat_1(A_610,A_609)))
      | ~ v1_relat_1(k7_relat_1(A_610,A_609))
      | ~ v1_relat_1(A_610)
      | ~ v1_relat_1(A_610) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8850,c_28])).

tff(c_123,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_45,A_46)),A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_130,plain,(
    ! [B_45,A_46] :
      ( k2_xboole_0(k1_relat_1(k7_relat_1(B_45,A_46)),A_46) = A_46
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_123,c_18])).

tff(c_877,plain,(
    ! [A_110,C_111,B_112] :
      ( r1_tarski(k2_xboole_0(A_110,C_111),B_112)
      | ~ r1_tarski(C_111,B_112)
      | ~ r1_tarski(A_110,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4590,plain,(
    ! [A_203,C_204,B_205] :
      ( k2_xboole_0(k2_xboole_0(A_203,C_204),B_205) = B_205
      | ~ r1_tarski(C_204,B_205)
      | ~ r1_tarski(A_203,B_205) ) ),
    inference(resolution,[status(thm)],[c_877,c_18])).

tff(c_161,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(A_53,C_54)
      | ~ r1_tarski(k2_xboole_0(A_53,B_55),C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_180,plain,(
    ! [A_57,B_58] : r1_tarski(A_57,k2_xboole_0(A_57,B_58)) ),
    inference(resolution,[status(thm)],[c_14,c_161])).

tff(c_16,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,C_12)
      | ~ r1_tarski(k2_xboole_0(A_10,B_11),C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_244,plain,(
    ! [A_62,B_63,B_64] : r1_tarski(A_62,k2_xboole_0(k2_xboole_0(A_62,B_63),B_64)) ),
    inference(resolution,[status(thm)],[c_180,c_16])).

tff(c_272,plain,(
    ! [A_10,B_11,B_63,B_64] : r1_tarski(A_10,k2_xboole_0(k2_xboole_0(k2_xboole_0(A_10,B_11),B_63),B_64)) ),
    inference(resolution,[status(thm)],[c_244,c_16])).

tff(c_4845,plain,(
    ! [A_206,B_207,B_208,C_209] :
      ( r1_tarski(A_206,k2_xboole_0(B_207,B_208))
      | ~ r1_tarski(C_209,B_207)
      | ~ r1_tarski(A_206,B_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4590,c_272])).

tff(c_5149,plain,(
    ! [A_215,B_216,B_217] :
      ( r1_tarski(A_215,k2_xboole_0(B_216,B_217))
      | ~ r1_tarski(A_215,B_216) ) ),
    inference(resolution,[status(thm)],[c_14,c_4845])).

tff(c_5239,plain,(
    ! [A_215,A_46,B_45] :
      ( r1_tarski(A_215,A_46)
      | ~ r1_tarski(A_215,k1_relat_1(k7_relat_1(B_45,A_46)))
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_5149])).

tff(c_33048,plain,(
    ! [A_622,A_623] :
      ( r1_tarski(k3_xboole_0(A_622,k1_relat_1(A_623)),A_622)
      | ~ v1_relat_1(k7_relat_1(A_623,A_622))
      | ~ v1_relat_1(A_623) ) ),
    inference(resolution,[status(thm)],[c_32086,c_5239])).

tff(c_33241,plain,(
    ! [A_622] :
      ( r1_tarski(k3_xboole_0(A_622,'#skF_2'),A_622)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),A_622))
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_33048])).

tff(c_33310,plain,(
    ! [A_624] :
      ( r1_tarski(k3_xboole_0(A_624,'#skF_2'),A_624)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),A_624)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_33241])).

tff(c_33313,plain,(
    ! [B_21] :
      ( r1_tarski(k3_xboole_0(B_21,'#skF_2'),B_21)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_24,c_33310])).

tff(c_33701,plain,(
    ! [B_629] : r1_tarski(k3_xboole_0(B_629,'#skF_2'),B_629) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_33313])).

tff(c_85743,plain,(
    ! [C_969,B_970] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_969,'#skF_2'),B_970),k10_relat_1(C_969,B_970))
      | ~ v1_relat_1(C_969) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1297,c_33701])).

tff(c_85937,plain,
    ( r1_tarski('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14883,c_85743])).

tff(c_86067,plain,(
    r1_tarski('#skF_2',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_85937])).

tff(c_86069,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_86067])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:05:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.03/14.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.08/14.97  
% 23.08/14.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.08/14.98  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 23.08/14.98  
% 23.08/14.98  %Foreground sorts:
% 23.08/14.98  
% 23.08/14.98  
% 23.08/14.98  %Background operators:
% 23.08/14.98  
% 23.08/14.98  
% 23.08/14.98  %Foreground operators:
% 23.08/14.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.08/14.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.08/14.98  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 23.08/14.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.08/14.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.08/14.98  tff('#skF_2', type, '#skF_2': $i).
% 23.08/14.98  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 23.08/14.98  tff('#skF_3', type, '#skF_3': $i).
% 23.08/14.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.08/14.98  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 23.08/14.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.08/14.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.08/14.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.08/14.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.08/14.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 23.08/14.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.08/14.98  
% 23.08/14.99  tff(f_95, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 23.08/14.99  tff(f_62, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 23.08/14.99  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 23.08/14.99  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 23.08/14.99  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.08/14.99  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 23.08/14.99  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 23.08/14.99  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 23.08/14.99  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 23.08/14.99  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 23.08/14.99  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 23.08/14.99  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 23.08/14.99  tff(f_58, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 23.08/14.99  tff(f_44, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 23.08/14.99  tff(c_38, plain, (~r1_tarski('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 23.08/14.99  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 23.08/14.99  tff(c_24, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 23.08/14.99  tff(c_40, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 23.08/14.99  tff(c_548, plain, (![B_89, A_90]: (k1_relat_1(k7_relat_1(B_89, A_90))=A_90 | ~r1_tarski(A_90, k1_relat_1(B_89)) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_84])).
% 23.08/14.99  tff(c_558, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_548])).
% 23.08/14.99  tff(c_567, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_558])).
% 23.08/14.99  tff(c_28, plain, (![B_25, A_24]: (r1_tarski(k10_relat_1(B_25, A_24), k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 23.08/14.99  tff(c_578, plain, (![A_24]: (r1_tarski(k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_24), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_567, c_28])).
% 23.08/14.99  tff(c_1072, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_578])).
% 23.08/14.99  tff(c_1075, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1072])).
% 23.08/14.99  tff(c_1079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1075])).
% 23.08/14.99  tff(c_1081, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_578])).
% 23.08/14.99  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.08/14.99  tff(c_79, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_52])).
% 23.08/14.99  tff(c_87, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_14, c_79])).
% 23.08/14.99  tff(c_433, plain, (![B_79, A_80]: (k2_relat_1(k7_relat_1(B_79, A_80))=k9_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_66])).
% 23.08/14.99  tff(c_30, plain, (![A_26]: (k10_relat_1(A_26, k2_relat_1(A_26))=k1_relat_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 23.08/14.99  tff(c_439, plain, (![B_79, A_80]: (k10_relat_1(k7_relat_1(B_79, A_80), k9_relat_1(B_79, A_80))=k1_relat_1(k7_relat_1(B_79, A_80)) | ~v1_relat_1(k7_relat_1(B_79, A_80)) | ~v1_relat_1(B_79))), inference(superposition, [status(thm), theory('equality')], [c_433, c_30])).
% 23.08/14.99  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.08/14.99  tff(c_133, plain, (![B_47, A_48]: (r1_tarski(k10_relat_1(B_47, A_48), k1_relat_1(B_47)) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_70])).
% 23.08/14.99  tff(c_20, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 23.08/14.99  tff(c_139, plain, (![B_47, A_48]: (k3_xboole_0(k10_relat_1(B_47, A_48), k1_relat_1(B_47))=k10_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_133, c_20])).
% 23.08/14.99  tff(c_2582, plain, (![B_151, A_152]: (k3_xboole_0(k1_relat_1(B_151), k10_relat_1(B_151, A_152))=k10_relat_1(B_151, A_152) | ~v1_relat_1(B_151))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_139])).
% 23.08/14.99  tff(c_2623, plain, (![A_152]: (k3_xboole_0('#skF_2', k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_152))=k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_152) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_567, c_2582])).
% 23.08/14.99  tff(c_14844, plain, (![A_378]: (k3_xboole_0('#skF_2', k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_378))=k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_378))), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_2623])).
% 23.08/14.99  tff(c_14857, plain, (k3_xboole_0('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))=k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_439, c_14844])).
% 23.08/14.99  tff(c_14883, plain, (k10_relat_1(k7_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1081, c_87, c_567, c_14857])).
% 23.08/14.99  tff(c_1284, plain, (![A_120, C_121, B_122]: (k3_xboole_0(A_120, k10_relat_1(C_121, B_122))=k10_relat_1(k7_relat_1(C_121, A_120), B_122) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_88])).
% 23.08/14.99  tff(c_1297, plain, (![C_121, B_122, A_120]: (k3_xboole_0(k10_relat_1(C_121, B_122), A_120)=k10_relat_1(k7_relat_1(C_121, A_120), B_122) | ~v1_relat_1(C_121))), inference(superposition, [status(thm), theory('equality')], [c_1284, c_2])).
% 23.08/14.99  tff(c_8850, plain, (![A_270, A_271]: (k10_relat_1(k7_relat_1(A_270, A_271), k2_relat_1(A_270))=k3_xboole_0(A_271, k1_relat_1(A_270)) | ~v1_relat_1(A_270) | ~v1_relat_1(A_270))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1284])).
% 23.08/14.99  tff(c_32086, plain, (![A_609, A_610]: (r1_tarski(k3_xboole_0(A_609, k1_relat_1(A_610)), k1_relat_1(k7_relat_1(A_610, A_609))) | ~v1_relat_1(k7_relat_1(A_610, A_609)) | ~v1_relat_1(A_610) | ~v1_relat_1(A_610))), inference(superposition, [status(thm), theory('equality')], [c_8850, c_28])).
% 23.08/14.99  tff(c_123, plain, (![B_45, A_46]: (r1_tarski(k1_relat_1(k7_relat_1(B_45, A_46)), A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.08/14.99  tff(c_18, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 23.08/14.99  tff(c_130, plain, (![B_45, A_46]: (k2_xboole_0(k1_relat_1(k7_relat_1(B_45, A_46)), A_46)=A_46 | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_123, c_18])).
% 23.08/14.99  tff(c_877, plain, (![A_110, C_111, B_112]: (r1_tarski(k2_xboole_0(A_110, C_111), B_112) | ~r1_tarski(C_111, B_112) | ~r1_tarski(A_110, B_112))), inference(cnfTransformation, [status(thm)], [f_58])).
% 23.08/14.99  tff(c_4590, plain, (![A_203, C_204, B_205]: (k2_xboole_0(k2_xboole_0(A_203, C_204), B_205)=B_205 | ~r1_tarski(C_204, B_205) | ~r1_tarski(A_203, B_205))), inference(resolution, [status(thm)], [c_877, c_18])).
% 23.08/14.99  tff(c_161, plain, (![A_53, C_54, B_55]: (r1_tarski(A_53, C_54) | ~r1_tarski(k2_xboole_0(A_53, B_55), C_54))), inference(cnfTransformation, [status(thm)], [f_44])).
% 23.08/14.99  tff(c_180, plain, (![A_57, B_58]: (r1_tarski(A_57, k2_xboole_0(A_57, B_58)))), inference(resolution, [status(thm)], [c_14, c_161])).
% 23.08/14.99  tff(c_16, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, C_12) | ~r1_tarski(k2_xboole_0(A_10, B_11), C_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 23.08/14.99  tff(c_244, plain, (![A_62, B_63, B_64]: (r1_tarski(A_62, k2_xboole_0(k2_xboole_0(A_62, B_63), B_64)))), inference(resolution, [status(thm)], [c_180, c_16])).
% 23.08/14.99  tff(c_272, plain, (![A_10, B_11, B_63, B_64]: (r1_tarski(A_10, k2_xboole_0(k2_xboole_0(k2_xboole_0(A_10, B_11), B_63), B_64)))), inference(resolution, [status(thm)], [c_244, c_16])).
% 23.08/14.99  tff(c_4845, plain, (![A_206, B_207, B_208, C_209]: (r1_tarski(A_206, k2_xboole_0(B_207, B_208)) | ~r1_tarski(C_209, B_207) | ~r1_tarski(A_206, B_207))), inference(superposition, [status(thm), theory('equality')], [c_4590, c_272])).
% 23.08/14.99  tff(c_5149, plain, (![A_215, B_216, B_217]: (r1_tarski(A_215, k2_xboole_0(B_216, B_217)) | ~r1_tarski(A_215, B_216))), inference(resolution, [status(thm)], [c_14, c_4845])).
% 23.08/14.99  tff(c_5239, plain, (![A_215, A_46, B_45]: (r1_tarski(A_215, A_46) | ~r1_tarski(A_215, k1_relat_1(k7_relat_1(B_45, A_46))) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_130, c_5149])).
% 23.08/14.99  tff(c_33048, plain, (![A_622, A_623]: (r1_tarski(k3_xboole_0(A_622, k1_relat_1(A_623)), A_622) | ~v1_relat_1(k7_relat_1(A_623, A_622)) | ~v1_relat_1(A_623))), inference(resolution, [status(thm)], [c_32086, c_5239])).
% 23.08/14.99  tff(c_33241, plain, (![A_622]: (r1_tarski(k3_xboole_0(A_622, '#skF_2'), A_622) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_622)) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_567, c_33048])).
% 23.08/14.99  tff(c_33310, plain, (![A_624]: (r1_tarski(k3_xboole_0(A_624, '#skF_2'), A_624) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_624)))), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_33241])).
% 23.08/14.99  tff(c_33313, plain, (![B_21]: (r1_tarski(k3_xboole_0(B_21, '#skF_2'), B_21) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_24, c_33310])).
% 23.08/14.99  tff(c_33701, plain, (![B_629]: (r1_tarski(k3_xboole_0(B_629, '#skF_2'), B_629))), inference(demodulation, [status(thm), theory('equality')], [c_1081, c_33313])).
% 23.08/14.99  tff(c_85743, plain, (![C_969, B_970]: (r1_tarski(k10_relat_1(k7_relat_1(C_969, '#skF_2'), B_970), k10_relat_1(C_969, B_970)) | ~v1_relat_1(C_969))), inference(superposition, [status(thm), theory('equality')], [c_1297, c_33701])).
% 23.08/14.99  tff(c_85937, plain, (r1_tarski('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14883, c_85743])).
% 23.08/14.99  tff(c_86067, plain, (r1_tarski('#skF_2', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_85937])).
% 23.08/14.99  tff(c_86069, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_86067])).
% 23.08/14.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.08/14.99  
% 23.08/14.99  Inference rules
% 23.08/14.99  ----------------------
% 23.08/14.99  #Ref     : 0
% 23.08/14.99  #Sup     : 21696
% 23.08/14.99  #Fact    : 0
% 23.08/14.99  #Define  : 0
% 23.08/14.99  #Split   : 5
% 23.08/14.99  #Chain   : 0
% 23.08/14.99  #Close   : 0
% 23.08/14.99  
% 23.08/14.99  Ordering : KBO
% 23.08/14.99  
% 23.08/14.99  Simplification rules
% 23.08/14.99  ----------------------
% 23.08/14.99  #Subsume      : 5976
% 23.08/14.99  #Demod        : 16214
% 23.08/14.99  #Tautology    : 6594
% 23.08/14.99  #SimpNegUnit  : 7
% 23.08/14.99  #BackRed      : 6
% 23.08/14.99  
% 23.08/14.99  #Partial instantiations: 0
% 23.08/14.99  #Strategies tried      : 1
% 23.08/14.99  
% 23.08/14.99  Timing (in seconds)
% 23.08/14.99  ----------------------
% 23.08/15.00  Preprocessing        : 0.33
% 23.08/15.00  Parsing              : 0.18
% 23.08/15.00  CNF conversion       : 0.02
% 23.08/15.00  Main loop            : 13.90
% 23.08/15.00  Inferencing          : 1.80
% 23.08/15.00  Reduction            : 6.83
% 23.08/15.00  Demodulation         : 6.02
% 23.08/15.00  BG Simplification    : 0.25
% 23.08/15.00  Subsumption          : 4.42
% 23.08/15.00  Abstraction          : 0.43
% 23.08/15.00  MUC search           : 0.00
% 23.08/15.00  Cooper               : 0.00
% 23.08/15.00  Total                : 14.26
% 23.08/15.00  Index Insertion      : 0.00
% 23.08/15.00  Index Deletion       : 0.00
% 23.08/15.00  Index Matching       : 0.00
% 23.08/15.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
