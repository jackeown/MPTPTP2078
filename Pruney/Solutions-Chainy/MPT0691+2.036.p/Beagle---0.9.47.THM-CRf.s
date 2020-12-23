%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:44 EST 2020

% Result     : Theorem 27.58s
% Output     : CNFRefutation 27.58s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 341 expanded)
%              Number of leaves         :   32 ( 125 expanded)
%              Depth                    :   17
%              Number of atoms          :  135 ( 657 expanded)
%              Number of equality atoms :   34 ( 141 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_42,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    ! [B_27,A_26] :
      ( k2_relat_1(k7_relat_1(B_27,A_26)) = k9_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k7_relat_1(A_24,B_25))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_30] :
      ( k10_relat_1(A_30,k2_relat_1(A_30)) = k1_relat_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2226,plain,(
    ! [C_140,A_141,B_142] :
      ( r1_tarski(k10_relat_1(C_140,A_141),k10_relat_1(C_140,B_142))
      | ~ r1_tarski(A_141,B_142)
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20755,plain,(
    ! [A_341,B_342] :
      ( r1_tarski(k1_relat_1(A_341),k10_relat_1(A_341,B_342))
      | ~ r1_tarski(k2_relat_1(A_341),B_342)
      | ~ v1_relat_1(A_341)
      | ~ v1_relat_1(A_341) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2226])).

tff(c_30,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k10_relat_1(B_29,A_28),k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_339,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(B_71,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_354,plain,(
    ! [B_29,A_28] :
      ( k10_relat_1(B_29,A_28) = k1_relat_1(B_29)
      | ~ r1_tarski(k1_relat_1(B_29),k10_relat_1(B_29,A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_30,c_339])).

tff(c_36100,plain,(
    ! [A_491,B_492] :
      ( k10_relat_1(A_491,B_492) = k1_relat_1(A_491)
      | ~ r1_tarski(k2_relat_1(A_491),B_492)
      | ~ v1_relat_1(A_491) ) ),
    inference(resolution,[status(thm)],[c_20755,c_354])).

tff(c_101847,plain,(
    ! [A_988,B_989] :
      ( k10_relat_1(A_988,k2_xboole_0(k2_relat_1(A_988),B_989)) = k1_relat_1(A_988)
      | ~ v1_relat_1(A_988) ) ),
    inference(resolution,[status(thm)],[c_20,c_36100])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_177,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(A_59,B_60) = B_60
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_197,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_177])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_391,plain,(
    ! [A_76,C_77,B_78] :
      ( r1_tarski(A_76,C_77)
      | ~ r1_tarski(k2_xboole_0(A_76,B_78),C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6948,plain,(
    ! [A_212,C_213,B_214,B_215] :
      ( r1_tarski(A_212,k2_xboole_0(C_213,B_214))
      | ~ r1_tarski(k2_xboole_0(A_212,B_215),B_214) ) ),
    inference(resolution,[status(thm)],[c_10,c_391])).

tff(c_7006,plain,(
    ! [A_216,C_217,B_218] : r1_tarski(A_216,k2_xboole_0(C_217,k2_xboole_0(A_216,B_218))) ),
    inference(resolution,[status(thm)],[c_8,c_6948])).

tff(c_7102,plain,(
    ! [B_4,C_217] : r1_tarski(B_4,k2_xboole_0(C_217,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_7006])).

tff(c_44,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_196,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_177])).

tff(c_401,plain,(
    ! [C_77] :
      ( r1_tarski('#skF_1',C_77)
      | ~ r1_tarski(k1_relat_1('#skF_2'),C_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_391])).

tff(c_20768,plain,(
    ! [B_342] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_2',B_342))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_342)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20755,c_401])).

tff(c_24874,plain,(
    ! [B_393] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_2',B_393))
      | ~ r1_tarski(k2_relat_1('#skF_2'),B_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_20768])).

tff(c_24951,plain,(
    ! [C_394] : r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_xboole_0(C_394,k2_relat_1('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_7102,c_24874])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_73377,plain,(
    ! [C_800] : k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_xboole_0(C_800,k2_relat_1('#skF_2')))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24951,c_18])).

tff(c_40,plain,(
    ! [A_38,C_40,B_39] :
      ( k3_xboole_0(A_38,k10_relat_1(C_40,B_39)) = k10_relat_1(k7_relat_1(C_40,A_38),B_39)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_73602,plain,(
    ! [C_800] :
      ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_xboole_0(C_800,k2_relat_1('#skF_2'))) = '#skF_1'
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73377,c_40])).

tff(c_73765,plain,(
    ! [C_800] : k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_xboole_0(C_800,k2_relat_1('#skF_2'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73602])).

tff(c_101919,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_101847,c_73765])).

tff(c_102217,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_101919])).

tff(c_102220,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_102217])).

tff(c_102224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_102220])).

tff(c_102226,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_101919])).

tff(c_102225,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_101919])).

tff(c_25029,plain,(
    ! [B_395] : r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_xboole_0(k2_relat_1('#skF_2'),B_395))) ),
    inference(resolution,[status(thm)],[c_20,c_24874])).

tff(c_75541,plain,(
    ! [B_811] : k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_xboole_0(k2_relat_1('#skF_2'),B_811))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_25029,c_18])).

tff(c_75769,plain,(
    ! [B_811] :
      ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_xboole_0(k2_relat_1('#skF_2'),B_811)) = '#skF_1'
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75541,c_40])).

tff(c_75936,plain,(
    ! [B_811] : k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_xboole_0(k2_relat_1('#skF_2'),B_811)) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_75769])).

tff(c_849,plain,(
    ! [B_104,A_105] :
      ( r1_tarski(k10_relat_1(B_104,A_105),k10_relat_1(B_104,k2_relat_1(B_104)))
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22050,plain,(
    ! [B_362,A_363] :
      ( k10_relat_1(B_362,k2_relat_1(B_362)) = k10_relat_1(B_362,A_363)
      | ~ r1_tarski(k10_relat_1(B_362,k2_relat_1(B_362)),k10_relat_1(B_362,A_363))
      | ~ v1_relat_1(B_362) ) ),
    inference(resolution,[status(thm)],[c_849,c_4])).

tff(c_117630,plain,(
    ! [A_1079,A_1080] :
      ( k10_relat_1(A_1079,k2_relat_1(A_1079)) = k10_relat_1(A_1079,A_1080)
      | ~ r1_tarski(k1_relat_1(A_1079),k10_relat_1(A_1079,A_1080))
      | ~ v1_relat_1(A_1079)
      | ~ v1_relat_1(A_1079) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_22050])).

tff(c_117666,plain,(
    ! [B_811] :
      ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_xboole_0(k2_relat_1('#skF_2'),B_811)) = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75936,c_117630])).

tff(c_117712,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102226,c_102226,c_8,c_102225,c_75936,c_117666])).

tff(c_1748,plain,(
    ! [A_131,C_132,B_133] :
      ( k3_xboole_0(A_131,k10_relat_1(C_132,B_133)) = k10_relat_1(k7_relat_1(C_132,A_131),B_133)
      | ~ v1_relat_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10452,plain,(
    ! [C_253,B_254,A_255] :
      ( k3_xboole_0(k10_relat_1(C_253,B_254),A_255) = k10_relat_1(k7_relat_1(C_253,A_255),B_254)
      | ~ v1_relat_1(C_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1748,c_2])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k3_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10621,plain,(
    ! [C_253,A_255,B_254] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_253,A_255),B_254),k10_relat_1(C_253,B_254))
      | ~ v1_relat_1(C_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10452,c_16])).

tff(c_117856,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_117712,c_10621])).

tff(c_118041,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_117856])).

tff(c_118147,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_118041])).

tff(c_118169,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_118147])).

tff(c_118171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_118169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.58/19.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.58/19.20  
% 27.58/19.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.58/19.21  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 27.58/19.21  
% 27.58/19.21  %Foreground sorts:
% 27.58/19.21  
% 27.58/19.21  
% 27.58/19.21  %Background operators:
% 27.58/19.21  
% 27.58/19.21  
% 27.58/19.21  %Foreground operators:
% 27.58/19.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.58/19.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 27.58/19.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.58/19.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.58/19.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.58/19.21  tff('#skF_2', type, '#skF_2': $i).
% 27.58/19.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 27.58/19.21  tff('#skF_1', type, '#skF_1': $i).
% 27.58/19.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.58/19.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 27.58/19.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.58/19.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.58/19.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.58/19.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 27.58/19.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.58/19.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 27.58/19.21  
% 27.58/19.22  tff(f_102, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 27.58/19.22  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 27.58/19.22  tff(f_65, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 27.58/19.22  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 27.58/19.22  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 27.58/19.22  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 27.58/19.22  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 27.58/19.22  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.58/19.22  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 27.58/19.22  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 27.58/19.22  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 27.58/19.22  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 27.58/19.22  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 27.58/19.22  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t170_relat_1)).
% 27.58/19.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 27.58/19.22  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 27.58/19.22  tff(c_42, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 27.58/19.22  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 27.58/19.22  tff(c_28, plain, (![B_27, A_26]: (k2_relat_1(k7_relat_1(B_27, A_26))=k9_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_69])).
% 27.58/19.22  tff(c_26, plain, (![A_24, B_25]: (v1_relat_1(k7_relat_1(A_24, B_25)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 27.58/19.22  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.58/19.22  tff(c_32, plain, (![A_30]: (k10_relat_1(A_30, k2_relat_1(A_30))=k1_relat_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 27.58/19.22  tff(c_2226, plain, (![C_140, A_141, B_142]: (r1_tarski(k10_relat_1(C_140, A_141), k10_relat_1(C_140, B_142)) | ~r1_tarski(A_141, B_142) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_87])).
% 27.58/19.22  tff(c_20755, plain, (![A_341, B_342]: (r1_tarski(k1_relat_1(A_341), k10_relat_1(A_341, B_342)) | ~r1_tarski(k2_relat_1(A_341), B_342) | ~v1_relat_1(A_341) | ~v1_relat_1(A_341))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2226])).
% 27.58/19.22  tff(c_30, plain, (![B_29, A_28]: (r1_tarski(k10_relat_1(B_29, A_28), k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 27.58/19.22  tff(c_339, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(B_71, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.58/19.22  tff(c_354, plain, (![B_29, A_28]: (k10_relat_1(B_29, A_28)=k1_relat_1(B_29) | ~r1_tarski(k1_relat_1(B_29), k10_relat_1(B_29, A_28)) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_30, c_339])).
% 27.58/19.22  tff(c_36100, plain, (![A_491, B_492]: (k10_relat_1(A_491, B_492)=k1_relat_1(A_491) | ~r1_tarski(k2_relat_1(A_491), B_492) | ~v1_relat_1(A_491))), inference(resolution, [status(thm)], [c_20755, c_354])).
% 27.58/19.22  tff(c_101847, plain, (![A_988, B_989]: (k10_relat_1(A_988, k2_xboole_0(k2_relat_1(A_988), B_989))=k1_relat_1(A_988) | ~v1_relat_1(A_988))), inference(resolution, [status(thm)], [c_20, c_36100])).
% 27.58/19.22  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.58/19.22  tff(c_177, plain, (![A_59, B_60]: (k2_xboole_0(A_59, B_60)=B_60 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 27.58/19.22  tff(c_197, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_177])).
% 27.58/19.22  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 27.58/19.22  tff(c_391, plain, (![A_76, C_77, B_78]: (r1_tarski(A_76, C_77) | ~r1_tarski(k2_xboole_0(A_76, B_78), C_77))), inference(cnfTransformation, [status(thm)], [f_41])).
% 27.58/19.22  tff(c_6948, plain, (![A_212, C_213, B_214, B_215]: (r1_tarski(A_212, k2_xboole_0(C_213, B_214)) | ~r1_tarski(k2_xboole_0(A_212, B_215), B_214))), inference(resolution, [status(thm)], [c_10, c_391])).
% 27.58/19.22  tff(c_7006, plain, (![A_216, C_217, B_218]: (r1_tarski(A_216, k2_xboole_0(C_217, k2_xboole_0(A_216, B_218))))), inference(resolution, [status(thm)], [c_8, c_6948])).
% 27.58/19.22  tff(c_7102, plain, (![B_4, C_217]: (r1_tarski(B_4, k2_xboole_0(C_217, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_7006])).
% 27.58/19.22  tff(c_44, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 27.58/19.22  tff(c_196, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_177])).
% 27.58/19.22  tff(c_401, plain, (![C_77]: (r1_tarski('#skF_1', C_77) | ~r1_tarski(k1_relat_1('#skF_2'), C_77))), inference(superposition, [status(thm), theory('equality')], [c_196, c_391])).
% 27.58/19.22  tff(c_20768, plain, (![B_342]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', B_342)) | ~r1_tarski(k2_relat_1('#skF_2'), B_342) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_20755, c_401])).
% 27.58/19.22  tff(c_24874, plain, (![B_393]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', B_393)) | ~r1_tarski(k2_relat_1('#skF_2'), B_393))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_20768])).
% 27.58/19.22  tff(c_24951, plain, (![C_394]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_xboole_0(C_394, k2_relat_1('#skF_2')))))), inference(resolution, [status(thm)], [c_7102, c_24874])).
% 27.58/19.22  tff(c_18, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 27.58/19.22  tff(c_73377, plain, (![C_800]: (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_xboole_0(C_800, k2_relat_1('#skF_2'))))='#skF_1')), inference(resolution, [status(thm)], [c_24951, c_18])).
% 27.58/19.22  tff(c_40, plain, (![A_38, C_40, B_39]: (k3_xboole_0(A_38, k10_relat_1(C_40, B_39))=k10_relat_1(k7_relat_1(C_40, A_38), B_39) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_95])).
% 27.58/19.22  tff(c_73602, plain, (![C_800]: (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_xboole_0(C_800, k2_relat_1('#skF_2')))='#skF_1' | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_73377, c_40])).
% 27.58/19.22  tff(c_73765, plain, (![C_800]: (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_xboole_0(C_800, k2_relat_1('#skF_2')))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_73602])).
% 27.58/19.22  tff(c_101919, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_101847, c_73765])).
% 27.58/19.22  tff(c_102217, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_101919])).
% 27.58/19.22  tff(c_102220, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_102217])).
% 27.58/19.22  tff(c_102224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_102220])).
% 27.58/19.22  tff(c_102226, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_101919])).
% 27.58/19.22  tff(c_102225, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(splitRight, [status(thm)], [c_101919])).
% 27.58/19.22  tff(c_25029, plain, (![B_395]: (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_xboole_0(k2_relat_1('#skF_2'), B_395))))), inference(resolution, [status(thm)], [c_20, c_24874])).
% 27.58/19.22  tff(c_75541, plain, (![B_811]: (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_xboole_0(k2_relat_1('#skF_2'), B_811)))='#skF_1')), inference(resolution, [status(thm)], [c_25029, c_18])).
% 27.58/19.22  tff(c_75769, plain, (![B_811]: (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_xboole_0(k2_relat_1('#skF_2'), B_811))='#skF_1' | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_75541, c_40])).
% 27.58/19.22  tff(c_75936, plain, (![B_811]: (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_xboole_0(k2_relat_1('#skF_2'), B_811))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_75769])).
% 27.58/19.22  tff(c_849, plain, (![B_104, A_105]: (r1_tarski(k10_relat_1(B_104, A_105), k10_relat_1(B_104, k2_relat_1(B_104))) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_81])).
% 27.58/19.22  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 27.58/19.22  tff(c_22050, plain, (![B_362, A_363]: (k10_relat_1(B_362, k2_relat_1(B_362))=k10_relat_1(B_362, A_363) | ~r1_tarski(k10_relat_1(B_362, k2_relat_1(B_362)), k10_relat_1(B_362, A_363)) | ~v1_relat_1(B_362))), inference(resolution, [status(thm)], [c_849, c_4])).
% 27.58/19.22  tff(c_117630, plain, (![A_1079, A_1080]: (k10_relat_1(A_1079, k2_relat_1(A_1079))=k10_relat_1(A_1079, A_1080) | ~r1_tarski(k1_relat_1(A_1079), k10_relat_1(A_1079, A_1080)) | ~v1_relat_1(A_1079) | ~v1_relat_1(A_1079))), inference(superposition, [status(thm), theory('equality')], [c_32, c_22050])).
% 27.58/19.22  tff(c_117666, plain, (![B_811]: (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_xboole_0(k2_relat_1('#skF_2'), B_811))=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_75936, c_117630])).
% 27.58/19.22  tff(c_117712, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102226, c_102226, c_8, c_102225, c_75936, c_117666])).
% 27.58/19.22  tff(c_1748, plain, (![A_131, C_132, B_133]: (k3_xboole_0(A_131, k10_relat_1(C_132, B_133))=k10_relat_1(k7_relat_1(C_132, A_131), B_133) | ~v1_relat_1(C_132))), inference(cnfTransformation, [status(thm)], [f_95])).
% 27.58/19.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.58/19.22  tff(c_10452, plain, (![C_253, B_254, A_255]: (k3_xboole_0(k10_relat_1(C_253, B_254), A_255)=k10_relat_1(k7_relat_1(C_253, A_255), B_254) | ~v1_relat_1(C_253))), inference(superposition, [status(thm), theory('equality')], [c_1748, c_2])).
% 27.58/19.22  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k3_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.58/19.22  tff(c_10621, plain, (![C_253, A_255, B_254]: (r1_tarski(k10_relat_1(k7_relat_1(C_253, A_255), B_254), k10_relat_1(C_253, B_254)) | ~v1_relat_1(C_253))), inference(superposition, [status(thm), theory('equality')], [c_10452, c_16])).
% 27.58/19.22  tff(c_117856, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_117712, c_10621])).
% 27.58/19.22  tff(c_118041, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_117856])).
% 27.58/19.22  tff(c_118147, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28, c_118041])).
% 27.58/19.22  tff(c_118169, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_118147])).
% 27.58/19.22  tff(c_118171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_118169])).
% 27.58/19.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.58/19.22  
% 27.58/19.22  Inference rules
% 27.58/19.22  ----------------------
% 27.58/19.22  #Ref     : 0
% 27.58/19.22  #Sup     : 30244
% 27.58/19.22  #Fact    : 0
% 27.58/19.22  #Define  : 0
% 27.58/19.22  #Split   : 3
% 27.58/19.22  #Chain   : 0
% 27.58/19.22  #Close   : 0
% 27.58/19.22  
% 27.58/19.22  Ordering : KBO
% 27.58/19.22  
% 27.58/19.22  Simplification rules
% 27.58/19.22  ----------------------
% 27.58/19.22  #Subsume      : 5294
% 27.58/19.22  #Demod        : 18646
% 27.58/19.22  #Tautology    : 13667
% 27.58/19.22  #SimpNegUnit  : 1
% 27.58/19.22  #BackRed      : 16
% 27.58/19.22  
% 27.58/19.22  #Partial instantiations: 0
% 27.58/19.22  #Strategies tried      : 1
% 27.58/19.22  
% 27.58/19.22  Timing (in seconds)
% 27.58/19.22  ----------------------
% 27.58/19.23  Preprocessing        : 0.31
% 27.58/19.23  Parsing              : 0.17
% 27.58/19.23  CNF conversion       : 0.02
% 27.58/19.23  Main loop            : 18.13
% 27.58/19.23  Inferencing          : 1.91
% 27.58/19.23  Reduction            : 10.01
% 27.58/19.23  Demodulation         : 9.07
% 27.58/19.23  BG Simplification    : 0.26
% 27.58/19.23  Subsumption          : 5.10
% 27.58/19.23  Abstraction          : 0.42
% 27.58/19.23  MUC search           : 0.00
% 27.58/19.23  Cooper               : 0.00
% 27.58/19.23  Total                : 18.48
% 27.58/19.23  Index Insertion      : 0.00
% 27.58/19.23  Index Deletion       : 0.00
% 27.58/19.23  Index Matching       : 0.00
% 27.58/19.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
