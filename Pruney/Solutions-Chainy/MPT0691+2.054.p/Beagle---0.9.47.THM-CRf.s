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
% DateTime   : Thu Dec  3 10:04:46 EST 2020

% Result     : Theorem 29.45s
% Output     : CNFRefutation 29.45s
% Verified   : 
% Statistics : Number of formulae       :  119 (3412 expanded)
%              Number of leaves         :   29 (1192 expanded)
%              Depth                    :   27
%              Number of atoms          :  246 (6685 expanded)
%              Number of equality atoms :   49 (1902 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_65,plain,(
    ! [A_35] :
      ( k7_relat_1(A_35,k1_relat_1(A_35)) = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_77,plain,(
    ! [A_19] :
      ( k7_relat_1(k6_relat_1(A_19),A_19) = k6_relat_1(A_19)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_65])).

tff(c_81,plain,(
    ! [A_19] : k7_relat_1(k6_relat_1(A_19),A_19) = k6_relat_1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_891,plain,(
    ! [A_98,B_99] :
      ( k7_relat_1(A_98,k1_relat_1(k7_relat_1(B_99,k1_relat_1(A_98)))) = k7_relat_1(A_98,k1_relat_1(B_99))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_951,plain,(
    ! [A_19,B_99] :
      ( k7_relat_1(k6_relat_1(A_19),k1_relat_1(k7_relat_1(B_99,A_19))) = k7_relat_1(k6_relat_1(A_19),k1_relat_1(B_99))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_891])).

tff(c_2250,plain,(
    ! [A_168,B_169] :
      ( k7_relat_1(k6_relat_1(A_168),k1_relat_1(k7_relat_1(B_169,A_168))) = k7_relat_1(k6_relat_1(A_168),k1_relat_1(B_169))
      | ~ v1_relat_1(B_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_951])).

tff(c_2322,plain,(
    ! [A_168,B_169] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_168),k1_relat_1(B_169)))
      | ~ v1_relat_1(k6_relat_1(A_168))
      | ~ v1_relat_1(B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2250,c_12])).

tff(c_2389,plain,(
    ! [A_170,B_171] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_170),k1_relat_1(B_171)))
      | ~ v1_relat_1(B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2322])).

tff(c_2417,plain,(
    ! [A_170,A_19] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_170),A_19))
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2389])).

tff(c_2425,plain,(
    ! [A_170,A_19] : v1_relat_1(k7_relat_1(k6_relat_1(A_170),A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2417])).

tff(c_32,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_25,A_24)),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4104,plain,(
    ! [A_241,B_242] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_241,k1_relat_1(B_242))),k1_relat_1(k7_relat_1(B_242,k1_relat_1(A_241))))
      | ~ v1_relat_1(A_241)
      | ~ v1_relat_1(B_242)
      | ~ v1_relat_1(A_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_891,c_32])).

tff(c_171,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(A_49,C_50)
      | ~ r1_tarski(B_51,C_50)
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_184,plain,(
    ! [A_49,A_24,B_25] :
      ( r1_tarski(A_49,A_24)
      | ~ r1_tarski(A_49,k1_relat_1(k7_relat_1(B_25,A_24)))
      | ~ v1_relat_1(B_25) ) ),
    inference(resolution,[status(thm)],[c_32,c_171])).

tff(c_4491,plain,(
    ! [A_245,B_246] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_245,k1_relat_1(B_246))),k1_relat_1(A_245))
      | ~ v1_relat_1(B_246)
      | ~ v1_relat_1(A_245) ) ),
    inference(resolution,[status(thm)],[c_4104,c_184])).

tff(c_4549,plain,(
    ! [A_245,A_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_245,A_19)),k1_relat_1(A_245))
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(A_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4491])).

tff(c_4603,plain,(
    ! [A_248,A_249] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_248,A_249)),k1_relat_1(A_248))
      | ~ v1_relat_1(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4549])).

tff(c_4652,plain,(
    ! [A_19,A_249] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_19),A_249)),A_19)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4603])).

tff(c_4675,plain,(
    ! [A_250,A_251] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_250),A_251)),A_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4652])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_relat_1(A_26),B_27) = k7_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_40,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_185,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_49,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_40,c_171])).

tff(c_254,plain,(
    ! [A_60,B_61] :
      ( k5_relat_1(k6_relat_1(A_60),B_61) = B_61
      | ~ r1_tarski(k1_relat_1(B_61),A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_640,plain,(
    ! [B_84] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),B_84) = B_84
      | ~ v1_relat_1(B_84)
      | ~ r1_tarski(k1_relat_1(B_84),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_185,c_254])).

tff(c_684,plain,(
    ! [B_27] :
      ( k7_relat_1(B_27,k1_relat_1('#skF_2')) = B_27
      | ~ v1_relat_1(B_27)
      | ~ r1_tarski(k1_relat_1(B_27),'#skF_1')
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_640])).

tff(c_4679,plain,(
    ! [A_251] :
      ( k7_relat_1(k7_relat_1(k6_relat_1('#skF_1'),A_251),k1_relat_1('#skF_2')) = k7_relat_1(k6_relat_1('#skF_1'),A_251)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1('#skF_1'),A_251)) ) ),
    inference(resolution,[status(thm)],[c_4675,c_684])).

tff(c_6328,plain,(
    ! [A_280] : k7_relat_1(k7_relat_1(k6_relat_1('#skF_1'),A_280),k1_relat_1('#skF_2')) = k7_relat_1(k6_relat_1('#skF_1'),A_280) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2425,c_4679])).

tff(c_6425,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k7_relat_1(k6_relat_1('#skF_1'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_6328])).

tff(c_6485,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),k1_relat_1('#skF_2')) = k6_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_6425])).

tff(c_924,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k1_relat_1(k7_relat_1(A_98,k1_relat_1(B_99))),k1_relat_1(k7_relat_1(B_99,k1_relat_1(A_98))))
      | ~ v1_relat_1(A_98)
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_891,c_32])).

tff(c_6524,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1('#skF_1')),k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(k6_relat_1('#skF_1')))))
    | ~ v1_relat_1(k6_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6485,c_924])).

tff(c_6662,plain,(
    r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_42,c_10,c_22,c_22,c_6524])).

tff(c_107,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_39,A_40)),A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [B_39,A_40] :
      ( k1_relat_1(k7_relat_1(B_39,A_40)) = A_40
      | ~ r1_tarski(A_40,k1_relat_1(k7_relat_1(B_39,A_40)))
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_6723,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6662,c_116])).

tff(c_6742,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6723])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [A_28] :
      ( k7_relat_1(A_28,k1_relat_1(A_28)) = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1439,plain,(
    ! [B_133,A_134] :
      ( k1_relat_1(k7_relat_1(B_133,A_134)) = A_134
      | ~ r1_tarski(A_134,k1_relat_1(k7_relat_1(B_133,A_134)))
      | ~ v1_relat_1(B_133) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_1451,plain,(
    ! [A_28] :
      ( k1_relat_1(k7_relat_1(A_28,k1_relat_1(A_28))) = k1_relat_1(A_28)
      | ~ r1_tarski(k1_relat_1(A_28),k1_relat_1(A_28))
      | ~ v1_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1439])).

tff(c_1457,plain,(
    ! [A_28] :
      ( k1_relat_1(k7_relat_1(A_28,k1_relat_1(A_28))) = k1_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1451])).

tff(c_6812,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6742,c_1457])).

tff(c_6863,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6742,c_6812])).

tff(c_21677,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6863])).

tff(c_21680,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_21677])).

tff(c_21684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_21680])).

tff(c_21686,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6863])).

tff(c_264,plain,(
    ! [A_60,A_19] :
      ( k5_relat_1(k6_relat_1(A_60),k6_relat_1(A_19)) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_60)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_254])).

tff(c_360,plain,(
    ! [A_66,A_67] :
      ( k5_relat_1(k6_relat_1(A_66),k6_relat_1(A_67)) = k6_relat_1(A_67)
      | ~ r1_tarski(A_67,A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_264])).

tff(c_374,plain,(
    ! [A_67,A_66] :
      ( k7_relat_1(k6_relat_1(A_67),A_66) = k6_relat_1(A_67)
      | ~ v1_relat_1(k6_relat_1(A_67))
      | ~ r1_tarski(A_67,A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_34])).

tff(c_403,plain,(
    ! [A_67,A_66] :
      ( k7_relat_1(k6_relat_1(A_67),A_66) = k6_relat_1(A_67)
      | ~ r1_tarski(A_67,A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_374])).

tff(c_2319,plain,(
    ! [A_168,B_169] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_168),k1_relat_1(B_169))),k1_relat_1(k7_relat_1(B_169,A_168)))
      | ~ v1_relat_1(k6_relat_1(A_168))
      | ~ v1_relat_1(B_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2250,c_32])).

tff(c_9170,plain,(
    ! [A_317,B_318] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_317),k1_relat_1(B_318))),k1_relat_1(k7_relat_1(B_318,A_317)))
      | ~ v1_relat_1(B_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2319])).

tff(c_9266,plain,(
    ! [A_67,B_318] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_67)),k1_relat_1(k7_relat_1(B_318,A_67)))
      | ~ v1_relat_1(B_318)
      | ~ r1_tarski(A_67,k1_relat_1(B_318)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_9170])).

tff(c_22343,plain,(
    ! [A_476,B_477] :
      ( r1_tarski(A_476,k1_relat_1(k7_relat_1(B_477,A_476)))
      | ~ v1_relat_1(B_477)
      | ~ r1_tarski(A_476,k1_relat_1(B_477)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_9266])).

tff(c_22756,plain,(
    ! [B_480,A_481] :
      ( k1_relat_1(k7_relat_1(B_480,A_481)) = A_481
      | ~ v1_relat_1(B_480)
      | ~ r1_tarski(A_481,k1_relat_1(B_480)) ) ),
    inference(resolution,[status(thm)],[c_22343,c_116])).

tff(c_22918,plain,(
    ! [A_481] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_481)) = A_481
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ r1_tarski(A_481,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6742,c_22756])).

tff(c_23175,plain,(
    ! [A_482] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_482)) = A_482
      | ~ r1_tarski(A_482,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21686,c_22918])).

tff(c_4172,plain,(
    ! [B_242] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k1_relat_1(B_242))),k1_relat_1(k7_relat_1(B_242,k1_relat_1(k6_relat_1(k1_relat_1(B_242))))))
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(B_242)))
      | ~ v1_relat_1(B_242)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(B_242))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_4104])).

tff(c_4221,plain,(
    ! [B_243] :
      ( r1_tarski(k1_relat_1(B_243),k1_relat_1(k7_relat_1(B_243,k1_relat_1(B_243))))
      | ~ v1_relat_1(B_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_22,c_22,c_4172])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( k5_relat_1(k6_relat_1(A_22),B_23) = B_23
      | ~ r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4296,plain,(
    ! [B_243] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(B_243,k1_relat_1(B_243)))),B_243) = B_243
      | ~ v1_relat_1(B_243) ) ),
    inference(resolution,[status(thm)],[c_4221,c_30])).

tff(c_23290,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_2','#skF_1'))),k7_relat_1('#skF_2','#skF_1')) = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_23175,c_4296])).

tff(c_23432,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),k7_relat_1('#skF_2','#skF_1')) = k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6742,c_21686,c_6742,c_23290])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_20),B_21),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_846,plain,(
    ! [A_95,B_96,A_97] :
      ( r1_tarski(A_95,B_96)
      | ~ r1_tarski(A_95,k5_relat_1(k6_relat_1(A_97),B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_26,c_171])).

tff(c_31015,plain,(
    ! [A_558,A_559,B_560] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_558),k5_relat_1(k6_relat_1(A_559),B_560)),B_560)
      | ~ v1_relat_1(B_560)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_559),B_560)) ) ),
    inference(resolution,[status(thm)],[c_26,c_846])).

tff(c_31119,plain,(
    ! [A_558] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_558),k7_relat_1('#skF_2','#skF_1')),k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'),k7_relat_1('#skF_2','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23432,c_31015])).

tff(c_31249,plain,(
    ! [A_561] : r1_tarski(k5_relat_1(k6_relat_1(A_561),k7_relat_1('#skF_2','#skF_1')),k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21686,c_23432,c_21686,c_31119])).

tff(c_203,plain,(
    ! [A_54,B_55] :
      ( k5_relat_1(k6_relat_1(A_54),B_55) = k7_relat_1(B_55,A_54)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_238,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k7_relat_1(B_58,A_59),B_58)
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_26])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_249,plain,(
    ! [A_3,B_58,A_59] :
      ( r1_tarski(A_3,B_58)
      | ~ r1_tarski(A_3,k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_238,c_8])).

tff(c_31262,plain,(
    ! [A_561] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_561),k7_relat_1('#skF_2','#skF_1')),'#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_31249,c_249])).

tff(c_31329,plain,(
    ! [A_562] : r1_tarski(k5_relat_1(k6_relat_1(A_562),k7_relat_1('#skF_2','#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_31262])).

tff(c_31345,plain,(
    r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_23432,c_31329])).

tff(c_151,plain,(
    ! [B_47,A_48] :
      ( k2_relat_1(k7_relat_1(B_47,A_48)) = k9_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_11] :
      ( k10_relat_1(A_11,k2_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_157,plain,(
    ! [B_47,A_48] :
      ( k10_relat_1(k7_relat_1(B_47,A_48),k9_relat_1(B_47,A_48)) = k1_relat_1(k7_relat_1(B_47,A_48))
      | ~ v1_relat_1(k7_relat_1(B_47,A_48))
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_16])).

tff(c_517,plain,(
    ! [B_74,A_75,C_76] :
      ( r1_tarski(k10_relat_1(B_74,A_75),k10_relat_1(C_76,A_75))
      | ~ r1_tarski(B_74,C_76)
      | ~ v1_relat_1(C_76)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5930,plain,(
    ! [A_271,C_272,A_273,B_274] :
      ( r1_tarski(A_271,k10_relat_1(C_272,A_273))
      | ~ r1_tarski(A_271,k10_relat_1(B_274,A_273))
      | ~ r1_tarski(B_274,C_272)
      | ~ v1_relat_1(C_272)
      | ~ v1_relat_1(B_274) ) ),
    inference(resolution,[status(thm)],[c_517,c_8])).

tff(c_83802,plain,(
    ! [A_1024,C_1025,B_1026,A_1027] :
      ( r1_tarski(A_1024,k10_relat_1(C_1025,k9_relat_1(B_1026,A_1027)))
      | ~ r1_tarski(A_1024,k1_relat_1(k7_relat_1(B_1026,A_1027)))
      | ~ r1_tarski(k7_relat_1(B_1026,A_1027),C_1025)
      | ~ v1_relat_1(C_1025)
      | ~ v1_relat_1(k7_relat_1(B_1026,A_1027))
      | ~ v1_relat_1(k7_relat_1(B_1026,A_1027))
      | ~ v1_relat_1(B_1026) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_5930])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_83877,plain,
    ( ~ r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_83802,c_38])).

tff(c_83962,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_21686,c_31345,c_6,c_6742,c_83877])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:35:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.45/18.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.45/18.64  
% 29.45/18.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.45/18.64  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 29.45/18.64  
% 29.45/18.64  %Foreground sorts:
% 29.45/18.64  
% 29.45/18.64  
% 29.45/18.64  %Background operators:
% 29.45/18.64  
% 29.45/18.64  
% 29.45/18.64  %Foreground operators:
% 29.45/18.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.45/18.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 29.45/18.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 29.45/18.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.45/18.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 29.45/18.64  tff('#skF_2', type, '#skF_2': $i).
% 29.45/18.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 29.45/18.64  tff('#skF_1', type, '#skF_1': $i).
% 29.45/18.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.45/18.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 29.45/18.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.45/18.64  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 29.45/18.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.45/18.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 29.45/18.64  
% 29.45/18.67  tff(f_102, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 29.45/18.67  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 29.45/18.67  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 29.45/18.67  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 29.45/18.67  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 29.45/18.67  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 29.45/18.67  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 29.45/18.67  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 29.45/18.67  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 29.45/18.67  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 29.45/18.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 29.45/18.67  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 29.45/18.67  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 29.45/18.67  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 29.45/18.67  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t179_relat_1)).
% 29.45/18.67  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 29.45/18.67  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.45/18.67  tff(c_10, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 29.45/18.67  tff(c_22, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_71])).
% 29.45/18.67  tff(c_65, plain, (![A_35]: (k7_relat_1(A_35, k1_relat_1(A_35))=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_95])).
% 29.45/18.67  tff(c_77, plain, (![A_19]: (k7_relat_1(k6_relat_1(A_19), A_19)=k6_relat_1(A_19) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_65])).
% 29.45/18.67  tff(c_81, plain, (![A_19]: (k7_relat_1(k6_relat_1(A_19), A_19)=k6_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_77])).
% 29.45/18.67  tff(c_891, plain, (![A_98, B_99]: (k7_relat_1(A_98, k1_relat_1(k7_relat_1(B_99, k1_relat_1(A_98))))=k7_relat_1(A_98, k1_relat_1(B_99)) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_67])).
% 29.45/18.67  tff(c_951, plain, (![A_19, B_99]: (k7_relat_1(k6_relat_1(A_19), k1_relat_1(k7_relat_1(B_99, A_19)))=k7_relat_1(k6_relat_1(A_19), k1_relat_1(B_99)) | ~v1_relat_1(B_99) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_891])).
% 29.45/18.67  tff(c_2250, plain, (![A_168, B_169]: (k7_relat_1(k6_relat_1(A_168), k1_relat_1(k7_relat_1(B_169, A_168)))=k7_relat_1(k6_relat_1(A_168), k1_relat_1(B_169)) | ~v1_relat_1(B_169))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_951])).
% 29.45/18.67  tff(c_2322, plain, (![A_168, B_169]: (v1_relat_1(k7_relat_1(k6_relat_1(A_168), k1_relat_1(B_169))) | ~v1_relat_1(k6_relat_1(A_168)) | ~v1_relat_1(B_169))), inference(superposition, [status(thm), theory('equality')], [c_2250, c_12])).
% 29.45/18.67  tff(c_2389, plain, (![A_170, B_171]: (v1_relat_1(k7_relat_1(k6_relat_1(A_170), k1_relat_1(B_171))) | ~v1_relat_1(B_171))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2322])).
% 29.45/18.67  tff(c_2417, plain, (![A_170, A_19]: (v1_relat_1(k7_relat_1(k6_relat_1(A_170), A_19)) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2389])).
% 29.45/18.67  tff(c_2425, plain, (![A_170, A_19]: (v1_relat_1(k7_relat_1(k6_relat_1(A_170), A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2417])).
% 29.45/18.67  tff(c_32, plain, (![B_25, A_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_25, A_24)), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_87])).
% 29.45/18.67  tff(c_4104, plain, (![A_241, B_242]: (r1_tarski(k1_relat_1(k7_relat_1(A_241, k1_relat_1(B_242))), k1_relat_1(k7_relat_1(B_242, k1_relat_1(A_241)))) | ~v1_relat_1(A_241) | ~v1_relat_1(B_242) | ~v1_relat_1(A_241))), inference(superposition, [status(thm), theory('equality')], [c_891, c_32])).
% 29.45/18.67  tff(c_171, plain, (![A_49, C_50, B_51]: (r1_tarski(A_49, C_50) | ~r1_tarski(B_51, C_50) | ~r1_tarski(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.45/18.67  tff(c_184, plain, (![A_49, A_24, B_25]: (r1_tarski(A_49, A_24) | ~r1_tarski(A_49, k1_relat_1(k7_relat_1(B_25, A_24))) | ~v1_relat_1(B_25))), inference(resolution, [status(thm)], [c_32, c_171])).
% 29.45/18.67  tff(c_4491, plain, (![A_245, B_246]: (r1_tarski(k1_relat_1(k7_relat_1(A_245, k1_relat_1(B_246))), k1_relat_1(A_245)) | ~v1_relat_1(B_246) | ~v1_relat_1(A_245))), inference(resolution, [status(thm)], [c_4104, c_184])).
% 29.45/18.67  tff(c_4549, plain, (![A_245, A_19]: (r1_tarski(k1_relat_1(k7_relat_1(A_245, A_19)), k1_relat_1(A_245)) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(A_245))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4491])).
% 29.45/18.67  tff(c_4603, plain, (![A_248, A_249]: (r1_tarski(k1_relat_1(k7_relat_1(A_248, A_249)), k1_relat_1(A_248)) | ~v1_relat_1(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4549])).
% 29.45/18.67  tff(c_4652, plain, (![A_19, A_249]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_19), A_249)), A_19) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4603])).
% 29.45/18.67  tff(c_4675, plain, (![A_250, A_251]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_250), A_251)), A_250))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4652])).
% 29.45/18.67  tff(c_34, plain, (![A_26, B_27]: (k5_relat_1(k6_relat_1(A_26), B_27)=k7_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_91])).
% 29.45/18.67  tff(c_40, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 29.45/18.67  tff(c_185, plain, (![A_49]: (r1_tarski(A_49, k1_relat_1('#skF_2')) | ~r1_tarski(A_49, '#skF_1'))), inference(resolution, [status(thm)], [c_40, c_171])).
% 29.45/18.67  tff(c_254, plain, (![A_60, B_61]: (k5_relat_1(k6_relat_1(A_60), B_61)=B_61 | ~r1_tarski(k1_relat_1(B_61), A_60) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_83])).
% 29.45/18.67  tff(c_640, plain, (![B_84]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), B_84)=B_84 | ~v1_relat_1(B_84) | ~r1_tarski(k1_relat_1(B_84), '#skF_1'))), inference(resolution, [status(thm)], [c_185, c_254])).
% 29.45/18.67  tff(c_684, plain, (![B_27]: (k7_relat_1(B_27, k1_relat_1('#skF_2'))=B_27 | ~v1_relat_1(B_27) | ~r1_tarski(k1_relat_1(B_27), '#skF_1') | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_34, c_640])).
% 29.45/18.67  tff(c_4679, plain, (![A_251]: (k7_relat_1(k7_relat_1(k6_relat_1('#skF_1'), A_251), k1_relat_1('#skF_2'))=k7_relat_1(k6_relat_1('#skF_1'), A_251) | ~v1_relat_1(k7_relat_1(k6_relat_1('#skF_1'), A_251)))), inference(resolution, [status(thm)], [c_4675, c_684])).
% 29.45/18.67  tff(c_6328, plain, (![A_280]: (k7_relat_1(k7_relat_1(k6_relat_1('#skF_1'), A_280), k1_relat_1('#skF_2'))=k7_relat_1(k6_relat_1('#skF_1'), A_280))), inference(demodulation, [status(thm), theory('equality')], [c_2425, c_4679])).
% 29.45/18.67  tff(c_6425, plain, (k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k7_relat_1(k6_relat_1('#skF_1'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_81, c_6328])).
% 29.45/18.67  tff(c_6485, plain, (k7_relat_1(k6_relat_1('#skF_1'), k1_relat_1('#skF_2'))=k6_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_6425])).
% 29.45/18.67  tff(c_924, plain, (![A_98, B_99]: (r1_tarski(k1_relat_1(k7_relat_1(A_98, k1_relat_1(B_99))), k1_relat_1(k7_relat_1(B_99, k1_relat_1(A_98)))) | ~v1_relat_1(A_98) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_891, c_32])).
% 29.45/18.67  tff(c_6524, plain, (r1_tarski(k1_relat_1(k6_relat_1('#skF_1')), k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(k6_relat_1('#skF_1'))))) | ~v1_relat_1(k6_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6485, c_924])).
% 29.45/18.67  tff(c_6662, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_42, c_10, c_22, c_22, c_6524])).
% 29.45/18.67  tff(c_107, plain, (![B_39, A_40]: (r1_tarski(k1_relat_1(k7_relat_1(B_39, A_40)), A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_87])).
% 29.45/18.67  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.45/18.67  tff(c_116, plain, (![B_39, A_40]: (k1_relat_1(k7_relat_1(B_39, A_40))=A_40 | ~r1_tarski(A_40, k1_relat_1(k7_relat_1(B_39, A_40))) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_107, c_2])).
% 29.45/18.67  tff(c_6723, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6662, c_116])).
% 29.45/18.67  tff(c_6742, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6723])).
% 29.45/18.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.45/18.67  tff(c_36, plain, (![A_28]: (k7_relat_1(A_28, k1_relat_1(A_28))=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_95])).
% 29.45/18.67  tff(c_1439, plain, (![B_133, A_134]: (k1_relat_1(k7_relat_1(B_133, A_134))=A_134 | ~r1_tarski(A_134, k1_relat_1(k7_relat_1(B_133, A_134))) | ~v1_relat_1(B_133))), inference(resolution, [status(thm)], [c_107, c_2])).
% 29.45/18.67  tff(c_1451, plain, (![A_28]: (k1_relat_1(k7_relat_1(A_28, k1_relat_1(A_28)))=k1_relat_1(A_28) | ~r1_tarski(k1_relat_1(A_28), k1_relat_1(A_28)) | ~v1_relat_1(A_28) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1439])).
% 29.45/18.67  tff(c_1457, plain, (![A_28]: (k1_relat_1(k7_relat_1(A_28, k1_relat_1(A_28)))=k1_relat_1(A_28) | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1451])).
% 29.45/18.67  tff(c_6812, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6742, c_1457])).
% 29.45/18.67  tff(c_6863, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6742, c_6812])).
% 29.45/18.67  tff(c_21677, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_6863])).
% 29.45/18.67  tff(c_21680, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_21677])).
% 29.45/18.67  tff(c_21684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_21680])).
% 29.45/18.67  tff(c_21686, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_6863])).
% 29.45/18.67  tff(c_264, plain, (![A_60, A_19]: (k5_relat_1(k6_relat_1(A_60), k6_relat_1(A_19))=k6_relat_1(A_19) | ~r1_tarski(A_19, A_60) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_254])).
% 29.45/18.67  tff(c_360, plain, (![A_66, A_67]: (k5_relat_1(k6_relat_1(A_66), k6_relat_1(A_67))=k6_relat_1(A_67) | ~r1_tarski(A_67, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_264])).
% 29.45/18.67  tff(c_374, plain, (![A_67, A_66]: (k7_relat_1(k6_relat_1(A_67), A_66)=k6_relat_1(A_67) | ~v1_relat_1(k6_relat_1(A_67)) | ~r1_tarski(A_67, A_66))), inference(superposition, [status(thm), theory('equality')], [c_360, c_34])).
% 29.45/18.67  tff(c_403, plain, (![A_67, A_66]: (k7_relat_1(k6_relat_1(A_67), A_66)=k6_relat_1(A_67) | ~r1_tarski(A_67, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_374])).
% 29.45/18.67  tff(c_2319, plain, (![A_168, B_169]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_168), k1_relat_1(B_169))), k1_relat_1(k7_relat_1(B_169, A_168))) | ~v1_relat_1(k6_relat_1(A_168)) | ~v1_relat_1(B_169))), inference(superposition, [status(thm), theory('equality')], [c_2250, c_32])).
% 29.45/18.67  tff(c_9170, plain, (![A_317, B_318]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_317), k1_relat_1(B_318))), k1_relat_1(k7_relat_1(B_318, A_317))) | ~v1_relat_1(B_318))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2319])).
% 29.45/18.67  tff(c_9266, plain, (![A_67, B_318]: (r1_tarski(k1_relat_1(k6_relat_1(A_67)), k1_relat_1(k7_relat_1(B_318, A_67))) | ~v1_relat_1(B_318) | ~r1_tarski(A_67, k1_relat_1(B_318)))), inference(superposition, [status(thm), theory('equality')], [c_403, c_9170])).
% 29.45/18.67  tff(c_22343, plain, (![A_476, B_477]: (r1_tarski(A_476, k1_relat_1(k7_relat_1(B_477, A_476))) | ~v1_relat_1(B_477) | ~r1_tarski(A_476, k1_relat_1(B_477)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_9266])).
% 29.45/18.67  tff(c_22756, plain, (![B_480, A_481]: (k1_relat_1(k7_relat_1(B_480, A_481))=A_481 | ~v1_relat_1(B_480) | ~r1_tarski(A_481, k1_relat_1(B_480)))), inference(resolution, [status(thm)], [c_22343, c_116])).
% 29.45/18.67  tff(c_22918, plain, (![A_481]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_481))=A_481 | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~r1_tarski(A_481, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6742, c_22756])).
% 29.45/18.67  tff(c_23175, plain, (![A_482]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_482))=A_482 | ~r1_tarski(A_482, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_21686, c_22918])).
% 29.45/18.67  tff(c_4172, plain, (![B_242]: (r1_tarski(k1_relat_1(k6_relat_1(k1_relat_1(B_242))), k1_relat_1(k7_relat_1(B_242, k1_relat_1(k6_relat_1(k1_relat_1(B_242)))))) | ~v1_relat_1(k6_relat_1(k1_relat_1(B_242))) | ~v1_relat_1(B_242) | ~v1_relat_1(k6_relat_1(k1_relat_1(B_242))))), inference(superposition, [status(thm), theory('equality')], [c_81, c_4104])).
% 29.45/18.67  tff(c_4221, plain, (![B_243]: (r1_tarski(k1_relat_1(B_243), k1_relat_1(k7_relat_1(B_243, k1_relat_1(B_243)))) | ~v1_relat_1(B_243))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_22, c_22, c_4172])).
% 29.45/18.67  tff(c_30, plain, (![A_22, B_23]: (k5_relat_1(k6_relat_1(A_22), B_23)=B_23 | ~r1_tarski(k1_relat_1(B_23), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 29.45/18.67  tff(c_4296, plain, (![B_243]: (k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(B_243, k1_relat_1(B_243)))), B_243)=B_243 | ~v1_relat_1(B_243))), inference(resolution, [status(thm)], [c_4221, c_30])).
% 29.45/18.67  tff(c_23290, plain, (k5_relat_1(k6_relat_1(k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), k7_relat_1('#skF_2', '#skF_1'))=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_23175, c_4296])).
% 29.45/18.67  tff(c_23432, plain, (k5_relat_1(k6_relat_1('#skF_1'), k7_relat_1('#skF_2', '#skF_1'))=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6742, c_21686, c_6742, c_23290])).
% 29.45/18.67  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(k5_relat_1(k6_relat_1(A_20), B_21), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 29.45/18.67  tff(c_846, plain, (![A_95, B_96, A_97]: (r1_tarski(A_95, B_96) | ~r1_tarski(A_95, k5_relat_1(k6_relat_1(A_97), B_96)) | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_26, c_171])).
% 29.45/18.67  tff(c_31015, plain, (![A_558, A_559, B_560]: (r1_tarski(k5_relat_1(k6_relat_1(A_558), k5_relat_1(k6_relat_1(A_559), B_560)), B_560) | ~v1_relat_1(B_560) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_559), B_560)))), inference(resolution, [status(thm)], [c_26, c_846])).
% 29.45/18.67  tff(c_31119, plain, (![A_558]: (r1_tarski(k5_relat_1(k6_relat_1(A_558), k7_relat_1('#skF_2', '#skF_1')), k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k5_relat_1(k6_relat_1('#skF_1'), k7_relat_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_23432, c_31015])).
% 29.45/18.67  tff(c_31249, plain, (![A_561]: (r1_tarski(k5_relat_1(k6_relat_1(A_561), k7_relat_1('#skF_2', '#skF_1')), k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_21686, c_23432, c_21686, c_31119])).
% 29.45/18.67  tff(c_203, plain, (![A_54, B_55]: (k5_relat_1(k6_relat_1(A_54), B_55)=k7_relat_1(B_55, A_54) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_91])).
% 29.45/18.67  tff(c_238, plain, (![B_58, A_59]: (r1_tarski(k7_relat_1(B_58, A_59), B_58) | ~v1_relat_1(B_58) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_203, c_26])).
% 29.45/18.67  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 29.45/18.67  tff(c_249, plain, (![A_3, B_58, A_59]: (r1_tarski(A_3, B_58) | ~r1_tarski(A_3, k7_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_238, c_8])).
% 29.45/18.67  tff(c_31262, plain, (![A_561]: (r1_tarski(k5_relat_1(k6_relat_1(A_561), k7_relat_1('#skF_2', '#skF_1')), '#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_31249, c_249])).
% 29.45/18.67  tff(c_31329, plain, (![A_562]: (r1_tarski(k5_relat_1(k6_relat_1(A_562), k7_relat_1('#skF_2', '#skF_1')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_31262])).
% 29.45/18.67  tff(c_31345, plain, (r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_23432, c_31329])).
% 29.45/18.67  tff(c_151, plain, (![B_47, A_48]: (k2_relat_1(k7_relat_1(B_47, A_48))=k9_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 29.45/18.67  tff(c_16, plain, (![A_11]: (k10_relat_1(A_11, k2_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 29.45/18.67  tff(c_157, plain, (![B_47, A_48]: (k10_relat_1(k7_relat_1(B_47, A_48), k9_relat_1(B_47, A_48))=k1_relat_1(k7_relat_1(B_47, A_48)) | ~v1_relat_1(k7_relat_1(B_47, A_48)) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_151, c_16])).
% 29.45/18.67  tff(c_517, plain, (![B_74, A_75, C_76]: (r1_tarski(k10_relat_1(B_74, A_75), k10_relat_1(C_76, A_75)) | ~r1_tarski(B_74, C_76) | ~v1_relat_1(C_76) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_60])).
% 29.45/18.67  tff(c_5930, plain, (![A_271, C_272, A_273, B_274]: (r1_tarski(A_271, k10_relat_1(C_272, A_273)) | ~r1_tarski(A_271, k10_relat_1(B_274, A_273)) | ~r1_tarski(B_274, C_272) | ~v1_relat_1(C_272) | ~v1_relat_1(B_274))), inference(resolution, [status(thm)], [c_517, c_8])).
% 29.45/18.67  tff(c_83802, plain, (![A_1024, C_1025, B_1026, A_1027]: (r1_tarski(A_1024, k10_relat_1(C_1025, k9_relat_1(B_1026, A_1027))) | ~r1_tarski(A_1024, k1_relat_1(k7_relat_1(B_1026, A_1027))) | ~r1_tarski(k7_relat_1(B_1026, A_1027), C_1025) | ~v1_relat_1(C_1025) | ~v1_relat_1(k7_relat_1(B_1026, A_1027)) | ~v1_relat_1(k7_relat_1(B_1026, A_1027)) | ~v1_relat_1(B_1026))), inference(superposition, [status(thm), theory('equality')], [c_157, c_5930])).
% 29.45/18.67  tff(c_38, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 29.45/18.67  tff(c_83877, plain, (~r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_83802, c_38])).
% 29.45/18.67  tff(c_83962, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_21686, c_31345, c_6, c_6742, c_83877])).
% 29.45/18.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.45/18.67  
% 29.45/18.67  Inference rules
% 29.45/18.67  ----------------------
% 29.45/18.67  #Ref     : 0
% 29.45/18.67  #Sup     : 20121
% 29.45/18.67  #Fact    : 0
% 29.45/18.67  #Define  : 0
% 29.45/18.67  #Split   : 20
% 29.45/18.67  #Chain   : 0
% 29.45/18.67  #Close   : 0
% 29.45/18.67  
% 29.45/18.67  Ordering : KBO
% 29.45/18.67  
% 29.45/18.67  Simplification rules
% 29.45/18.67  ----------------------
% 29.45/18.67  #Subsume      : 4296
% 29.45/18.67  #Demod        : 19009
% 29.45/18.67  #Tautology    : 4824
% 29.45/18.67  #SimpNegUnit  : 9
% 29.45/18.67  #BackRed      : 5
% 29.45/18.67  
% 29.45/18.67  #Partial instantiations: 0
% 29.45/18.67  #Strategies tried      : 1
% 29.45/18.67  
% 29.45/18.67  Timing (in seconds)
% 29.45/18.67  ----------------------
% 29.45/18.67  Preprocessing        : 0.30
% 29.45/18.67  Parsing              : 0.16
% 29.45/18.67  CNF conversion       : 0.02
% 29.45/18.67  Main loop            : 17.60
% 29.45/18.67  Inferencing          : 2.00
% 29.45/18.67  Reduction            : 8.34
% 29.45/18.67  Demodulation         : 7.37
% 29.45/18.67  BG Simplification    : 0.24
% 29.45/18.67  Subsumption          : 6.24
% 29.45/18.67  Abstraction          : 0.41
% 29.45/18.67  MUC search           : 0.00
% 29.45/18.67  Cooper               : 0.00
% 29.45/18.67  Total                : 17.94
% 29.45/18.67  Index Insertion      : 0.00
% 29.45/18.67  Index Deletion       : 0.00
% 29.45/18.67  Index Matching       : 0.00
% 29.45/18.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
