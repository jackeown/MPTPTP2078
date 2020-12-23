%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:26 EST 2020

% Result     : Timeout 58.21s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   79 ( 381 expanded)
%              Number of leaves         :   29 ( 148 expanded)
%              Depth                    :   15
%              Number of atoms          :  129 ( 677 expanded)
%              Number of equality atoms :   50 ( 248 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [B_39,A_40] : k1_setfam_1(k2_tarski(B_39,A_40)) = k3_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_84])).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_8])).

tff(c_146,plain,(
    ! [B_41,A_42] : r1_tarski(k3_xboole_0(B_41,A_42),A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_2])).

tff(c_12,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_181,plain,(
    ! [A_45] :
      ( k5_relat_1(A_45,k6_relat_1(k2_relat_1(A_45))) = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_190,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_relat_1(A_19),k6_relat_1(A_19)) = k6_relat_1(A_19)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_181])).

tff(c_194,plain,(
    ! [A_19] : k5_relat_1(k6_relat_1(A_19),k6_relat_1(A_19)) = k6_relat_1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_190])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_relat_1(A_26),B_27) = k7_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_432,plain,(
    ! [A_66,B_67,C_68] :
      ( k5_relat_1(k5_relat_1(A_66,B_67),C_68) = k5_relat_1(A_66,k5_relat_1(B_67,C_68))
      | ~ v1_relat_1(C_68)
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_454,plain,(
    ! [A_26,B_27,C_68] :
      ( k5_relat_1(k6_relat_1(A_26),k5_relat_1(B_27,C_68)) = k5_relat_1(k7_relat_1(B_27,A_26),C_68)
      | ~ v1_relat_1(C_68)
      | ~ v1_relat_1(B_27)
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_432])).

tff(c_1847,plain,(
    ! [A_102,B_103,C_104] :
      ( k5_relat_1(k6_relat_1(A_102),k5_relat_1(B_103,C_104)) = k5_relat_1(k7_relat_1(B_103,A_102),C_104)
      | ~ v1_relat_1(C_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_454])).

tff(c_1916,plain,(
    ! [A_19,A_102] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_19),A_102),k6_relat_1(A_19)) = k5_relat_1(k6_relat_1(A_102),k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_1847])).

tff(c_1950,plain,(
    ! [A_19,A_102] : k5_relat_1(k7_relat_1(k6_relat_1(A_19),A_102),k6_relat_1(A_19)) = k5_relat_1(k6_relat_1(A_102),k6_relat_1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_1916])).

tff(c_21333,plain,(
    ! [B_336,C_337,A_338] :
      ( k7_relat_1(k5_relat_1(B_336,C_337),A_338) = k5_relat_1(k7_relat_1(B_336,A_338),C_337)
      | ~ v1_relat_1(k5_relat_1(B_336,C_337))
      | ~ v1_relat_1(C_337)
      | ~ v1_relat_1(B_336) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_28])).

tff(c_21403,plain,(
    ! [A_19,A_338] :
      ( k7_relat_1(k5_relat_1(k6_relat_1(A_19),k6_relat_1(A_19)),A_338) = k5_relat_1(k7_relat_1(k6_relat_1(A_19),A_338),k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_21333])).

tff(c_21466,plain,(
    ! [A_338,A_19] : k5_relat_1(k6_relat_1(A_338),k6_relat_1(A_19)) = k7_relat_1(k6_relat_1(A_19),A_338) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_12,c_1950,c_194,c_21403])).

tff(c_378,plain,(
    ! [B_60,A_61] :
      ( k5_relat_1(B_60,k6_relat_1(A_61)) = B_60
      | ~ r1_tarski(k2_relat_1(B_60),A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_381,plain,(
    ! [A_19,A_61] :
      ( k5_relat_1(k6_relat_1(A_19),k6_relat_1(A_61)) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_61)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_378])).

tff(c_621,plain,(
    ! [A_74,A_75] :
      ( k5_relat_1(k6_relat_1(A_74),k6_relat_1(A_75)) = k6_relat_1(A_74)
      | ~ r1_tarski(A_74,A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_381])).

tff(c_630,plain,(
    ! [A_75,A_74] :
      ( k7_relat_1(k6_relat_1(A_75),A_74) = k6_relat_1(A_74)
      | ~ v1_relat_1(k6_relat_1(A_75))
      | ~ r1_tarski(A_74,A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_28])).

tff(c_671,plain,(
    ! [A_75,A_74] :
      ( k7_relat_1(k6_relat_1(A_75),A_74) = k6_relat_1(A_74)
      | ~ r1_tarski(A_74,A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_630])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k5_relat_1(A_9,B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1877,plain,(
    ! [B_103,A_102,C_104] :
      ( v1_relat_1(k5_relat_1(k7_relat_1(B_103,A_102),C_104))
      | ~ v1_relat_1(k5_relat_1(B_103,C_104))
      | ~ v1_relat_1(k6_relat_1(A_102))
      | ~ v1_relat_1(C_104)
      | ~ v1_relat_1(B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_10])).

tff(c_6766,plain,(
    ! [B_181,A_182,C_183] :
      ( v1_relat_1(k5_relat_1(k7_relat_1(B_181,A_182),C_183))
      | ~ v1_relat_1(k5_relat_1(B_181,C_183))
      | ~ v1_relat_1(C_183)
      | ~ v1_relat_1(B_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1877])).

tff(c_6779,plain,(
    ! [A_102,A_19] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_102),k6_relat_1(A_19)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_19),k6_relat_1(A_19)))
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1950,c_6766])).

tff(c_6816,plain,(
    ! [A_184,A_185] : v1_relat_1(k5_relat_1(k6_relat_1(A_184),k6_relat_1(A_185))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_12,c_194,c_6779])).

tff(c_6830,plain,(
    ! [A_185,A_26] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_185),A_26))
      | ~ v1_relat_1(k6_relat_1(A_185)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6816])).

tff(c_6847,plain,(
    ! [A_185,A_26] : v1_relat_1(k7_relat_1(k6_relat_1(A_185),A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6830])).

tff(c_16,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_302,plain,(
    ! [B_55,A_56] :
      ( k3_xboole_0(k1_relat_1(B_55),A_56) = k1_relat_1(k7_relat_1(B_55,A_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_331,plain,(
    ! [A_19,A_56] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_19),A_56)) = k3_xboole_0(A_19,A_56)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_302])).

tff(c_335,plain,(
    ! [A_19,A_56] : k1_relat_1(k7_relat_1(k6_relat_1(A_19),A_56)) = k3_xboole_0(A_19,A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_331])).

tff(c_20,plain,(
    ! [A_20] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_20)),A_20) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24131,plain,(
    ! [B_370,C_371] :
      ( k5_relat_1(k7_relat_1(B_370,k1_relat_1(k5_relat_1(B_370,C_371))),C_371) = k5_relat_1(B_370,C_371)
      | ~ v1_relat_1(k5_relat_1(B_370,C_371))
      | ~ v1_relat_1(C_371)
      | ~ v1_relat_1(B_370) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1847,c_20])).

tff(c_24222,plain,(
    ! [A_338,A_19] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_338),k1_relat_1(k7_relat_1(k6_relat_1(A_19),A_338))),k6_relat_1(A_19)) = k5_relat_1(k6_relat_1(A_338),k6_relat_1(A_19))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_338),k6_relat_1(A_19)))
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(k6_relat_1(A_338)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21466,c_24131])).

tff(c_166235,plain,(
    ! [A_1012,A_1013] : k5_relat_1(k7_relat_1(k6_relat_1(A_1012),k3_xboole_0(A_1013,A_1012)),k6_relat_1(A_1013)) = k7_relat_1(k6_relat_1(A_1013),A_1012) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_6847,c_21466,c_21466,c_335,c_24222])).

tff(c_166837,plain,(
    ! [A_1013,A_75] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_1013,A_75)),k6_relat_1(A_1013)) = k7_relat_1(k6_relat_1(A_1013),A_75)
      | ~ r1_tarski(k3_xboole_0(A_1013,A_75),A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_166235])).

tff(c_167088,plain,(
    ! [A_1014,A_1015] : k7_relat_1(k6_relat_1(A_1014),k3_xboole_0(A_1014,A_1015)) = k7_relat_1(k6_relat_1(A_1014),A_1015) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_21466,c_166837])).

tff(c_167399,plain,(
    ! [A_1014,A_1015] :
      ( k7_relat_1(k6_relat_1(A_1014),A_1015) = k6_relat_1(k3_xboole_0(A_1014,A_1015))
      | ~ r1_tarski(k3_xboole_0(A_1014,A_1015),A_1014) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167088,c_671])).

tff(c_167829,plain,(
    ! [A_1014,A_1015] : k7_relat_1(k6_relat_1(A_1014),A_1015) = k6_relat_1(k3_xboole_0(A_1014,A_1015)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_167399])).

tff(c_235,plain,(
    ! [A_50,B_51] :
      ( k5_relat_1(k6_relat_1(A_50),B_51) = k7_relat_1(B_51,A_50)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_256,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_30])).

tff(c_278,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_256])).

tff(c_167924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167829,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 58.21/38.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.21/38.96  
% 58.21/38.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.21/38.96  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 58.21/38.96  
% 58.21/38.96  %Foreground sorts:
% 58.21/38.96  
% 58.21/38.96  
% 58.21/38.96  %Background operators:
% 58.21/38.96  
% 58.21/38.96  
% 58.21/38.96  %Foreground operators:
% 58.21/38.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 58.21/38.96  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 58.21/38.96  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 58.21/38.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 58.21/38.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 58.21/38.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 58.21/38.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 58.21/38.96  tff('#skF_2', type, '#skF_2': $i).
% 58.21/38.96  tff('#skF_1', type, '#skF_1': $i).
% 58.21/38.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 58.21/38.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 58.21/38.96  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 58.21/38.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 58.21/38.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 58.21/38.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 58.21/38.96  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 58.21/38.96  
% 58.21/38.98  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 58.21/38.98  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 58.21/38.98  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 58.21/38.98  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 58.21/38.98  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 58.21/38.98  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 58.21/38.98  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 58.21/38.98  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 58.21/38.98  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 58.21/38.98  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 58.21/38.98  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 58.21/38.98  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 58.21/38.98  tff(f_80, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 58.21/38.98  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 58.21/38.98  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 58.21/38.98  tff(c_84, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 58.21/38.98  tff(c_108, plain, (![B_39, A_40]: (k1_setfam_1(k2_tarski(B_39, A_40))=k3_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_4, c_84])).
% 58.21/38.98  tff(c_8, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 58.21/38.98  tff(c_131, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_108, c_8])).
% 58.21/38.98  tff(c_146, plain, (![B_41, A_42]: (r1_tarski(k3_xboole_0(B_41, A_42), A_42))), inference(superposition, [status(thm), theory('equality')], [c_131, c_2])).
% 58.21/38.98  tff(c_12, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 58.21/38.98  tff(c_18, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_55])).
% 58.21/38.98  tff(c_181, plain, (![A_45]: (k5_relat_1(A_45, k6_relat_1(k2_relat_1(A_45)))=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 58.21/38.98  tff(c_190, plain, (![A_19]: (k5_relat_1(k6_relat_1(A_19), k6_relat_1(A_19))=k6_relat_1(A_19) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_181])).
% 58.21/38.98  tff(c_194, plain, (![A_19]: (k5_relat_1(k6_relat_1(A_19), k6_relat_1(A_19))=k6_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_190])).
% 58.21/38.98  tff(c_28, plain, (![A_26, B_27]: (k5_relat_1(k6_relat_1(A_26), B_27)=k7_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 58.21/38.98  tff(c_432, plain, (![A_66, B_67, C_68]: (k5_relat_1(k5_relat_1(A_66, B_67), C_68)=k5_relat_1(A_66, k5_relat_1(B_67, C_68)) | ~v1_relat_1(C_68) | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 58.21/38.98  tff(c_454, plain, (![A_26, B_27, C_68]: (k5_relat_1(k6_relat_1(A_26), k5_relat_1(B_27, C_68))=k5_relat_1(k7_relat_1(B_27, A_26), C_68) | ~v1_relat_1(C_68) | ~v1_relat_1(B_27) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(B_27))), inference(superposition, [status(thm), theory('equality')], [c_28, c_432])).
% 58.21/38.98  tff(c_1847, plain, (![A_102, B_103, C_104]: (k5_relat_1(k6_relat_1(A_102), k5_relat_1(B_103, C_104))=k5_relat_1(k7_relat_1(B_103, A_102), C_104) | ~v1_relat_1(C_104) | ~v1_relat_1(B_103))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_454])).
% 58.21/38.98  tff(c_1916, plain, (![A_19, A_102]: (k5_relat_1(k7_relat_1(k6_relat_1(A_19), A_102), k6_relat_1(A_19))=k5_relat_1(k6_relat_1(A_102), k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_194, c_1847])).
% 58.21/38.98  tff(c_1950, plain, (![A_19, A_102]: (k5_relat_1(k7_relat_1(k6_relat_1(A_19), A_102), k6_relat_1(A_19))=k5_relat_1(k6_relat_1(A_102), k6_relat_1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_1916])).
% 58.21/38.98  tff(c_21333, plain, (![B_336, C_337, A_338]: (k7_relat_1(k5_relat_1(B_336, C_337), A_338)=k5_relat_1(k7_relat_1(B_336, A_338), C_337) | ~v1_relat_1(k5_relat_1(B_336, C_337)) | ~v1_relat_1(C_337) | ~v1_relat_1(B_336))), inference(superposition, [status(thm), theory('equality')], [c_1847, c_28])).
% 58.21/38.98  tff(c_21403, plain, (![A_19, A_338]: (k7_relat_1(k5_relat_1(k6_relat_1(A_19), k6_relat_1(A_19)), A_338)=k5_relat_1(k7_relat_1(k6_relat_1(A_19), A_338), k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_194, c_21333])).
% 58.21/38.98  tff(c_21466, plain, (![A_338, A_19]: (k5_relat_1(k6_relat_1(A_338), k6_relat_1(A_19))=k7_relat_1(k6_relat_1(A_19), A_338))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_12, c_1950, c_194, c_21403])).
% 58.21/38.98  tff(c_378, plain, (![B_60, A_61]: (k5_relat_1(B_60, k6_relat_1(A_61))=B_60 | ~r1_tarski(k2_relat_1(B_60), A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_65])).
% 58.21/38.98  tff(c_381, plain, (![A_19, A_61]: (k5_relat_1(k6_relat_1(A_19), k6_relat_1(A_61))=k6_relat_1(A_19) | ~r1_tarski(A_19, A_61) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_378])).
% 58.21/38.98  tff(c_621, plain, (![A_74, A_75]: (k5_relat_1(k6_relat_1(A_74), k6_relat_1(A_75))=k6_relat_1(A_74) | ~r1_tarski(A_74, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_381])).
% 58.21/38.98  tff(c_630, plain, (![A_75, A_74]: (k7_relat_1(k6_relat_1(A_75), A_74)=k6_relat_1(A_74) | ~v1_relat_1(k6_relat_1(A_75)) | ~r1_tarski(A_74, A_75))), inference(superposition, [status(thm), theory('equality')], [c_621, c_28])).
% 58.21/38.98  tff(c_671, plain, (![A_75, A_74]: (k7_relat_1(k6_relat_1(A_75), A_74)=k6_relat_1(A_74) | ~r1_tarski(A_74, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_630])).
% 58.21/38.98  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k5_relat_1(A_9, B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 58.21/38.98  tff(c_1877, plain, (![B_103, A_102, C_104]: (v1_relat_1(k5_relat_1(k7_relat_1(B_103, A_102), C_104)) | ~v1_relat_1(k5_relat_1(B_103, C_104)) | ~v1_relat_1(k6_relat_1(A_102)) | ~v1_relat_1(C_104) | ~v1_relat_1(B_103))), inference(superposition, [status(thm), theory('equality')], [c_1847, c_10])).
% 58.21/38.98  tff(c_6766, plain, (![B_181, A_182, C_183]: (v1_relat_1(k5_relat_1(k7_relat_1(B_181, A_182), C_183)) | ~v1_relat_1(k5_relat_1(B_181, C_183)) | ~v1_relat_1(C_183) | ~v1_relat_1(B_181))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1877])).
% 58.21/38.98  tff(c_6779, plain, (![A_102, A_19]: (v1_relat_1(k5_relat_1(k6_relat_1(A_102), k6_relat_1(A_19))) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_19), k6_relat_1(A_19))) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_1950, c_6766])).
% 58.21/38.98  tff(c_6816, plain, (![A_184, A_185]: (v1_relat_1(k5_relat_1(k6_relat_1(A_184), k6_relat_1(A_185))))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_12, c_194, c_6779])).
% 58.21/38.98  tff(c_6830, plain, (![A_185, A_26]: (v1_relat_1(k7_relat_1(k6_relat_1(A_185), A_26)) | ~v1_relat_1(k6_relat_1(A_185)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6816])).
% 58.21/38.98  tff(c_6847, plain, (![A_185, A_26]: (v1_relat_1(k7_relat_1(k6_relat_1(A_185), A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6830])).
% 58.21/38.98  tff(c_16, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_55])).
% 58.21/38.98  tff(c_302, plain, (![B_55, A_56]: (k3_xboole_0(k1_relat_1(B_55), A_56)=k1_relat_1(k7_relat_1(B_55, A_56)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_73])).
% 58.21/38.98  tff(c_331, plain, (![A_19, A_56]: (k1_relat_1(k7_relat_1(k6_relat_1(A_19), A_56))=k3_xboole_0(A_19, A_56) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_302])).
% 58.21/38.98  tff(c_335, plain, (![A_19, A_56]: (k1_relat_1(k7_relat_1(k6_relat_1(A_19), A_56))=k3_xboole_0(A_19, A_56))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_331])).
% 58.21/38.98  tff(c_20, plain, (![A_20]: (k5_relat_1(k6_relat_1(k1_relat_1(A_20)), A_20)=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 58.21/38.98  tff(c_24131, plain, (![B_370, C_371]: (k5_relat_1(k7_relat_1(B_370, k1_relat_1(k5_relat_1(B_370, C_371))), C_371)=k5_relat_1(B_370, C_371) | ~v1_relat_1(k5_relat_1(B_370, C_371)) | ~v1_relat_1(C_371) | ~v1_relat_1(B_370))), inference(superposition, [status(thm), theory('equality')], [c_1847, c_20])).
% 58.21/38.98  tff(c_24222, plain, (![A_338, A_19]: (k5_relat_1(k7_relat_1(k6_relat_1(A_338), k1_relat_1(k7_relat_1(k6_relat_1(A_19), A_338))), k6_relat_1(A_19))=k5_relat_1(k6_relat_1(A_338), k6_relat_1(A_19)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_338), k6_relat_1(A_19))) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(k6_relat_1(A_338)))), inference(superposition, [status(thm), theory('equality')], [c_21466, c_24131])).
% 58.21/38.98  tff(c_166235, plain, (![A_1012, A_1013]: (k5_relat_1(k7_relat_1(k6_relat_1(A_1012), k3_xboole_0(A_1013, A_1012)), k6_relat_1(A_1013))=k7_relat_1(k6_relat_1(A_1013), A_1012))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_6847, c_21466, c_21466, c_335, c_24222])).
% 58.21/38.98  tff(c_166837, plain, (![A_1013, A_75]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_1013, A_75)), k6_relat_1(A_1013))=k7_relat_1(k6_relat_1(A_1013), A_75) | ~r1_tarski(k3_xboole_0(A_1013, A_75), A_75))), inference(superposition, [status(thm), theory('equality')], [c_671, c_166235])).
% 58.21/38.98  tff(c_167088, plain, (![A_1014, A_1015]: (k7_relat_1(k6_relat_1(A_1014), k3_xboole_0(A_1014, A_1015))=k7_relat_1(k6_relat_1(A_1014), A_1015))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_21466, c_166837])).
% 58.21/38.98  tff(c_167399, plain, (![A_1014, A_1015]: (k7_relat_1(k6_relat_1(A_1014), A_1015)=k6_relat_1(k3_xboole_0(A_1014, A_1015)) | ~r1_tarski(k3_xboole_0(A_1014, A_1015), A_1014))), inference(superposition, [status(thm), theory('equality')], [c_167088, c_671])).
% 58.21/38.98  tff(c_167829, plain, (![A_1014, A_1015]: (k7_relat_1(k6_relat_1(A_1014), A_1015)=k6_relat_1(k3_xboole_0(A_1014, A_1015)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_167399])).
% 58.21/38.98  tff(c_235, plain, (![A_50, B_51]: (k5_relat_1(k6_relat_1(A_50), B_51)=k7_relat_1(B_51, A_50) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_77])).
% 58.21/38.98  tff(c_30, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 58.21/38.98  tff(c_256, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_30])).
% 58.21/38.98  tff(c_278, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_256])).
% 58.21/38.98  tff(c_167924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167829, c_278])).
% 58.21/38.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 58.21/38.98  
% 58.21/38.98  Inference rules
% 58.21/38.98  ----------------------
% 58.21/38.98  #Ref     : 0
% 58.21/38.98  #Sup     : 42006
% 58.21/38.98  #Fact    : 0
% 58.21/38.98  #Define  : 0
% 58.21/38.98  #Split   : 1
% 58.21/38.98  #Chain   : 0
% 58.21/38.98  #Close   : 0
% 58.21/38.98  
% 58.21/38.98  Ordering : KBO
% 58.21/38.98  
% 58.21/38.98  Simplification rules
% 58.21/38.98  ----------------------
% 58.41/38.98  #Subsume      : 6385
% 58.41/38.98  #Demod        : 41895
% 58.41/38.98  #Tautology    : 6390
% 58.41/38.98  #SimpNegUnit  : 0
% 58.41/38.98  #BackRed      : 42
% 58.41/38.98  
% 58.41/38.98  #Partial instantiations: 0
% 58.41/38.98  #Strategies tried      : 1
% 58.41/38.98  
% 58.41/38.98  Timing (in seconds)
% 58.41/38.98  ----------------------
% 58.42/38.98  Preprocessing        : 0.29
% 58.42/38.98  Parsing              : 0.15
% 58.42/38.98  CNF conversion       : 0.02
% 58.42/38.98  Main loop            : 37.92
% 58.42/38.98  Inferencing          : 5.37
% 58.42/38.98  Reduction            : 19.43
% 58.42/38.98  Demodulation         : 17.71
% 58.42/38.98  BG Simplification    : 1.10
% 58.42/38.98  Subsumption          : 10.53
% 58.42/38.98  Abstraction          : 1.82
% 58.42/38.98  MUC search           : 0.00
% 58.42/38.98  Cooper               : 0.00
% 58.42/38.98  Total                : 38.25
% 58.42/38.98  Index Insertion      : 0.00
% 58.42/38.98  Index Deletion       : 0.00
% 58.42/38.98  Index Matching       : 0.00
% 58.42/38.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
