%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:31 EST 2020

% Result     : Theorem 12.17s
% Output     : CNFRefutation 12.33s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 317 expanded)
%              Number of leaves         :   26 ( 126 expanded)
%              Depth                    :   21
%              Number of atoms          :  152 ( 616 expanded)
%              Number of equality atoms :   52 ( 207 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_28,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    ! [A_32] :
      ( k9_relat_1(A_32,k1_relat_1(A_32)) = k2_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_10] :
      ( k9_relat_1(k6_relat_1(A_10),A_10) = k2_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_80])).

tff(c_93,plain,(
    ! [A_10] : k9_relat_1(k6_relat_1(A_10),A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_89])).

tff(c_24,plain,(
    ! [A_15] : v1_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_305,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,k10_relat_1(C_52,B_53))
      | ~ r1_tarski(k9_relat_1(C_52,A_51),B_53)
      | ~ r1_tarski(A_51,k1_relat_1(C_52))
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_308,plain,(
    ! [A_10,B_53] :
      ( r1_tarski(A_10,k10_relat_1(k6_relat_1(A_10),B_53))
      | ~ r1_tarski(A_10,B_53)
      | ~ r1_tarski(A_10,k1_relat_1(k6_relat_1(A_10)))
      | ~ v1_funct_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_305])).

tff(c_321,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,k10_relat_1(k6_relat_1(A_54),B_55))
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_6,c_14,c_308])).

tff(c_57,plain,(
    ! [B_26,A_27] :
      ( r1_tarski(k10_relat_1(B_26,A_27),k1_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    ! [A_10,A_27] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_10),A_27),A_10)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_57])).

tff(c_62,plain,(
    ! [A_10,A_27] : r1_tarski(k10_relat_1(k6_relat_1(A_10),A_27),A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_60])).

tff(c_64,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_10,A_27] :
      ( k10_relat_1(k6_relat_1(A_10),A_27) = A_10
      | ~ r1_tarski(A_10,k10_relat_1(k6_relat_1(A_10),A_27)) ) ),
    inference(resolution,[status(thm)],[c_62,c_64])).

tff(c_336,plain,(
    ! [A_54,B_55] :
      ( k10_relat_1(k6_relat_1(A_54),B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_321,c_73])).

tff(c_112,plain,(
    ! [A_36,B_37] :
      ( k5_relat_1(k6_relat_1(A_36),B_37) = B_37
      | ~ r1_tarski(k1_relat_1(B_37),A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_123,plain,(
    ! [B_38] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_38)),B_38) = B_38
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_139,plain,(
    ! [A_10] :
      ( k5_relat_1(k6_relat_1(A_10),k6_relat_1(A_10)) = k6_relat_1(A_10)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_123])).

tff(c_143,plain,(
    ! [A_10] : k5_relat_1(k6_relat_1(A_10),k6_relat_1(A_10)) = k6_relat_1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_139])).

tff(c_236,plain,(
    ! [B_44,C_45,A_46] :
      ( k10_relat_1(k5_relat_1(B_44,C_45),A_46) = k10_relat_1(B_44,k10_relat_1(C_45,A_46))
      | ~ v1_relat_1(C_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_251,plain,(
    ! [A_10,A_46] :
      ( k10_relat_1(k6_relat_1(A_10),k10_relat_1(k6_relat_1(A_10),A_46)) = k10_relat_1(k6_relat_1(A_10),A_46)
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_236])).

tff(c_368,plain,(
    ! [A_58,A_59] : k10_relat_1(k6_relat_1(A_58),k10_relat_1(k6_relat_1(A_58),A_59)) = k10_relat_1(k6_relat_1(A_58),A_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_251])).

tff(c_411,plain,(
    ! [A_60,B_61] :
      ( k10_relat_1(k6_relat_1(A_60),B_61) = k10_relat_1(k6_relat_1(A_60),A_60)
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_368])).

tff(c_657,plain,(
    ! [A_73,B_74] :
      ( k10_relat_1(k6_relat_1(A_73),A_73) = A_73
      | ~ r1_tarski(A_73,B_74)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_411])).

tff(c_671,plain,(
    ! [B_2] :
      ( k10_relat_1(k6_relat_1(B_2),B_2) = B_2
      | ~ r1_tarski(B_2,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_657])).

tff(c_684,plain,(
    ! [B_2] : k10_relat_1(k6_relat_1(B_2),B_2) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_671])).

tff(c_115,plain,(
    ! [A_36,A_10] :
      ( k5_relat_1(k6_relat_1(A_36),k6_relat_1(A_10)) = k6_relat_1(A_10)
      | ~ r1_tarski(A_10,A_36)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_112])).

tff(c_189,plain,(
    ! [A_42,A_43] :
      ( k5_relat_1(k6_relat_1(A_42),k6_relat_1(A_43)) = k6_relat_1(A_43)
      | ~ r1_tarski(A_43,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_115])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_203,plain,(
    ! [A_43,A_42] :
      ( k7_relat_1(k6_relat_1(A_43),A_42) = k6_relat_1(A_43)
      | ~ v1_relat_1(k6_relat_1(A_43))
      | ~ r1_tarski(A_43,A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_20])).

tff(c_226,plain,(
    ! [A_43,A_42] :
      ( k7_relat_1(k6_relat_1(A_43),A_42) = k6_relat_1(A_43)
      | ~ r1_tarski(A_43,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_203])).

tff(c_687,plain,(
    ! [B_75] : k10_relat_1(k6_relat_1(B_75),B_75) = B_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_671])).

tff(c_257,plain,(
    ! [A_13,B_14,A_46] :
      ( k10_relat_1(k6_relat_1(A_13),k10_relat_1(B_14,A_46)) = k10_relat_1(k7_relat_1(B_14,A_13),A_46)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_236])).

tff(c_267,plain,(
    ! [A_13,B_14,A_46] :
      ( k10_relat_1(k6_relat_1(A_13),k10_relat_1(B_14,A_46)) = k10_relat_1(k7_relat_1(B_14,A_13),A_46)
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_257])).

tff(c_699,plain,(
    ! [B_75,A_13] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(B_75),A_13),B_75) = k10_relat_1(k6_relat_1(A_13),B_75)
      | ~ v1_relat_1(k6_relat_1(B_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_267])).

tff(c_753,plain,(
    ! [B_76,A_77] : k10_relat_1(k7_relat_1(k6_relat_1(B_76),A_77),B_76) = k10_relat_1(k6_relat_1(A_77),B_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_699])).

tff(c_774,plain,(
    ! [A_43,A_42] :
      ( k10_relat_1(k6_relat_1(A_43),A_43) = k10_relat_1(k6_relat_1(A_42),A_43)
      | ~ r1_tarski(A_43,A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_753])).

tff(c_787,plain,(
    ! [A_42,A_43] :
      ( k10_relat_1(k6_relat_1(A_42),A_43) = A_43
      | ~ r1_tarski(A_43,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_684,c_774])).

tff(c_121,plain,(
    ! [A_36,A_10] :
      ( k5_relat_1(k6_relat_1(A_36),k6_relat_1(A_10)) = k6_relat_1(A_10)
      | ~ r1_tarski(A_10,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_115])).

tff(c_248,plain,(
    ! [A_36,A_10,A_46] :
      ( k10_relat_1(k6_relat_1(A_36),k10_relat_1(k6_relat_1(A_10),A_46)) = k10_relat_1(k6_relat_1(A_10),A_46)
      | ~ v1_relat_1(k6_relat_1(A_10))
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ r1_tarski(A_10,A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_236])).

tff(c_2988,plain,(
    ! [A_152,A_153,A_154] :
      ( k10_relat_1(k6_relat_1(A_152),k10_relat_1(k6_relat_1(A_153),A_154)) = k10_relat_1(k6_relat_1(A_153),A_154)
      | ~ r1_tarski(A_153,A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_248])).

tff(c_29569,plain,(
    ! [A_513,A_512,A_511] :
      ( k10_relat_1(k6_relat_1(A_513),A_512) = k10_relat_1(k6_relat_1(A_511),A_512)
      | ~ r1_tarski(A_511,A_513)
      | ~ r1_tarski(A_512,A_511) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_2988])).

tff(c_30076,plain,(
    ! [A_517] :
      ( k10_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),A_517) = k10_relat_1(k6_relat_1('#skF_2'),A_517)
      | ~ r1_tarski(A_517,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_29569])).

tff(c_1180,plain,(
    ! [A_96,C_97] :
      ( r1_tarski(A_96,k10_relat_1(C_97,k9_relat_1(C_97,A_96)))
      | ~ r1_tarski(A_96,k1_relat_1(C_97))
      | ~ v1_funct_1(C_97)
      | ~ v1_relat_1(C_97) ) ),
    inference(resolution,[status(thm)],[c_6,c_305])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k10_relat_1(B_5,A_4),k1_relat_1(B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [B_5,A_4] :
      ( k10_relat_1(B_5,A_4) = k1_relat_1(B_5)
      | ~ r1_tarski(k1_relat_1(B_5),k10_relat_1(B_5,A_4))
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_64])).

tff(c_1193,plain,(
    ! [C_97] :
      ( k10_relat_1(C_97,k9_relat_1(C_97,k1_relat_1(C_97))) = k1_relat_1(C_97)
      | ~ r1_tarski(k1_relat_1(C_97),k1_relat_1(C_97))
      | ~ v1_funct_1(C_97)
      | ~ v1_relat_1(C_97) ) ),
    inference(resolution,[status(thm)],[c_1180,c_74])).

tff(c_1233,plain,(
    ! [C_97] :
      ( k10_relat_1(C_97,k9_relat_1(C_97,k1_relat_1(C_97))) = k1_relat_1(C_97)
      | ~ v1_funct_1(C_97)
      | ~ v1_relat_1(C_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1193])).

tff(c_30389,plain,
    ( k10_relat_1(k6_relat_1('#skF_2'),k9_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))))) = k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))),k10_relat_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30076,c_1233])).

tff(c_30642,plain,(
    k10_relat_1(k6_relat_1('#skF_2'),k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_93,c_14,c_22,c_24,c_93,c_14,c_14,c_30389])).

tff(c_30945,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30642,c_267])).

tff(c_31098,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30945])).

tff(c_31100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_31098])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:59:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.17/5.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/5.57  
% 12.17/5.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/5.57  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 12.17/5.57  
% 12.17/5.57  %Foreground sorts:
% 12.17/5.57  
% 12.17/5.57  
% 12.17/5.57  %Background operators:
% 12.17/5.57  
% 12.17/5.57  
% 12.17/5.57  %Foreground operators:
% 12.17/5.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.17/5.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.17/5.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.17/5.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.17/5.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.17/5.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.17/5.57  tff('#skF_2', type, '#skF_2': $i).
% 12.17/5.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.17/5.57  tff('#skF_3', type, '#skF_3': $i).
% 12.17/5.57  tff('#skF_1', type, '#skF_1': $i).
% 12.17/5.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.17/5.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.17/5.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.17/5.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.17/5.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.17/5.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.17/5.57  
% 12.33/5.59  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 12.33/5.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.33/5.59  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 12.33/5.59  tff(f_50, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 12.33/5.59  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 12.33/5.59  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 12.33/5.59  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 12.33/5.59  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 12.33/5.59  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t181_relat_1)).
% 12.33/5.59  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 12.33/5.59  tff(c_28, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.33/5.59  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.33/5.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.33/5.59  tff(c_22, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.33/5.59  tff(c_16, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.33/5.59  tff(c_14, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.33/5.59  tff(c_80, plain, (![A_32]: (k9_relat_1(A_32, k1_relat_1(A_32))=k2_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.33/5.59  tff(c_89, plain, (![A_10]: (k9_relat_1(k6_relat_1(A_10), A_10)=k2_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_80])).
% 12.33/5.59  tff(c_93, plain, (![A_10]: (k9_relat_1(k6_relat_1(A_10), A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_89])).
% 12.33/5.59  tff(c_24, plain, (![A_15]: (v1_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.33/5.59  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 12.33/5.59  tff(c_305, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, k10_relat_1(C_52, B_53)) | ~r1_tarski(k9_relat_1(C_52, A_51), B_53) | ~r1_tarski(A_51, k1_relat_1(C_52)) | ~v1_funct_1(C_52) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.33/5.59  tff(c_308, plain, (![A_10, B_53]: (r1_tarski(A_10, k10_relat_1(k6_relat_1(A_10), B_53)) | ~r1_tarski(A_10, B_53) | ~r1_tarski(A_10, k1_relat_1(k6_relat_1(A_10))) | ~v1_funct_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_305])).
% 12.33/5.59  tff(c_321, plain, (![A_54, B_55]: (r1_tarski(A_54, k10_relat_1(k6_relat_1(A_54), B_55)) | ~r1_tarski(A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_6, c_14, c_308])).
% 12.33/5.59  tff(c_57, plain, (![B_26, A_27]: (r1_tarski(k10_relat_1(B_26, A_27), k1_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.33/5.59  tff(c_60, plain, (![A_10, A_27]: (r1_tarski(k10_relat_1(k6_relat_1(A_10), A_27), A_10) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_57])).
% 12.33/5.59  tff(c_62, plain, (![A_10, A_27]: (r1_tarski(k10_relat_1(k6_relat_1(A_10), A_27), A_10))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_60])).
% 12.33/5.59  tff(c_64, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.33/5.59  tff(c_73, plain, (![A_10, A_27]: (k10_relat_1(k6_relat_1(A_10), A_27)=A_10 | ~r1_tarski(A_10, k10_relat_1(k6_relat_1(A_10), A_27)))), inference(resolution, [status(thm)], [c_62, c_64])).
% 12.33/5.59  tff(c_336, plain, (![A_54, B_55]: (k10_relat_1(k6_relat_1(A_54), B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_321, c_73])).
% 12.33/5.59  tff(c_112, plain, (![A_36, B_37]: (k5_relat_1(k6_relat_1(A_36), B_37)=B_37 | ~r1_tarski(k1_relat_1(B_37), A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.33/5.59  tff(c_123, plain, (![B_38]: (k5_relat_1(k6_relat_1(k1_relat_1(B_38)), B_38)=B_38 | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_6, c_112])).
% 12.33/5.59  tff(c_139, plain, (![A_10]: (k5_relat_1(k6_relat_1(A_10), k6_relat_1(A_10))=k6_relat_1(A_10) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_123])).
% 12.33/5.59  tff(c_143, plain, (![A_10]: (k5_relat_1(k6_relat_1(A_10), k6_relat_1(A_10))=k6_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_139])).
% 12.33/5.59  tff(c_236, plain, (![B_44, C_45, A_46]: (k10_relat_1(k5_relat_1(B_44, C_45), A_46)=k10_relat_1(B_44, k10_relat_1(C_45, A_46)) | ~v1_relat_1(C_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.33/5.59  tff(c_251, plain, (![A_10, A_46]: (k10_relat_1(k6_relat_1(A_10), k10_relat_1(k6_relat_1(A_10), A_46))=k10_relat_1(k6_relat_1(A_10), A_46) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_236])).
% 12.33/5.59  tff(c_368, plain, (![A_58, A_59]: (k10_relat_1(k6_relat_1(A_58), k10_relat_1(k6_relat_1(A_58), A_59))=k10_relat_1(k6_relat_1(A_58), A_59))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_251])).
% 12.33/5.59  tff(c_411, plain, (![A_60, B_61]: (k10_relat_1(k6_relat_1(A_60), B_61)=k10_relat_1(k6_relat_1(A_60), A_60) | ~r1_tarski(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_336, c_368])).
% 12.33/5.59  tff(c_657, plain, (![A_73, B_74]: (k10_relat_1(k6_relat_1(A_73), A_73)=A_73 | ~r1_tarski(A_73, B_74) | ~r1_tarski(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_336, c_411])).
% 12.33/5.59  tff(c_671, plain, (![B_2]: (k10_relat_1(k6_relat_1(B_2), B_2)=B_2 | ~r1_tarski(B_2, B_2))), inference(resolution, [status(thm)], [c_6, c_657])).
% 12.33/5.59  tff(c_684, plain, (![B_2]: (k10_relat_1(k6_relat_1(B_2), B_2)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_671])).
% 12.33/5.59  tff(c_115, plain, (![A_36, A_10]: (k5_relat_1(k6_relat_1(A_36), k6_relat_1(A_10))=k6_relat_1(A_10) | ~r1_tarski(A_10, A_36) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_112])).
% 12.33/5.59  tff(c_189, plain, (![A_42, A_43]: (k5_relat_1(k6_relat_1(A_42), k6_relat_1(A_43))=k6_relat_1(A_43) | ~r1_tarski(A_43, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_115])).
% 12.33/5.59  tff(c_20, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.33/5.59  tff(c_203, plain, (![A_43, A_42]: (k7_relat_1(k6_relat_1(A_43), A_42)=k6_relat_1(A_43) | ~v1_relat_1(k6_relat_1(A_43)) | ~r1_tarski(A_43, A_42))), inference(superposition, [status(thm), theory('equality')], [c_189, c_20])).
% 12.33/5.59  tff(c_226, plain, (![A_43, A_42]: (k7_relat_1(k6_relat_1(A_43), A_42)=k6_relat_1(A_43) | ~r1_tarski(A_43, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_203])).
% 12.33/5.59  tff(c_687, plain, (![B_75]: (k10_relat_1(k6_relat_1(B_75), B_75)=B_75)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_671])).
% 12.33/5.59  tff(c_257, plain, (![A_13, B_14, A_46]: (k10_relat_1(k6_relat_1(A_13), k10_relat_1(B_14, A_46))=k10_relat_1(k7_relat_1(B_14, A_13), A_46) | ~v1_relat_1(B_14) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(B_14))), inference(superposition, [status(thm), theory('equality')], [c_20, c_236])).
% 12.33/5.59  tff(c_267, plain, (![A_13, B_14, A_46]: (k10_relat_1(k6_relat_1(A_13), k10_relat_1(B_14, A_46))=k10_relat_1(k7_relat_1(B_14, A_13), A_46) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_257])).
% 12.33/5.59  tff(c_699, plain, (![B_75, A_13]: (k10_relat_1(k7_relat_1(k6_relat_1(B_75), A_13), B_75)=k10_relat_1(k6_relat_1(A_13), B_75) | ~v1_relat_1(k6_relat_1(B_75)))), inference(superposition, [status(thm), theory('equality')], [c_687, c_267])).
% 12.33/5.59  tff(c_753, plain, (![B_76, A_77]: (k10_relat_1(k7_relat_1(k6_relat_1(B_76), A_77), B_76)=k10_relat_1(k6_relat_1(A_77), B_76))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_699])).
% 12.33/5.59  tff(c_774, plain, (![A_43, A_42]: (k10_relat_1(k6_relat_1(A_43), A_43)=k10_relat_1(k6_relat_1(A_42), A_43) | ~r1_tarski(A_43, A_42))), inference(superposition, [status(thm), theory('equality')], [c_226, c_753])).
% 12.33/5.59  tff(c_787, plain, (![A_42, A_43]: (k10_relat_1(k6_relat_1(A_42), A_43)=A_43 | ~r1_tarski(A_43, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_684, c_774])).
% 12.33/5.59  tff(c_121, plain, (![A_36, A_10]: (k5_relat_1(k6_relat_1(A_36), k6_relat_1(A_10))=k6_relat_1(A_10) | ~r1_tarski(A_10, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_115])).
% 12.33/5.59  tff(c_248, plain, (![A_36, A_10, A_46]: (k10_relat_1(k6_relat_1(A_36), k10_relat_1(k6_relat_1(A_10), A_46))=k10_relat_1(k6_relat_1(A_10), A_46) | ~v1_relat_1(k6_relat_1(A_10)) | ~v1_relat_1(k6_relat_1(A_36)) | ~r1_tarski(A_10, A_36))), inference(superposition, [status(thm), theory('equality')], [c_121, c_236])).
% 12.33/5.59  tff(c_2988, plain, (![A_152, A_153, A_154]: (k10_relat_1(k6_relat_1(A_152), k10_relat_1(k6_relat_1(A_153), A_154))=k10_relat_1(k6_relat_1(A_153), A_154) | ~r1_tarski(A_153, A_152))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_248])).
% 12.33/5.59  tff(c_29569, plain, (![A_513, A_512, A_511]: (k10_relat_1(k6_relat_1(A_513), A_512)=k10_relat_1(k6_relat_1(A_511), A_512) | ~r1_tarski(A_511, A_513) | ~r1_tarski(A_512, A_511))), inference(superposition, [status(thm), theory('equality')], [c_787, c_2988])).
% 12.33/5.59  tff(c_30076, plain, (![A_517]: (k10_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), A_517)=k10_relat_1(k6_relat_1('#skF_2'), A_517) | ~r1_tarski(A_517, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_30, c_29569])).
% 12.33/5.59  tff(c_1180, plain, (![A_96, C_97]: (r1_tarski(A_96, k10_relat_1(C_97, k9_relat_1(C_97, A_96))) | ~r1_tarski(A_96, k1_relat_1(C_97)) | ~v1_funct_1(C_97) | ~v1_relat_1(C_97))), inference(resolution, [status(thm)], [c_6, c_305])).
% 12.33/5.59  tff(c_10, plain, (![B_5, A_4]: (r1_tarski(k10_relat_1(B_5, A_4), k1_relat_1(B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.33/5.59  tff(c_74, plain, (![B_5, A_4]: (k10_relat_1(B_5, A_4)=k1_relat_1(B_5) | ~r1_tarski(k1_relat_1(B_5), k10_relat_1(B_5, A_4)) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_10, c_64])).
% 12.33/5.59  tff(c_1193, plain, (![C_97]: (k10_relat_1(C_97, k9_relat_1(C_97, k1_relat_1(C_97)))=k1_relat_1(C_97) | ~r1_tarski(k1_relat_1(C_97), k1_relat_1(C_97)) | ~v1_funct_1(C_97) | ~v1_relat_1(C_97))), inference(resolution, [status(thm)], [c_1180, c_74])).
% 12.33/5.59  tff(c_1233, plain, (![C_97]: (k10_relat_1(C_97, k9_relat_1(C_97, k1_relat_1(C_97)))=k1_relat_1(C_97) | ~v1_funct_1(C_97) | ~v1_relat_1(C_97))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1193])).
% 12.33/5.59  tff(c_30389, plain, (k10_relat_1(k6_relat_1('#skF_2'), k9_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))))=k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~v1_funct_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~v1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))), k10_relat_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_30076, c_1233])).
% 12.33/5.59  tff(c_30642, plain, (k10_relat_1(k6_relat_1('#skF_2'), k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_93, c_14, c_22, c_24, c_93, c_14, c_14, c_30389])).
% 12.33/5.59  tff(c_30945, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30642, c_267])).
% 12.33/5.59  tff(c_31098, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30945])).
% 12.33/5.59  tff(c_31100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_31098])).
% 12.33/5.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.33/5.59  
% 12.33/5.59  Inference rules
% 12.33/5.59  ----------------------
% 12.33/5.59  #Ref     : 0
% 12.33/5.59  #Sup     : 7293
% 12.33/5.59  #Fact    : 0
% 12.33/5.59  #Define  : 0
% 12.33/5.59  #Split   : 2
% 12.33/5.59  #Chain   : 0
% 12.33/5.59  #Close   : 0
% 12.33/5.59  
% 12.33/5.59  Ordering : KBO
% 12.33/5.59  
% 12.33/5.59  Simplification rules
% 12.33/5.59  ----------------------
% 12.33/5.59  #Subsume      : 1671
% 12.33/5.59  #Demod        : 5954
% 12.33/5.59  #Tautology    : 1478
% 12.33/5.59  #SimpNegUnit  : 2
% 12.33/5.59  #BackRed      : 2
% 12.33/5.59  
% 12.33/5.59  #Partial instantiations: 0
% 12.33/5.59  #Strategies tried      : 1
% 12.33/5.59  
% 12.33/5.59  Timing (in seconds)
% 12.33/5.59  ----------------------
% 12.33/5.59  Preprocessing        : 0.32
% 12.33/5.59  Parsing              : 0.18
% 12.33/5.59  CNF conversion       : 0.02
% 12.33/5.59  Main loop            : 4.45
% 12.33/5.59  Inferencing          : 0.99
% 12.33/5.59  Reduction            : 1.56
% 12.33/5.59  Demodulation         : 1.26
% 12.33/5.59  BG Simplification    : 0.14
% 12.33/5.59  Subsumption          : 1.53
% 12.33/5.59  Abstraction          : 0.20
% 12.33/5.59  MUC search           : 0.00
% 12.33/5.59  Cooper               : 0.00
% 12.33/5.59  Total                : 4.80
% 12.33/5.59  Index Insertion      : 0.00
% 12.33/5.59  Index Deletion       : 0.00
% 12.33/5.59  Index Matching       : 0.00
% 12.33/5.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
