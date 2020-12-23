%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:12 EST 2020

% Result     : Theorem 20.56s
% Output     : CNFRefutation 20.73s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 356 expanded)
%              Number of leaves         :   27 ( 136 expanded)
%              Depth                    :   21
%              Number of atoms          :  174 ( 618 expanded)
%              Number of equality atoms :   50 ( 234 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_36,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_61,plain,(
    ! [A_35] :
      ( k7_relat_1(A_35,k1_relat_1(A_35)) = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_73,plain,(
    ! [A_19] :
      ( k7_relat_1(k6_relat_1(A_19),A_19) = k6_relat_1(A_19)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_61])).

tff(c_77,plain,(
    ! [A_19] : k7_relat_1(k6_relat_1(A_19),A_19) = k6_relat_1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_73])).

tff(c_224,plain,(
    ! [B_56,A_57] :
      ( k7_relat_1(B_56,A_57) = B_56
      | ~ r1_tarski(k1_relat_1(B_56),A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_227,plain,(
    ! [A_19,A_57] :
      ( k7_relat_1(k6_relat_1(A_19),A_57) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_57)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_224])).

tff(c_233,plain,(
    ! [A_19,A_57] :
      ( k7_relat_1(k6_relat_1(A_19),A_57) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_227])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k5_relat_1(k6_relat_1(A_22),B_23) = k7_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_318,plain,(
    ! [B_64,C_65,A_66] :
      ( k7_relat_1(k5_relat_1(B_64,C_65),A_66) = k5_relat_1(k7_relat_1(B_64,A_66),C_65)
      | ~ v1_relat_1(C_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_340,plain,(
    ! [A_22,A_66,B_23] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_22),A_66),B_23) = k7_relat_1(k7_relat_1(B_23,A_22),A_66)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_318])).

tff(c_348,plain,(
    ! [A_22,A_66,B_23] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_22),A_66),B_23) = k7_relat_1(k7_relat_1(B_23,A_22),A_66)
      | ~ v1_relat_1(B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_340])).

tff(c_945,plain,(
    ! [A_119,A_120,B_121] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_119),A_120),B_121) = k7_relat_1(k7_relat_1(B_121,A_119),A_120)
      | ~ v1_relat_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_340])).

tff(c_984,plain,(
    ! [B_122,A_123] :
      ( k7_relat_1(k7_relat_1(B_122,A_123),A_123) = k5_relat_1(k6_relat_1(A_123),B_122)
      | ~ v1_relat_1(B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_945])).

tff(c_1023,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_relat_1(A_19),k6_relat_1(A_19)) = k7_relat_1(k6_relat_1(A_19),A_19)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_984])).

tff(c_1032,plain,(
    ! [A_19] : k5_relat_1(k6_relat_1(A_19),k6_relat_1(A_19)) = k6_relat_1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_77,c_1023])).

tff(c_1033,plain,(
    ! [A_124] : k5_relat_1(k6_relat_1(A_124),k6_relat_1(A_124)) = k6_relat_1(A_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_77,c_1023])).

tff(c_14,plain,(
    ! [B_10,C_12,A_9] :
      ( k7_relat_1(k5_relat_1(B_10,C_12),A_9) = k5_relat_1(k7_relat_1(B_10,A_9),C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1054,plain,(
    ! [A_124,A_9] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_124),A_9),k6_relat_1(A_124)) = k7_relat_1(k6_relat_1(A_124),A_9)
      | ~ v1_relat_1(k6_relat_1(A_124))
      | ~ v1_relat_1(k6_relat_1(A_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1033,c_14])).

tff(c_1079,plain,(
    ! [A_124,A_9] : k5_relat_1(k7_relat_1(k6_relat_1(A_124),A_9),k6_relat_1(A_124)) = k7_relat_1(k6_relat_1(A_124),A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_1054])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1886,plain,(
    ! [B_171,A_172,C_173] :
      ( v1_relat_1(k5_relat_1(k7_relat_1(B_171,A_172),C_173))
      | ~ v1_relat_1(k5_relat_1(B_171,C_173))
      | ~ v1_relat_1(C_173)
      | ~ v1_relat_1(B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_12])).

tff(c_1889,plain,(
    ! [A_124,A_9] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_124),A_9))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_124),k6_relat_1(A_124)))
      | ~ v1_relat_1(k6_relat_1(A_124))
      | ~ v1_relat_1(k6_relat_1(A_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1079,c_1886])).

tff(c_1909,plain,(
    ! [A_124,A_9] : v1_relat_1(k7_relat_1(k6_relat_1(A_124),A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_1032,c_1889])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_26] :
      ( k7_relat_1(A_26,k1_relat_1(A_26)) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_20),B_21),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_94,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1272,plain,(
    ! [A_135,B_136] :
      ( k5_relat_1(k6_relat_1(A_135),B_136) = B_136
      | ~ r1_tarski(B_136,k5_relat_1(k6_relat_1(A_135),B_136))
      | ~ v1_relat_1(B_136) ) ),
    inference(resolution,[status(thm)],[c_24,c_94])).

tff(c_6121,plain,(
    ! [A_323,B_324] :
      ( k5_relat_1(k6_relat_1(A_323),B_324) = B_324
      | ~ r1_tarski(B_324,k7_relat_1(B_324,A_323))
      | ~ v1_relat_1(B_324)
      | ~ v1_relat_1(B_324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1272])).

tff(c_6139,plain,(
    ! [A_26] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_26)),A_26) = A_26
      | ~ r1_tarski(A_26,A_26)
      | ~ v1_relat_1(A_26)
      | ~ v1_relat_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6121])).

tff(c_6146,plain,(
    ! [A_325] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_325)),A_325) = A_325
      | ~ v1_relat_1(A_325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6139])).

tff(c_6235,plain,(
    ! [A_325,A_9] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(A_325)),A_9),A_325) = k7_relat_1(A_325,A_9)
      | ~ v1_relat_1(A_325)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(A_325)))
      | ~ v1_relat_1(A_325) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6146,c_14])).

tff(c_6302,plain,(
    ! [A_325,A_9] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(A_325)),A_9),A_325) = k7_relat_1(A_325,A_9)
      | ~ v1_relat_1(A_325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6235])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k5_relat_1(B_21,k6_relat_1(A_20)),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_169,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(A_50,C_51)
      | ~ r1_tarski(B_52,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_485,plain,(
    ! [A_76,B_77,A_78] :
      ( r1_tarski(A_76,B_77)
      | ~ r1_tarski(A_76,k5_relat_1(B_77,k6_relat_1(A_78)))
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_26,c_169])).

tff(c_8789,plain,(
    ! [B_410,A_411,A_412] :
      ( r1_tarski(k5_relat_1(k5_relat_1(B_410,k6_relat_1(A_411)),k6_relat_1(A_412)),B_410)
      | ~ v1_relat_1(B_410)
      | ~ v1_relat_1(k5_relat_1(B_410,k6_relat_1(A_411))) ) ),
    inference(resolution,[status(thm)],[c_26,c_485])).

tff(c_8888,plain,(
    ! [A_411,A_9,A_412] :
      ( r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(A_411),A_9),k6_relat_1(A_412)),k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_411))),A_9))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_411))),A_9))
      | ~ v1_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_411))),A_9),k6_relat_1(A_411)))
      | ~ v1_relat_1(k6_relat_1(A_411)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6302,c_8789])).

tff(c_8994,plain,(
    ! [A_413,A_414,A_415] : r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(A_413),A_414),k6_relat_1(A_415)),k7_relat_1(k6_relat_1(A_413),A_414)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1909,c_1079,c_20,c_1909,c_20,c_20,c_8888])).

tff(c_9050,plain,(
    ! [A_415,A_22,A_66] :
      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_415),A_22),A_66),k7_relat_1(k6_relat_1(A_22),A_66))
      | ~ v1_relat_1(k6_relat_1(A_415)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_8994])).

tff(c_9336,plain,(
    ! [A_425,A_426,A_427] : r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_425),A_426),A_427),k7_relat_1(k6_relat_1(A_426),A_427)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9050])).

tff(c_11261,plain,(
    ! [A_460,A_461,A_462] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_460),A_461),k7_relat_1(k6_relat_1(A_462),A_461))
      | ~ r1_tarski(A_460,A_462) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_9336])).

tff(c_11347,plain,(
    ! [A_463,A_464] :
      ( r1_tarski(k6_relat_1(A_463),k7_relat_1(k6_relat_1(A_464),A_463))
      | ~ r1_tarski(A_463,A_464) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_11261])).

tff(c_137,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = k7_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_147,plain,(
    ! [A_20,A_46] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_20),A_46),k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_26])).

tff(c_155,plain,(
    ! [A_48,A_49] : r1_tarski(k7_relat_1(k6_relat_1(A_48),A_49),k6_relat_1(A_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_147])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_165,plain,(
    ! [A_48,A_49] :
      ( k7_relat_1(k6_relat_1(A_48),A_49) = k6_relat_1(A_49)
      | ~ r1_tarski(k6_relat_1(A_49),k7_relat_1(k6_relat_1(A_48),A_49)) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_11448,plain,(
    ! [A_465,A_466] :
      ( k7_relat_1(k6_relat_1(A_465),A_466) = k6_relat_1(A_466)
      | ~ r1_tarski(A_466,A_465) ) ),
    inference(resolution,[status(thm)],[c_11347,c_165])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_11763,plain,(
    ! [A_465,A_466] :
      ( k9_relat_1(k6_relat_1(A_465),A_466) = k2_relat_1(k6_relat_1(A_466))
      | ~ v1_relat_1(k6_relat_1(A_465))
      | ~ r1_tarski(A_466,A_465) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11448,c_16])).

tff(c_11904,plain,(
    ! [A_469,A_470] :
      ( k9_relat_1(k6_relat_1(A_469),A_470) = A_470
      | ~ r1_tarski(A_470,A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22,c_11763])).

tff(c_512,plain,(
    ! [B_79,C_80,A_81] :
      ( k9_relat_1(k5_relat_1(B_79,C_80),A_81) = k9_relat_1(C_80,k9_relat_1(B_79,A_81))
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_529,plain,(
    ! [B_23,A_22,A_81] :
      ( k9_relat_1(B_23,k9_relat_1(k6_relat_1(A_22),A_81)) = k9_relat_1(k7_relat_1(B_23,A_22),A_81)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(k6_relat_1(A_22))
      | ~ v1_relat_1(B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_512])).

tff(c_533,plain,(
    ! [B_23,A_22,A_81] :
      ( k9_relat_1(B_23,k9_relat_1(k6_relat_1(A_22),A_81)) = k9_relat_1(k7_relat_1(B_23,A_22),A_81)
      | ~ v1_relat_1(B_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_529])).

tff(c_54367,plain,(
    ! [B_1018,A_1019,A_1020] :
      ( k9_relat_1(k7_relat_1(B_1018,A_1019),A_1020) = k9_relat_1(B_1018,A_1020)
      | ~ v1_relat_1(B_1018)
      | ~ r1_tarski(A_1020,A_1019) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11904,c_533])).

tff(c_34,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_54452,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_54367,c_34])).

tff(c_54562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_54452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.56/11.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.56/11.35  
% 20.56/11.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.56/11.35  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 20.56/11.35  
% 20.56/11.35  %Foreground sorts:
% 20.56/11.35  
% 20.56/11.35  
% 20.56/11.35  %Background operators:
% 20.56/11.35  
% 20.56/11.35  
% 20.56/11.35  %Foreground operators:
% 20.56/11.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.56/11.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 20.56/11.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 20.56/11.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.56/11.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.56/11.35  tff('#skF_2', type, '#skF_2': $i).
% 20.56/11.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 20.56/11.35  tff('#skF_3', type, '#skF_3': $i).
% 20.56/11.35  tff('#skF_1', type, '#skF_1': $i).
% 20.56/11.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.56/11.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.56/11.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 20.56/11.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.56/11.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.56/11.35  
% 20.73/11.37  tff(f_93, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 20.73/11.37  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 20.73/11.37  tff(f_65, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 20.73/11.37  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 20.73/11.37  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 20.73/11.37  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 20.73/11.37  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 20.73/11.37  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 20.73/11.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.73/11.37  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_relat_1)).
% 20.73/11.37  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 20.73/11.37  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 20.73/11.37  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 20.73/11.37  tff(c_36, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 20.73/11.37  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 20.73/11.37  tff(c_10, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.73/11.37  tff(c_22, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_65])).
% 20.73/11.37  tff(c_20, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_65])).
% 20.73/11.37  tff(c_61, plain, (![A_35]: (k7_relat_1(A_35, k1_relat_1(A_35))=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_85])).
% 20.73/11.37  tff(c_73, plain, (![A_19]: (k7_relat_1(k6_relat_1(A_19), A_19)=k6_relat_1(A_19) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_61])).
% 20.73/11.37  tff(c_77, plain, (![A_19]: (k7_relat_1(k6_relat_1(A_19), A_19)=k6_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_73])).
% 20.73/11.37  tff(c_224, plain, (![B_56, A_57]: (k7_relat_1(B_56, A_57)=B_56 | ~r1_tarski(k1_relat_1(B_56), A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_81])).
% 20.73/11.37  tff(c_227, plain, (![A_19, A_57]: (k7_relat_1(k6_relat_1(A_19), A_57)=k6_relat_1(A_19) | ~r1_tarski(A_19, A_57) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_224])).
% 20.73/11.37  tff(c_233, plain, (![A_19, A_57]: (k7_relat_1(k6_relat_1(A_19), A_57)=k6_relat_1(A_19) | ~r1_tarski(A_19, A_57))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_227])).
% 20.73/11.37  tff(c_28, plain, (![A_22, B_23]: (k5_relat_1(k6_relat_1(A_22), B_23)=k7_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 20.73/11.37  tff(c_318, plain, (![B_64, C_65, A_66]: (k7_relat_1(k5_relat_1(B_64, C_65), A_66)=k5_relat_1(k7_relat_1(B_64, A_66), C_65) | ~v1_relat_1(C_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.73/11.37  tff(c_340, plain, (![A_22, A_66, B_23]: (k5_relat_1(k7_relat_1(k6_relat_1(A_22), A_66), B_23)=k7_relat_1(k7_relat_1(B_23, A_22), A_66) | ~v1_relat_1(B_23) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(B_23))), inference(superposition, [status(thm), theory('equality')], [c_28, c_318])).
% 20.73/11.37  tff(c_348, plain, (![A_22, A_66, B_23]: (k5_relat_1(k7_relat_1(k6_relat_1(A_22), A_66), B_23)=k7_relat_1(k7_relat_1(B_23, A_22), A_66) | ~v1_relat_1(B_23))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_340])).
% 20.73/11.37  tff(c_945, plain, (![A_119, A_120, B_121]: (k5_relat_1(k7_relat_1(k6_relat_1(A_119), A_120), B_121)=k7_relat_1(k7_relat_1(B_121, A_119), A_120) | ~v1_relat_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_340])).
% 20.73/11.37  tff(c_984, plain, (![B_122, A_123]: (k7_relat_1(k7_relat_1(B_122, A_123), A_123)=k5_relat_1(k6_relat_1(A_123), B_122) | ~v1_relat_1(B_122))), inference(superposition, [status(thm), theory('equality')], [c_77, c_945])).
% 20.73/11.37  tff(c_1023, plain, (![A_19]: (k5_relat_1(k6_relat_1(A_19), k6_relat_1(A_19))=k7_relat_1(k6_relat_1(A_19), A_19) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_984])).
% 20.73/11.37  tff(c_1032, plain, (![A_19]: (k5_relat_1(k6_relat_1(A_19), k6_relat_1(A_19))=k6_relat_1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_77, c_1023])).
% 20.73/11.37  tff(c_1033, plain, (![A_124]: (k5_relat_1(k6_relat_1(A_124), k6_relat_1(A_124))=k6_relat_1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_77, c_1023])).
% 20.73/11.37  tff(c_14, plain, (![B_10, C_12, A_9]: (k7_relat_1(k5_relat_1(B_10, C_12), A_9)=k5_relat_1(k7_relat_1(B_10, A_9), C_12) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.73/11.37  tff(c_1054, plain, (![A_124, A_9]: (k5_relat_1(k7_relat_1(k6_relat_1(A_124), A_9), k6_relat_1(A_124))=k7_relat_1(k6_relat_1(A_124), A_9) | ~v1_relat_1(k6_relat_1(A_124)) | ~v1_relat_1(k6_relat_1(A_124)))), inference(superposition, [status(thm), theory('equality')], [c_1033, c_14])).
% 20.73/11.37  tff(c_1079, plain, (![A_124, A_9]: (k5_relat_1(k7_relat_1(k6_relat_1(A_124), A_9), k6_relat_1(A_124))=k7_relat_1(k6_relat_1(A_124), A_9))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_1054])).
% 20.73/11.37  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 20.73/11.37  tff(c_1886, plain, (![B_171, A_172, C_173]: (v1_relat_1(k5_relat_1(k7_relat_1(B_171, A_172), C_173)) | ~v1_relat_1(k5_relat_1(B_171, C_173)) | ~v1_relat_1(C_173) | ~v1_relat_1(B_171))), inference(superposition, [status(thm), theory('equality')], [c_318, c_12])).
% 20.73/11.37  tff(c_1889, plain, (![A_124, A_9]: (v1_relat_1(k7_relat_1(k6_relat_1(A_124), A_9)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_124), k6_relat_1(A_124))) | ~v1_relat_1(k6_relat_1(A_124)) | ~v1_relat_1(k6_relat_1(A_124)))), inference(superposition, [status(thm), theory('equality')], [c_1079, c_1886])).
% 20.73/11.37  tff(c_1909, plain, (![A_124, A_9]: (v1_relat_1(k7_relat_1(k6_relat_1(A_124), A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_1032, c_1889])).
% 20.73/11.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.73/11.37  tff(c_32, plain, (![A_26]: (k7_relat_1(A_26, k1_relat_1(A_26))=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 20.73/11.37  tff(c_24, plain, (![A_20, B_21]: (r1_tarski(k5_relat_1(k6_relat_1(A_20), B_21), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.73/11.37  tff(c_94, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.73/11.37  tff(c_1272, plain, (![A_135, B_136]: (k5_relat_1(k6_relat_1(A_135), B_136)=B_136 | ~r1_tarski(B_136, k5_relat_1(k6_relat_1(A_135), B_136)) | ~v1_relat_1(B_136))), inference(resolution, [status(thm)], [c_24, c_94])).
% 20.73/11.37  tff(c_6121, plain, (![A_323, B_324]: (k5_relat_1(k6_relat_1(A_323), B_324)=B_324 | ~r1_tarski(B_324, k7_relat_1(B_324, A_323)) | ~v1_relat_1(B_324) | ~v1_relat_1(B_324))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1272])).
% 20.73/11.37  tff(c_6139, plain, (![A_26]: (k5_relat_1(k6_relat_1(k1_relat_1(A_26)), A_26)=A_26 | ~r1_tarski(A_26, A_26) | ~v1_relat_1(A_26) | ~v1_relat_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6121])).
% 20.73/11.37  tff(c_6146, plain, (![A_325]: (k5_relat_1(k6_relat_1(k1_relat_1(A_325)), A_325)=A_325 | ~v1_relat_1(A_325))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6139])).
% 20.73/11.37  tff(c_6235, plain, (![A_325, A_9]: (k5_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(A_325)), A_9), A_325)=k7_relat_1(A_325, A_9) | ~v1_relat_1(A_325) | ~v1_relat_1(k6_relat_1(k1_relat_1(A_325))) | ~v1_relat_1(A_325))), inference(superposition, [status(thm), theory('equality')], [c_6146, c_14])).
% 20.73/11.37  tff(c_6302, plain, (![A_325, A_9]: (k5_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(A_325)), A_9), A_325)=k7_relat_1(A_325, A_9) | ~v1_relat_1(A_325))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6235])).
% 20.73/11.37  tff(c_26, plain, (![B_21, A_20]: (r1_tarski(k5_relat_1(B_21, k6_relat_1(A_20)), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.73/11.37  tff(c_169, plain, (![A_50, C_51, B_52]: (r1_tarski(A_50, C_51) | ~r1_tarski(B_52, C_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.73/11.37  tff(c_485, plain, (![A_76, B_77, A_78]: (r1_tarski(A_76, B_77) | ~r1_tarski(A_76, k5_relat_1(B_77, k6_relat_1(A_78))) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_26, c_169])).
% 20.73/11.37  tff(c_8789, plain, (![B_410, A_411, A_412]: (r1_tarski(k5_relat_1(k5_relat_1(B_410, k6_relat_1(A_411)), k6_relat_1(A_412)), B_410) | ~v1_relat_1(B_410) | ~v1_relat_1(k5_relat_1(B_410, k6_relat_1(A_411))))), inference(resolution, [status(thm)], [c_26, c_485])).
% 20.73/11.37  tff(c_8888, plain, (![A_411, A_9, A_412]: (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(A_411), A_9), k6_relat_1(A_412)), k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_411))), A_9)) | ~v1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_411))), A_9)) | ~v1_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(A_411))), A_9), k6_relat_1(A_411))) | ~v1_relat_1(k6_relat_1(A_411)))), inference(superposition, [status(thm), theory('equality')], [c_6302, c_8789])).
% 20.73/11.37  tff(c_8994, plain, (![A_413, A_414, A_415]: (r1_tarski(k5_relat_1(k7_relat_1(k6_relat_1(A_413), A_414), k6_relat_1(A_415)), k7_relat_1(k6_relat_1(A_413), A_414)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1909, c_1079, c_20, c_1909, c_20, c_20, c_8888])).
% 20.73/11.37  tff(c_9050, plain, (![A_415, A_22, A_66]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_415), A_22), A_66), k7_relat_1(k6_relat_1(A_22), A_66)) | ~v1_relat_1(k6_relat_1(A_415)))), inference(superposition, [status(thm), theory('equality')], [c_348, c_8994])).
% 20.73/11.37  tff(c_9336, plain, (![A_425, A_426, A_427]: (r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(A_425), A_426), A_427), k7_relat_1(k6_relat_1(A_426), A_427)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9050])).
% 20.73/11.37  tff(c_11261, plain, (![A_460, A_461, A_462]: (r1_tarski(k7_relat_1(k6_relat_1(A_460), A_461), k7_relat_1(k6_relat_1(A_462), A_461)) | ~r1_tarski(A_460, A_462))), inference(superposition, [status(thm), theory('equality')], [c_233, c_9336])).
% 20.73/11.37  tff(c_11347, plain, (![A_463, A_464]: (r1_tarski(k6_relat_1(A_463), k7_relat_1(k6_relat_1(A_464), A_463)) | ~r1_tarski(A_463, A_464))), inference(superposition, [status(thm), theory('equality')], [c_77, c_11261])).
% 20.73/11.37  tff(c_137, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=k7_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_75])).
% 20.73/11.37  tff(c_147, plain, (![A_20, A_46]: (r1_tarski(k7_relat_1(k6_relat_1(A_20), A_46), k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_26])).
% 20.73/11.37  tff(c_155, plain, (![A_48, A_49]: (r1_tarski(k7_relat_1(k6_relat_1(A_48), A_49), k6_relat_1(A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_147])).
% 20.73/11.37  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.73/11.37  tff(c_165, plain, (![A_48, A_49]: (k7_relat_1(k6_relat_1(A_48), A_49)=k6_relat_1(A_49) | ~r1_tarski(k6_relat_1(A_49), k7_relat_1(k6_relat_1(A_48), A_49)))), inference(resolution, [status(thm)], [c_155, c_2])).
% 20.73/11.37  tff(c_11448, plain, (![A_465, A_466]: (k7_relat_1(k6_relat_1(A_465), A_466)=k6_relat_1(A_466) | ~r1_tarski(A_466, A_465))), inference(resolution, [status(thm)], [c_11347, c_165])).
% 20.73/11.37  tff(c_16, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 20.73/11.37  tff(c_11763, plain, (![A_465, A_466]: (k9_relat_1(k6_relat_1(A_465), A_466)=k2_relat_1(k6_relat_1(A_466)) | ~v1_relat_1(k6_relat_1(A_465)) | ~r1_tarski(A_466, A_465))), inference(superposition, [status(thm), theory('equality')], [c_11448, c_16])).
% 20.73/11.37  tff(c_11904, plain, (![A_469, A_470]: (k9_relat_1(k6_relat_1(A_469), A_470)=A_470 | ~r1_tarski(A_470, A_469))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22, c_11763])).
% 20.73/11.37  tff(c_512, plain, (![B_79, C_80, A_81]: (k9_relat_1(k5_relat_1(B_79, C_80), A_81)=k9_relat_1(C_80, k9_relat_1(B_79, A_81)) | ~v1_relat_1(C_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_61])).
% 20.73/11.37  tff(c_529, plain, (![B_23, A_22, A_81]: (k9_relat_1(B_23, k9_relat_1(k6_relat_1(A_22), A_81))=k9_relat_1(k7_relat_1(B_23, A_22), A_81) | ~v1_relat_1(B_23) | ~v1_relat_1(k6_relat_1(A_22)) | ~v1_relat_1(B_23))), inference(superposition, [status(thm), theory('equality')], [c_28, c_512])).
% 20.73/11.37  tff(c_533, plain, (![B_23, A_22, A_81]: (k9_relat_1(B_23, k9_relat_1(k6_relat_1(A_22), A_81))=k9_relat_1(k7_relat_1(B_23, A_22), A_81) | ~v1_relat_1(B_23))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_529])).
% 20.73/11.37  tff(c_54367, plain, (![B_1018, A_1019, A_1020]: (k9_relat_1(k7_relat_1(B_1018, A_1019), A_1020)=k9_relat_1(B_1018, A_1020) | ~v1_relat_1(B_1018) | ~r1_tarski(A_1020, A_1019))), inference(superposition, [status(thm), theory('equality')], [c_11904, c_533])).
% 20.73/11.37  tff(c_34, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 20.73/11.37  tff(c_54452, plain, (~v1_relat_1('#skF_1') | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_54367, c_34])).
% 20.73/11.37  tff(c_54562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_54452])).
% 20.73/11.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.73/11.37  
% 20.73/11.37  Inference rules
% 20.73/11.37  ----------------------
% 20.73/11.37  #Ref     : 0
% 20.73/11.37  #Sup     : 14774
% 20.73/11.37  #Fact    : 0
% 20.73/11.37  #Define  : 0
% 20.73/11.37  #Split   : 5
% 20.73/11.37  #Chain   : 0
% 20.73/11.37  #Close   : 0
% 20.73/11.37  
% 20.73/11.37  Ordering : KBO
% 20.73/11.37  
% 20.73/11.37  Simplification rules
% 20.73/11.37  ----------------------
% 20.73/11.37  #Subsume      : 3237
% 20.73/11.37  #Demod        : 6917
% 20.73/11.37  #Tautology    : 2105
% 20.73/11.37  #SimpNegUnit  : 0
% 20.73/11.37  #BackRed      : 1
% 20.73/11.37  
% 20.73/11.37  #Partial instantiations: 0
% 20.73/11.37  #Strategies tried      : 1
% 20.73/11.37  
% 20.73/11.37  Timing (in seconds)
% 20.73/11.37  ----------------------
% 20.73/11.37  Preprocessing        : 0.31
% 20.73/11.37  Parsing              : 0.16
% 20.73/11.37  CNF conversion       : 0.02
% 20.73/11.37  Main loop            : 10.22
% 20.73/11.38  Inferencing          : 1.43
% 20.73/11.38  Reduction            : 3.24
% 20.73/11.38  Demodulation         : 2.68
% 20.73/11.38  BG Simplification    : 0.22
% 20.73/11.38  Subsumption          : 4.80
% 20.73/11.38  Abstraction          : 0.31
% 20.73/11.38  MUC search           : 0.00
% 20.73/11.38  Cooper               : 0.00
% 20.73/11.38  Total                : 10.56
% 20.73/11.38  Index Insertion      : 0.00
% 20.73/11.38  Index Deletion       : 0.00
% 20.73/11.38  Index Matching       : 0.00
% 20.73/11.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
