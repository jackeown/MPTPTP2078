%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:28 EST 2020

% Result     : Theorem 21.86s
% Output     : CNFRefutation 21.86s
% Verified   : 
% Statistics : Number of formulae       :  104 (4951 expanded)
%              Number of leaves         :   27 (1686 expanded)
%              Depth                    :   37
%              Number of atoms          :  195 (11628 expanded)
%              Number of equality atoms :   70 (4026 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_32,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( v1_relat_1(k7_relat_1(A_34,B_35))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_155,plain,(
    ! [C_72,B_73,A_74] :
      ( k7_relat_1(k7_relat_1(C_72,B_73),A_74) = k7_relat_1(C_72,A_74)
      | ~ r1_tarski(A_74,B_73)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [C_41,B_40,A_39] :
      ( k7_relat_1(k7_relat_1(C_41,B_40),A_39) = k7_relat_1(C_41,A_39)
      | ~ r1_tarski(A_39,B_40)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3001,plain,(
    ! [C_177,B_178,A_179,A_180] :
      ( k7_relat_1(k7_relat_1(C_177,B_178),A_179) = k7_relat_1(k7_relat_1(C_177,A_180),A_179)
      | ~ r1_tarski(A_179,A_180)
      | ~ v1_relat_1(k7_relat_1(C_177,B_178))
      | ~ r1_tarski(A_180,B_178)
      | ~ v1_relat_1(C_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_28])).

tff(c_3354,plain,(
    ! [A_187,B_188,A_189,A_190] :
      ( k7_relat_1(k7_relat_1(A_187,B_188),A_189) = k7_relat_1(k7_relat_1(A_187,A_190),A_189)
      | ~ r1_tarski(A_189,A_190)
      | ~ r1_tarski(A_190,B_188)
      | ~ v1_relat_1(A_187) ) ),
    inference(resolution,[status(thm)],[c_24,c_3001])).

tff(c_3359,plain,(
    ! [A_187,A_189] :
      ( k7_relat_1(k7_relat_1(A_187,k10_relat_1('#skF_1','#skF_3')),A_189) = k7_relat_1(k7_relat_1(A_187,'#skF_2'),A_189)
      | ~ r1_tarski(A_189,k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(A_187) ) ),
    inference(resolution,[status(thm)],[c_34,c_3354])).

tff(c_3604,plain,(
    ! [A_206,A_207] :
      ( k7_relat_1(k7_relat_1(A_206,k10_relat_1('#skF_1','#skF_3')),A_207) = k7_relat_1(k7_relat_1(A_206,'#skF_2'),A_207)
      | ~ r1_tarski(A_207,k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(A_206) ) ),
    inference(resolution,[status(thm)],[c_34,c_3354])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [C_38,A_36,B_37] :
      ( k7_relat_1(k7_relat_1(C_38,A_36),B_37) = k7_relat_1(C_38,k3_xboole_0(A_36,B_37))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_98,plain,(
    ! [C_64,A_65,B_66] :
      ( k7_relat_1(k7_relat_1(C_64,A_65),B_66) = k7_relat_1(C_64,k3_xboole_0(A_65,B_66))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_259,plain,(
    ! [C_96,A_97,B_98,B_99] :
      ( k7_relat_1(k7_relat_1(C_96,k3_xboole_0(A_97,B_98)),B_99) = k7_relat_1(k7_relat_1(C_96,A_97),k3_xboole_0(B_98,B_99))
      | ~ v1_relat_1(k7_relat_1(C_96,A_97))
      | ~ v1_relat_1(C_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_98])).

tff(c_328,plain,(
    ! [C_100,A_101,B_102] :
      ( k7_relat_1(k7_relat_1(C_100,A_101),k3_xboole_0(A_101,B_102)) = k7_relat_1(k7_relat_1(C_100,A_101),B_102)
      | ~ v1_relat_1(k7_relat_1(C_100,A_101))
      | ~ v1_relat_1(C_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_259])).

tff(c_405,plain,(
    ! [C_103,A_104,B_105] :
      ( k7_relat_1(C_103,k3_xboole_0(A_104,k3_xboole_0(A_104,B_105))) = k7_relat_1(k7_relat_1(C_103,A_104),B_105)
      | ~ v1_relat_1(C_103)
      | ~ v1_relat_1(k7_relat_1(C_103,A_104))
      | ~ v1_relat_1(C_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_26])).

tff(c_471,plain,(
    ! [C_103,A_1] :
      ( k7_relat_1(k7_relat_1(C_103,A_1),A_1) = k7_relat_1(C_103,k3_xboole_0(A_1,A_1))
      | ~ v1_relat_1(C_103)
      | ~ v1_relat_1(k7_relat_1(C_103,A_1))
      | ~ v1_relat_1(C_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_405])).

tff(c_475,plain,(
    ! [C_106,A_107] :
      ( k7_relat_1(k7_relat_1(C_106,A_107),A_107) = k7_relat_1(C_106,A_107)
      | ~ v1_relat_1(C_106)
      | ~ v1_relat_1(k7_relat_1(C_106,A_107))
      | ~ v1_relat_1(C_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_471])).

tff(c_490,plain,(
    ! [A_34,B_35] :
      ( k7_relat_1(k7_relat_1(A_34,B_35),B_35) = k7_relat_1(A_34,B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_24,c_475])).

tff(c_3728,plain,(
    ! [A_206] :
      ( k7_relat_1(k7_relat_1(A_206,'#skF_2'),k10_relat_1('#skF_1','#skF_3')) = k7_relat_1(A_206,k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(A_206)
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(A_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3604,c_490])).

tff(c_3868,plain,(
    ! [A_206] :
      ( k7_relat_1(k7_relat_1(A_206,'#skF_2'),k10_relat_1('#skF_1','#skF_3')) = k7_relat_1(A_206,k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3728])).

tff(c_491,plain,(
    ! [A_108,B_109] :
      ( k7_relat_1(k7_relat_1(A_108,B_109),B_109) = k7_relat_1(A_108,B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(resolution,[status(thm)],[c_24,c_475])).

tff(c_696,plain,(
    ! [C_113,B_114,A_115] :
      ( k7_relat_1(k7_relat_1(C_113,B_114),A_115) = k7_relat_1(k7_relat_1(C_113,A_115),A_115)
      | ~ v1_relat_1(k7_relat_1(C_113,B_114))
      | ~ r1_tarski(A_115,B_114)
      | ~ v1_relat_1(C_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_491])).

tff(c_715,plain,(
    ! [A_34,B_35,A_115] :
      ( k7_relat_1(k7_relat_1(A_34,B_35),A_115) = k7_relat_1(k7_relat_1(A_34,A_115),A_115)
      | ~ r1_tarski(A_115,B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_24,c_696])).

tff(c_40447,plain,(
    ! [A_523,A_524] :
      ( k7_relat_1(k7_relat_1(A_523,A_524),A_524) = k7_relat_1(k7_relat_1(A_523,'#skF_2'),A_524)
      | ~ r1_tarski(A_524,k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(A_523)
      | ~ r1_tarski(A_524,k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(A_523) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_3604])).

tff(c_40450,plain,(
    ! [A_523] :
      ( k7_relat_1(k7_relat_1(A_523,k10_relat_1('#skF_1','#skF_3')),k10_relat_1('#skF_1','#skF_3')) = k7_relat_1(k7_relat_1(A_523,'#skF_2'),k10_relat_1('#skF_1','#skF_3'))
      | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(A_523) ) ),
    inference(resolution,[status(thm)],[c_8,c_40447])).

tff(c_40454,plain,(
    ! [A_525] :
      ( k7_relat_1(k7_relat_1(A_525,k10_relat_1('#skF_1','#skF_3')),k10_relat_1('#skF_1','#skF_3')) = k7_relat_1(k7_relat_1(A_525,'#skF_2'),k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(A_525) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_40450])).

tff(c_116,plain,(
    ! [A_67,C_68,B_69] :
      ( k3_xboole_0(A_67,k10_relat_1(C_68,B_69)) = k10_relat_1(k7_relat_1(C_68,A_67),B_69)
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_133,plain,(
    ! [C_70,B_71] :
      ( k10_relat_1(k7_relat_1(C_70,k10_relat_1(C_70,B_71)),B_71) = k10_relat_1(C_70,B_71)
      | ~ v1_relat_1(C_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_2])).

tff(c_30,plain,(
    ! [A_42,C_44,B_43] :
      ( k3_xboole_0(A_42,k10_relat_1(C_44,B_43)) = k10_relat_1(k7_relat_1(C_44,A_42),B_43)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_142,plain,(
    ! [C_70,B_71,A_42] :
      ( k10_relat_1(k7_relat_1(k7_relat_1(C_70,k10_relat_1(C_70,B_71)),A_42),B_71) = k3_xboole_0(A_42,k10_relat_1(C_70,B_71))
      | ~ v1_relat_1(k7_relat_1(C_70,k10_relat_1(C_70,B_71)))
      | ~ v1_relat_1(C_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_30])).

tff(c_40703,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')),'#skF_3') = k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),k10_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3')))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40454,c_142])).

tff(c_41009,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_2,c_40703])).

tff(c_41036,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_41009])).

tff(c_41039,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_41036])).

tff(c_41043,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_41039])).

tff(c_41044,plain,(
    k10_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_41009])).

tff(c_41086,plain,
    ( k10_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3')),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3868,c_41044])).

tff(c_41109,plain,(
    k10_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3')),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_41086])).

tff(c_40453,plain,(
    ! [A_523] :
      ( k7_relat_1(k7_relat_1(A_523,k10_relat_1('#skF_1','#skF_3')),k10_relat_1('#skF_1','#skF_3')) = k7_relat_1(k7_relat_1(A_523,'#skF_2'),k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(A_523) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_40450])).

tff(c_41045,plain,(
    v1_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_41009])).

tff(c_41141,plain,(
    ! [A_42] :
      ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3')),A_42),'#skF_3') = k3_xboole_0(A_42,k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41109,c_30])).

tff(c_41166,plain,(
    ! [A_42] : k10_relat_1(k7_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3')),A_42),'#skF_3') = k3_xboole_0(A_42,k10_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41045,c_41141])).

tff(c_716,plain,(
    ! [A_116,B_117,A_118] :
      ( k7_relat_1(k7_relat_1(A_116,B_117),A_118) = k7_relat_1(k7_relat_1(A_116,A_118),A_118)
      | ~ r1_tarski(A_118,B_117)
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_24,c_696])).

tff(c_1519,plain,(
    ! [A_143,A_144,B_145] :
      ( k7_relat_1(k7_relat_1(A_143,A_144),A_144) = k7_relat_1(A_143,k3_xboole_0(B_145,A_144))
      | ~ v1_relat_1(A_143)
      | ~ r1_tarski(A_144,B_145)
      | ~ v1_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_716,c_26])).

tff(c_1687,plain,(
    ! [A_143,B_145,A_144] :
      ( k7_relat_1(A_143,k3_xboole_0(B_145,A_144)) = k7_relat_1(A_143,A_144)
      | ~ r1_tarski(A_144,A_144)
      | ~ v1_relat_1(A_143)
      | ~ v1_relat_1(A_143)
      | ~ r1_tarski(A_144,B_145)
      | ~ v1_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1519,c_28])).

tff(c_1835,plain,(
    ! [A_143,B_145,A_144] :
      ( k7_relat_1(A_143,k3_xboole_0(B_145,A_144)) = k7_relat_1(A_143,A_144)
      | ~ r1_tarski(A_144,B_145)
      | ~ v1_relat_1(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1687])).

tff(c_41398,plain,(
    ! [A_526] : k10_relat_1(k7_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3')),A_526),'#skF_3') = k3_xboole_0(A_526,k10_relat_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41045,c_41141])).

tff(c_41589,plain,(
    ! [B_145,A_144] :
      ( k3_xboole_0(k3_xboole_0(B_145,A_144),k10_relat_1('#skF_1','#skF_3')) = k10_relat_1(k7_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3')),A_144),'#skF_3')
      | ~ r1_tarski(A_144,B_145)
      | ~ v1_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1835,c_41398])).

tff(c_43359,plain,(
    ! [B_534,A_535] :
      ( k3_xboole_0(k3_xboole_0(B_534,A_535),k10_relat_1('#skF_1','#skF_3')) = k3_xboole_0(A_535,k10_relat_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_535,B_534) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41045,c_41166,c_41589])).

tff(c_43489,plain,(
    ! [B_534,A_535] :
      ( k10_relat_1(k7_relat_1('#skF_1',k3_xboole_0(B_534,A_535)),'#skF_3') = k3_xboole_0(A_535,k10_relat_1('#skF_1','#skF_3'))
      | ~ v1_relat_1('#skF_1')
      | ~ r1_tarski(A_535,B_534) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43359,c_30])).

tff(c_44532,plain,(
    ! [B_542,A_543] :
      ( k10_relat_1(k7_relat_1('#skF_1',k3_xboole_0(B_542,A_543)),'#skF_3') = k3_xboole_0(A_543,k10_relat_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_543,B_542) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_43489])).

tff(c_44683,plain,(
    ! [A_1] :
      ( k3_xboole_0(A_1,k10_relat_1('#skF_1','#skF_3')) = k10_relat_1(k7_relat_1('#skF_1',A_1),'#skF_3')
      | ~ r1_tarski(A_1,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_44532])).

tff(c_44749,plain,(
    ! [A_1] : k3_xboole_0(A_1,k10_relat_1('#skF_1','#skF_3')) = k10_relat_1(k7_relat_1('#skF_1',A_1),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_44683])).

tff(c_17205,plain,(
    ! [A_403,A_404,B_405] :
      ( k7_relat_1(k7_relat_1(k7_relat_1(A_403,A_404),A_404),A_404) = k7_relat_1(k7_relat_1(A_403,B_405),A_404)
      | ~ v1_relat_1(k7_relat_1(A_403,B_405))
      | ~ r1_tarski(A_404,B_405)
      | ~ v1_relat_1(A_403) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_716,c_490])).

tff(c_17298,plain,(
    ! [A_406,A_407,B_408] :
      ( k7_relat_1(k7_relat_1(k7_relat_1(A_406,A_407),A_407),A_407) = k7_relat_1(k7_relat_1(A_406,B_408),A_407)
      | ~ r1_tarski(A_407,B_408)
      | ~ v1_relat_1(A_406) ) ),
    inference(resolution,[status(thm)],[c_24,c_17205])).

tff(c_17811,plain,(
    ! [A_406,A_407,B_408] :
      ( k7_relat_1(k7_relat_1(k7_relat_1(A_406,A_407),A_407),A_407) = k7_relat_1(A_406,k3_xboole_0(B_408,A_407))
      | ~ v1_relat_1(A_406)
      | ~ r1_tarski(A_407,B_408)
      | ~ v1_relat_1(A_406) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17298,c_26])).

tff(c_44621,plain,(
    ! [A_407,B_408] :
      ( k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1',A_407),A_407),A_407),'#skF_3') = k3_xboole_0(A_407,k10_relat_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_407,B_408)
      | ~ v1_relat_1('#skF_1')
      | ~ r1_tarski(A_407,B_408)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17811,c_44532])).

tff(c_44719,plain,(
    ! [A_407,B_408] :
      ( k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1',A_407),A_407),A_407),'#skF_3') = k3_xboole_0(A_407,k10_relat_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_407,B_408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_44621])).

tff(c_54638,plain,(
    ! [A_590,B_591] :
      ( k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1',A_590),A_590),A_590),'#skF_3') = k10_relat_1(k7_relat_1('#skF_1',A_590),'#skF_3')
      | ~ r1_tarski(A_590,B_591) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44749,c_44719])).

tff(c_54647,plain,(
    ! [B_592] : k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1',B_592),B_592),B_592),'#skF_3') = k10_relat_1(k7_relat_1('#skF_1',B_592),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_54638])).

tff(c_54725,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')),k10_relat_1('#skF_1','#skF_3')),'#skF_3') = k10_relat_1(k7_relat_1('#skF_1',k10_relat_1('#skF_1','#skF_3')),'#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40453,c_54647])).

tff(c_55159,plain,(
    k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),k10_relat_1('#skF_1','#skF_3')),k10_relat_1('#skF_1','#skF_3')),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_41109,c_54725])).

tff(c_55360,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_2'),k10_relat_1('#skF_1','#skF_3')),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1('#skF_1','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3359,c_55159])).

tff(c_55427,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_2'),k10_relat_1('#skF_1','#skF_3')),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_55360])).

tff(c_64399,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_55427])).

tff(c_64402,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_64399])).

tff(c_64406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64402])).

tff(c_64408,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_55427])).

tff(c_64407,plain,(
    k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_2'),k10_relat_1('#skF_1','#skF_3')),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_55427])).

tff(c_64495,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3'))),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_64407])).

tff(c_64542,plain,(
    k10_relat_1(k7_relat_1(k7_relat_1('#skF_1','#skF_2'),k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3')),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64408,c_44749,c_64495])).

tff(c_123,plain,(
    ! [C_68,B_69] :
      ( k10_relat_1(k7_relat_1(C_68,k10_relat_1(C_68,B_69)),B_69) = k10_relat_1(C_68,B_69)
      | ~ v1_relat_1(C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_2])).

tff(c_65661,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64542,c_123])).

tff(c_65719,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64408,c_65661])).

tff(c_65721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_65719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.86/11.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.86/11.23  
% 21.86/11.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.86/11.23  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 21.86/11.23  
% 21.86/11.23  %Foreground sorts:
% 21.86/11.23  
% 21.86/11.23  
% 21.86/11.23  %Background operators:
% 21.86/11.23  
% 21.86/11.23  
% 21.86/11.23  %Foreground operators:
% 21.86/11.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.86/11.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.86/11.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 21.86/11.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 21.86/11.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.86/11.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 21.86/11.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.86/11.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 21.86/11.23  tff('#skF_2', type, '#skF_2': $i).
% 21.86/11.23  tff('#skF_3', type, '#skF_3': $i).
% 21.86/11.23  tff('#skF_1', type, '#skF_1': $i).
% 21.86/11.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 21.86/11.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 21.86/11.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.86/11.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 21.86/11.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.86/11.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.86/11.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.86/11.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 21.86/11.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 21.86/11.23  
% 21.86/11.25  tff(f_75, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 21.86/11.25  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 21.86/11.25  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 21.86/11.25  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 21.86/11.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 21.86/11.25  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 21.86/11.25  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 21.86/11.25  tff(c_32, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.86/11.25  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.86/11.25  tff(c_24, plain, (![A_34, B_35]: (v1_relat_1(k7_relat_1(A_34, B_35)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.86/11.25  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 21.86/11.25  tff(c_34, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.86/11.25  tff(c_155, plain, (![C_72, B_73, A_74]: (k7_relat_1(k7_relat_1(C_72, B_73), A_74)=k7_relat_1(C_72, A_74) | ~r1_tarski(A_74, B_73) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_61])).
% 21.86/11.25  tff(c_28, plain, (![C_41, B_40, A_39]: (k7_relat_1(k7_relat_1(C_41, B_40), A_39)=k7_relat_1(C_41, A_39) | ~r1_tarski(A_39, B_40) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 21.86/11.25  tff(c_3001, plain, (![C_177, B_178, A_179, A_180]: (k7_relat_1(k7_relat_1(C_177, B_178), A_179)=k7_relat_1(k7_relat_1(C_177, A_180), A_179) | ~r1_tarski(A_179, A_180) | ~v1_relat_1(k7_relat_1(C_177, B_178)) | ~r1_tarski(A_180, B_178) | ~v1_relat_1(C_177))), inference(superposition, [status(thm), theory('equality')], [c_155, c_28])).
% 21.86/11.25  tff(c_3354, plain, (![A_187, B_188, A_189, A_190]: (k7_relat_1(k7_relat_1(A_187, B_188), A_189)=k7_relat_1(k7_relat_1(A_187, A_190), A_189) | ~r1_tarski(A_189, A_190) | ~r1_tarski(A_190, B_188) | ~v1_relat_1(A_187))), inference(resolution, [status(thm)], [c_24, c_3001])).
% 21.86/11.25  tff(c_3359, plain, (![A_187, A_189]: (k7_relat_1(k7_relat_1(A_187, k10_relat_1('#skF_1', '#skF_3')), A_189)=k7_relat_1(k7_relat_1(A_187, '#skF_2'), A_189) | ~r1_tarski(A_189, k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(A_187))), inference(resolution, [status(thm)], [c_34, c_3354])).
% 21.86/11.25  tff(c_3604, plain, (![A_206, A_207]: (k7_relat_1(k7_relat_1(A_206, k10_relat_1('#skF_1', '#skF_3')), A_207)=k7_relat_1(k7_relat_1(A_206, '#skF_2'), A_207) | ~r1_tarski(A_207, k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(A_206))), inference(resolution, [status(thm)], [c_34, c_3354])).
% 21.86/11.25  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.86/11.25  tff(c_26, plain, (![C_38, A_36, B_37]: (k7_relat_1(k7_relat_1(C_38, A_36), B_37)=k7_relat_1(C_38, k3_xboole_0(A_36, B_37)) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.86/11.25  tff(c_98, plain, (![C_64, A_65, B_66]: (k7_relat_1(k7_relat_1(C_64, A_65), B_66)=k7_relat_1(C_64, k3_xboole_0(A_65, B_66)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.86/11.25  tff(c_259, plain, (![C_96, A_97, B_98, B_99]: (k7_relat_1(k7_relat_1(C_96, k3_xboole_0(A_97, B_98)), B_99)=k7_relat_1(k7_relat_1(C_96, A_97), k3_xboole_0(B_98, B_99)) | ~v1_relat_1(k7_relat_1(C_96, A_97)) | ~v1_relat_1(C_96))), inference(superposition, [status(thm), theory('equality')], [c_26, c_98])).
% 21.86/11.25  tff(c_328, plain, (![C_100, A_101, B_102]: (k7_relat_1(k7_relat_1(C_100, A_101), k3_xboole_0(A_101, B_102))=k7_relat_1(k7_relat_1(C_100, A_101), B_102) | ~v1_relat_1(k7_relat_1(C_100, A_101)) | ~v1_relat_1(C_100))), inference(superposition, [status(thm), theory('equality')], [c_2, c_259])).
% 21.86/11.25  tff(c_405, plain, (![C_103, A_104, B_105]: (k7_relat_1(C_103, k3_xboole_0(A_104, k3_xboole_0(A_104, B_105)))=k7_relat_1(k7_relat_1(C_103, A_104), B_105) | ~v1_relat_1(C_103) | ~v1_relat_1(k7_relat_1(C_103, A_104)) | ~v1_relat_1(C_103))), inference(superposition, [status(thm), theory('equality')], [c_328, c_26])).
% 21.86/11.25  tff(c_471, plain, (![C_103, A_1]: (k7_relat_1(k7_relat_1(C_103, A_1), A_1)=k7_relat_1(C_103, k3_xboole_0(A_1, A_1)) | ~v1_relat_1(C_103) | ~v1_relat_1(k7_relat_1(C_103, A_1)) | ~v1_relat_1(C_103))), inference(superposition, [status(thm), theory('equality')], [c_2, c_405])).
% 21.86/11.25  tff(c_475, plain, (![C_106, A_107]: (k7_relat_1(k7_relat_1(C_106, A_107), A_107)=k7_relat_1(C_106, A_107) | ~v1_relat_1(C_106) | ~v1_relat_1(k7_relat_1(C_106, A_107)) | ~v1_relat_1(C_106))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_471])).
% 21.86/11.25  tff(c_490, plain, (![A_34, B_35]: (k7_relat_1(k7_relat_1(A_34, B_35), B_35)=k7_relat_1(A_34, B_35) | ~v1_relat_1(A_34))), inference(resolution, [status(thm)], [c_24, c_475])).
% 21.86/11.25  tff(c_3728, plain, (![A_206]: (k7_relat_1(k7_relat_1(A_206, '#skF_2'), k10_relat_1('#skF_1', '#skF_3'))=k7_relat_1(A_206, k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(A_206) | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(A_206))), inference(superposition, [status(thm), theory('equality')], [c_3604, c_490])).
% 21.86/11.25  tff(c_3868, plain, (![A_206]: (k7_relat_1(k7_relat_1(A_206, '#skF_2'), k10_relat_1('#skF_1', '#skF_3'))=k7_relat_1(A_206, k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(A_206))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3728])).
% 21.86/11.25  tff(c_491, plain, (![A_108, B_109]: (k7_relat_1(k7_relat_1(A_108, B_109), B_109)=k7_relat_1(A_108, B_109) | ~v1_relat_1(A_108))), inference(resolution, [status(thm)], [c_24, c_475])).
% 21.86/11.25  tff(c_696, plain, (![C_113, B_114, A_115]: (k7_relat_1(k7_relat_1(C_113, B_114), A_115)=k7_relat_1(k7_relat_1(C_113, A_115), A_115) | ~v1_relat_1(k7_relat_1(C_113, B_114)) | ~r1_tarski(A_115, B_114) | ~v1_relat_1(C_113))), inference(superposition, [status(thm), theory('equality')], [c_28, c_491])).
% 21.86/11.25  tff(c_715, plain, (![A_34, B_35, A_115]: (k7_relat_1(k7_relat_1(A_34, B_35), A_115)=k7_relat_1(k7_relat_1(A_34, A_115), A_115) | ~r1_tarski(A_115, B_35) | ~v1_relat_1(A_34))), inference(resolution, [status(thm)], [c_24, c_696])).
% 21.86/11.25  tff(c_40447, plain, (![A_523, A_524]: (k7_relat_1(k7_relat_1(A_523, A_524), A_524)=k7_relat_1(k7_relat_1(A_523, '#skF_2'), A_524) | ~r1_tarski(A_524, k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(A_523) | ~r1_tarski(A_524, k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(A_523))), inference(superposition, [status(thm), theory('equality')], [c_715, c_3604])).
% 21.86/11.25  tff(c_40450, plain, (![A_523]: (k7_relat_1(k7_relat_1(A_523, k10_relat_1('#skF_1', '#skF_3')), k10_relat_1('#skF_1', '#skF_3'))=k7_relat_1(k7_relat_1(A_523, '#skF_2'), k10_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(A_523))), inference(resolution, [status(thm)], [c_8, c_40447])).
% 21.86/11.25  tff(c_40454, plain, (![A_525]: (k7_relat_1(k7_relat_1(A_525, k10_relat_1('#skF_1', '#skF_3')), k10_relat_1('#skF_1', '#skF_3'))=k7_relat_1(k7_relat_1(A_525, '#skF_2'), k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(A_525))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_40450])).
% 21.86/11.25  tff(c_116, plain, (![A_67, C_68, B_69]: (k3_xboole_0(A_67, k10_relat_1(C_68, B_69))=k10_relat_1(k7_relat_1(C_68, A_67), B_69) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.86/11.25  tff(c_133, plain, (![C_70, B_71]: (k10_relat_1(k7_relat_1(C_70, k10_relat_1(C_70, B_71)), B_71)=k10_relat_1(C_70, B_71) | ~v1_relat_1(C_70))), inference(superposition, [status(thm), theory('equality')], [c_116, c_2])).
% 21.86/11.25  tff(c_30, plain, (![A_42, C_44, B_43]: (k3_xboole_0(A_42, k10_relat_1(C_44, B_43))=k10_relat_1(k7_relat_1(C_44, A_42), B_43) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.86/11.25  tff(c_142, plain, (![C_70, B_71, A_42]: (k10_relat_1(k7_relat_1(k7_relat_1(C_70, k10_relat_1(C_70, B_71)), A_42), B_71)=k3_xboole_0(A_42, k10_relat_1(C_70, B_71)) | ~v1_relat_1(k7_relat_1(C_70, k10_relat_1(C_70, B_71))) | ~v1_relat_1(C_70))), inference(superposition, [status(thm), theory('equality')], [c_133, c_30])).
% 21.86/11.25  tff(c_40703, plain, (k10_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3')), '#skF_3')=k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3'))) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40454, c_142])).
% 21.86/11.25  tff(c_41009, plain, (k10_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3')), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_2, c_40703])).
% 21.86/11.25  tff(c_41036, plain, (~v1_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3')))), inference(splitLeft, [status(thm)], [c_41009])).
% 21.86/11.25  tff(c_41039, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_41036])).
% 21.86/11.25  tff(c_41043, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_41039])).
% 21.86/11.25  tff(c_41044, plain, (k10_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3')), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_41009])).
% 21.86/11.25  tff(c_41086, plain, (k10_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3')), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3868, c_41044])).
% 21.86/11.25  tff(c_41109, plain, (k10_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3')), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_41086])).
% 21.86/11.25  tff(c_40453, plain, (![A_523]: (k7_relat_1(k7_relat_1(A_523, k10_relat_1('#skF_1', '#skF_3')), k10_relat_1('#skF_1', '#skF_3'))=k7_relat_1(k7_relat_1(A_523, '#skF_2'), k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(A_523))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_40450])).
% 21.86/11.25  tff(c_41045, plain, (v1_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_41009])).
% 21.86/11.25  tff(c_41141, plain, (![A_42]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3')), A_42), '#skF_3')=k3_xboole_0(A_42, k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_41109, c_30])).
% 21.86/11.25  tff(c_41166, plain, (![A_42]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3')), A_42), '#skF_3')=k3_xboole_0(A_42, k10_relat_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_41045, c_41141])).
% 21.86/11.25  tff(c_716, plain, (![A_116, B_117, A_118]: (k7_relat_1(k7_relat_1(A_116, B_117), A_118)=k7_relat_1(k7_relat_1(A_116, A_118), A_118) | ~r1_tarski(A_118, B_117) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_24, c_696])).
% 21.86/11.25  tff(c_1519, plain, (![A_143, A_144, B_145]: (k7_relat_1(k7_relat_1(A_143, A_144), A_144)=k7_relat_1(A_143, k3_xboole_0(B_145, A_144)) | ~v1_relat_1(A_143) | ~r1_tarski(A_144, B_145) | ~v1_relat_1(A_143))), inference(superposition, [status(thm), theory('equality')], [c_716, c_26])).
% 21.86/11.25  tff(c_1687, plain, (![A_143, B_145, A_144]: (k7_relat_1(A_143, k3_xboole_0(B_145, A_144))=k7_relat_1(A_143, A_144) | ~r1_tarski(A_144, A_144) | ~v1_relat_1(A_143) | ~v1_relat_1(A_143) | ~r1_tarski(A_144, B_145) | ~v1_relat_1(A_143))), inference(superposition, [status(thm), theory('equality')], [c_1519, c_28])).
% 21.86/11.25  tff(c_1835, plain, (![A_143, B_145, A_144]: (k7_relat_1(A_143, k3_xboole_0(B_145, A_144))=k7_relat_1(A_143, A_144) | ~r1_tarski(A_144, B_145) | ~v1_relat_1(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1687])).
% 21.86/11.25  tff(c_41398, plain, (![A_526]: (k10_relat_1(k7_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3')), A_526), '#skF_3')=k3_xboole_0(A_526, k10_relat_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_41045, c_41141])).
% 21.86/11.25  tff(c_41589, plain, (![B_145, A_144]: (k3_xboole_0(k3_xboole_0(B_145, A_144), k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1(k7_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3')), A_144), '#skF_3') | ~r1_tarski(A_144, B_145) | ~v1_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1835, c_41398])).
% 21.86/11.25  tff(c_43359, plain, (![B_534, A_535]: (k3_xboole_0(k3_xboole_0(B_534, A_535), k10_relat_1('#skF_1', '#skF_3'))=k3_xboole_0(A_535, k10_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(A_535, B_534))), inference(demodulation, [status(thm), theory('equality')], [c_41045, c_41166, c_41589])).
% 21.86/11.25  tff(c_43489, plain, (![B_534, A_535]: (k10_relat_1(k7_relat_1('#skF_1', k3_xboole_0(B_534, A_535)), '#skF_3')=k3_xboole_0(A_535, k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1('#skF_1') | ~r1_tarski(A_535, B_534))), inference(superposition, [status(thm), theory('equality')], [c_43359, c_30])).
% 21.86/11.25  tff(c_44532, plain, (![B_542, A_543]: (k10_relat_1(k7_relat_1('#skF_1', k3_xboole_0(B_542, A_543)), '#skF_3')=k3_xboole_0(A_543, k10_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(A_543, B_542))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_43489])).
% 21.86/11.25  tff(c_44683, plain, (![A_1]: (k3_xboole_0(A_1, k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1(k7_relat_1('#skF_1', A_1), '#skF_3') | ~r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_44532])).
% 21.86/11.25  tff(c_44749, plain, (![A_1]: (k3_xboole_0(A_1, k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1(k7_relat_1('#skF_1', A_1), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_44683])).
% 21.86/11.25  tff(c_17205, plain, (![A_403, A_404, B_405]: (k7_relat_1(k7_relat_1(k7_relat_1(A_403, A_404), A_404), A_404)=k7_relat_1(k7_relat_1(A_403, B_405), A_404) | ~v1_relat_1(k7_relat_1(A_403, B_405)) | ~r1_tarski(A_404, B_405) | ~v1_relat_1(A_403))), inference(superposition, [status(thm), theory('equality')], [c_716, c_490])).
% 21.86/11.25  tff(c_17298, plain, (![A_406, A_407, B_408]: (k7_relat_1(k7_relat_1(k7_relat_1(A_406, A_407), A_407), A_407)=k7_relat_1(k7_relat_1(A_406, B_408), A_407) | ~r1_tarski(A_407, B_408) | ~v1_relat_1(A_406))), inference(resolution, [status(thm)], [c_24, c_17205])).
% 21.86/11.25  tff(c_17811, plain, (![A_406, A_407, B_408]: (k7_relat_1(k7_relat_1(k7_relat_1(A_406, A_407), A_407), A_407)=k7_relat_1(A_406, k3_xboole_0(B_408, A_407)) | ~v1_relat_1(A_406) | ~r1_tarski(A_407, B_408) | ~v1_relat_1(A_406))), inference(superposition, [status(thm), theory('equality')], [c_17298, c_26])).
% 21.86/11.25  tff(c_44621, plain, (![A_407, B_408]: (k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1', A_407), A_407), A_407), '#skF_3')=k3_xboole_0(A_407, k10_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(A_407, B_408) | ~v1_relat_1('#skF_1') | ~r1_tarski(A_407, B_408) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_17811, c_44532])).
% 21.86/11.25  tff(c_44719, plain, (![A_407, B_408]: (k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1', A_407), A_407), A_407), '#skF_3')=k3_xboole_0(A_407, k10_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(A_407, B_408))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_44621])).
% 21.86/11.25  tff(c_54638, plain, (![A_590, B_591]: (k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1', A_590), A_590), A_590), '#skF_3')=k10_relat_1(k7_relat_1('#skF_1', A_590), '#skF_3') | ~r1_tarski(A_590, B_591))), inference(demodulation, [status(thm), theory('equality')], [c_44749, c_44719])).
% 21.86/11.25  tff(c_54647, plain, (![B_592]: (k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1', B_592), B_592), B_592), '#skF_3')=k10_relat_1(k7_relat_1('#skF_1', B_592), '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_54638])).
% 21.86/11.25  tff(c_54725, plain, (k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3')), k10_relat_1('#skF_1', '#skF_3')), '#skF_3')=k10_relat_1(k7_relat_1('#skF_1', k10_relat_1('#skF_1', '#skF_3')), '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40453, c_54647])).
% 21.86/11.25  tff(c_55159, plain, (k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), k10_relat_1('#skF_1', '#skF_3')), k10_relat_1('#skF_1', '#skF_3')), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_41109, c_54725])).
% 21.86/11.25  tff(c_55360, plain, (k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_2'), k10_relat_1('#skF_1', '#skF_3')), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1('#skF_1', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3359, c_55159])).
% 21.86/11.25  tff(c_55427, plain, (k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_2'), k10_relat_1('#skF_1', '#skF_3')), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_55360])).
% 21.86/11.25  tff(c_64399, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_55427])).
% 21.86/11.25  tff(c_64402, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_64399])).
% 21.86/11.25  tff(c_64406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_64402])).
% 21.86/11.25  tff(c_64408, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_55427])).
% 21.86/11.25  tff(c_64407, plain, (k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_2'), k10_relat_1('#skF_1', '#skF_3')), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_55427])).
% 21.86/11.25  tff(c_64495, plain, (k10_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_64407])).
% 21.86/11.25  tff(c_64542, plain, (k10_relat_1(k7_relat_1(k7_relat_1('#skF_1', '#skF_2'), k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64408, c_44749, c_64495])).
% 21.86/11.25  tff(c_123, plain, (![C_68, B_69]: (k10_relat_1(k7_relat_1(C_68, k10_relat_1(C_68, B_69)), B_69)=k10_relat_1(C_68, B_69) | ~v1_relat_1(C_68))), inference(superposition, [status(thm), theory('equality')], [c_116, c_2])).
% 21.86/11.25  tff(c_65661, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64542, c_123])).
% 21.86/11.25  tff(c_65719, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64408, c_65661])).
% 21.86/11.25  tff(c_65721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_65719])).
% 21.86/11.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.86/11.25  
% 21.86/11.25  Inference rules
% 21.86/11.25  ----------------------
% 21.86/11.25  #Ref     : 0
% 21.86/11.25  #Sup     : 17425
% 21.86/11.25  #Fact    : 0
% 21.86/11.25  #Define  : 0
% 21.86/11.25  #Split   : 4
% 21.86/11.25  #Chain   : 0
% 21.86/11.25  #Close   : 0
% 21.86/11.25  
% 21.86/11.25  Ordering : KBO
% 21.86/11.25  
% 21.86/11.25  Simplification rules
% 21.86/11.25  ----------------------
% 21.86/11.25  #Subsume      : 5398
% 21.86/11.25  #Demod        : 3196
% 21.86/11.25  #Tautology    : 777
% 21.86/11.25  #SimpNegUnit  : 5
% 21.86/11.25  #BackRed      : 8
% 21.86/11.25  
% 21.86/11.25  #Partial instantiations: 0
% 21.86/11.25  #Strategies tried      : 1
% 21.86/11.25  
% 21.86/11.25  Timing (in seconds)
% 21.86/11.25  ----------------------
% 21.86/11.25  Preprocessing        : 0.38
% 21.86/11.25  Parsing              : 0.18
% 21.86/11.25  CNF conversion       : 0.03
% 21.86/11.25  Main loop            : 10.10
% 21.86/11.25  Inferencing          : 2.78
% 21.86/11.25  Reduction            : 2.36
% 21.86/11.25  Demodulation         : 1.79
% 21.86/11.26  BG Simplification    : 0.54
% 21.86/11.26  Subsumption          : 3.95
% 21.86/11.26  Abstraction          : 0.62
% 21.86/11.26  MUC search           : 0.00
% 21.86/11.26  Cooper               : 0.00
% 21.86/11.26  Total                : 10.52
% 21.86/11.26  Index Insertion      : 0.00
% 21.86/11.26  Index Deletion       : 0.00
% 21.86/11.26  Index Matching       : 0.00
% 21.86/11.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
