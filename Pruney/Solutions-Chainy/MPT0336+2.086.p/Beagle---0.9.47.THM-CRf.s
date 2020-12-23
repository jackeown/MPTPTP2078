%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:12 EST 2020

% Result     : Theorem 21.49s
% Output     : CNFRefutation 21.49s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 229 expanded)
%              Number of leaves         :   28 (  88 expanded)
%              Depth                    :   18
%              Number of atoms          :  126 ( 401 expanded)
%              Number of equality atoms :   30 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_90,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_108,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [B_41,A_40] :
      ( r1_xboole_0(B_41,A_40)
      | k4_xboole_0(A_40,B_41) != A_40 ) ),
    inference(resolution,[status(thm)],[c_108,c_4])).

tff(c_42,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_59,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(B_34,A_35)
      | ~ r1_xboole_0(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_1951,plain,(
    ! [A_135,C_136,B_137] :
      ( ~ r1_xboole_0(A_135,C_136)
      | ~ r1_xboole_0(A_135,B_137)
      | r1_xboole_0(A_135,k2_xboole_0(B_137,C_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5468,plain,(
    ! [B_260,C_261,A_262] :
      ( r1_xboole_0(k2_xboole_0(B_260,C_261),A_262)
      | ~ r1_xboole_0(A_262,C_261)
      | ~ r1_xboole_0(A_262,B_260) ) ),
    inference(resolution,[status(thm)],[c_1951,c_4])).

tff(c_40,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5486,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_5468,c_40])).

tff(c_5494,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_5486])).

tff(c_5505,plain,(
    k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_114,c_5494])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_47,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_116,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = A_42
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_134,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_65,c_116])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1968,plain,(
    ! [A_135,B_137,C_136] :
      ( k4_xboole_0(A_135,k2_xboole_0(B_137,C_136)) = A_135
      | ~ r1_xboole_0(A_135,C_136)
      | ~ r1_xboole_0(A_135,B_137) ) ),
    inference(resolution,[status(thm)],[c_1951,c_28])).

tff(c_254,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,k1_tarski(B_58)) = A_57
      | r2_hidden(B_58,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_64,plain,(
    ! [B_21,A_20] : r1_xboole_0(B_21,k4_xboole_0(A_20,B_21)) ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_263,plain,(
    ! [B_58,A_57] :
      ( r1_xboole_0(k1_tarski(B_58),A_57)
      | r2_hidden(B_58,A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_64])).

tff(c_1289,plain,(
    ! [A_109,B_110,C_111] :
      ( r1_xboole_0(A_109,B_110)
      | ~ r1_xboole_0(A_109,k2_xboole_0(B_110,C_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_72429,plain,(
    ! [B_1151,B_1152,C_1153] :
      ( r1_xboole_0(k1_tarski(B_1151),B_1152)
      | r2_hidden(B_1151,k2_xboole_0(B_1152,C_1153)) ) ),
    inference(resolution,[status(thm)],[c_263,c_1289])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1550,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r1_xboole_0(A_116,B_117)
      | ~ r2_hidden(C_118,B_117)
      | ~ r2_hidden(C_118,A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14314,plain,(
    ! [C_489,A_490,B_491] :
      ( ~ r2_hidden(C_489,A_490)
      | ~ r2_hidden(C_489,B_491)
      | k4_xboole_0(A_490,B_491) != A_490 ) ),
    inference(resolution,[status(thm)],[c_114,c_1550])).

tff(c_14323,plain,(
    ! [B_491] :
      ( ~ r2_hidden('#skF_5',B_491)
      | k4_xboole_0('#skF_4',B_491) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_44,c_14314])).

tff(c_72510,plain,(
    ! [B_1154,C_1155] :
      ( k4_xboole_0('#skF_4',k2_xboole_0(B_1154,C_1155)) != '#skF_4'
      | r1_xboole_0(k1_tarski('#skF_5'),B_1154) ) ),
    inference(resolution,[status(thm)],[c_72429,c_14323])).

tff(c_72522,plain,(
    ! [B_137,C_136] :
      ( r1_xboole_0(k1_tarski('#skF_5'),B_137)
      | ~ r1_xboole_0('#skF_4',C_136)
      | ~ r1_xboole_0('#skF_4',B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1968,c_72510])).

tff(c_72730,plain,(
    ! [C_136] : ~ r1_xboole_0('#skF_4',C_136) ),
    inference(splitLeft,[status(thm)],[c_72522])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_306,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_xboole_0(A_66,C_67)
      | ~ r1_tarski(A_66,k4_xboole_0(B_68,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_658,plain,(
    ! [B_85,C_86,B_87] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_85,C_86),B_87),C_86) ),
    inference(resolution,[status(thm)],[c_16,c_306])).

tff(c_743,plain,(
    ! [B_89] : r1_xboole_0(k4_xboole_0('#skF_3',B_89),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_658])).

tff(c_828,plain,(
    ! [B_92] : r1_xboole_0('#skF_4',k4_xboole_0('#skF_3',B_92)) ),
    inference(resolution,[status(thm)],[c_743,c_4])).

tff(c_852,plain,(
    ! [B_92] : k4_xboole_0('#skF_4',k4_xboole_0('#skF_3',B_92)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_828,c_28])).

tff(c_133,plain,(
    ! [B_21,A_20] : k4_xboole_0(B_21,k4_xboole_0(A_20,B_21)) = B_21 ),
    inference(resolution,[status(thm)],[c_64,c_116])).

tff(c_2109,plain,(
    ! [B_144,C_145,B_146] : r1_xboole_0(k3_xboole_0(k4_xboole_0(B_144,C_145),B_146),C_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_658])).

tff(c_3210,plain,(
    ! [C_186,B_187,B_188] : r1_xboole_0(C_186,k3_xboole_0(k4_xboole_0(B_187,C_186),B_188)) ),
    inference(resolution,[status(thm)],[c_2109,c_4])).

tff(c_3729,plain,(
    ! [A_207,B_208,B_209] : r1_xboole_0(k4_xboole_0(A_207,B_208),k3_xboole_0(B_208,B_209)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_3210])).

tff(c_9177,plain,(
    ! [B_385,B_386] : r1_xboole_0('#skF_4',k3_xboole_0(k4_xboole_0('#skF_3',B_385),B_386)) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_3729])).

tff(c_9640,plain,(
    ! [B_395,B_396] : r1_xboole_0('#skF_4',k3_xboole_0(k3_xboole_0('#skF_3',B_395),B_396)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_9177])).

tff(c_9675,plain,(
    ! [A_1,B_396] : r1_xboole_0('#skF_4',k3_xboole_0(k3_xboole_0(A_1,'#skF_3'),B_396)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9640])).

tff(c_72752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72730,c_9675])).

tff(c_72754,plain,(
    ! [B_1165] :
      ( r1_xboole_0(k1_tarski('#skF_5'),B_1165)
      | ~ r1_xboole_0('#skF_4',B_1165) ) ),
    inference(splitRight,[status(thm)],[c_72522])).

tff(c_72775,plain,(
    ! [B_1166] :
      ( r1_xboole_0(B_1166,k1_tarski('#skF_5'))
      | ~ r1_xboole_0('#skF_4',B_1166) ) ),
    inference(resolution,[status(thm)],[c_72754,c_4])).

tff(c_72809,plain,(
    ! [B_1167] :
      ( k4_xboole_0(B_1167,k1_tarski('#skF_5')) = B_1167
      | ~ r1_xboole_0('#skF_4',B_1167) ) ),
    inference(resolution,[status(thm)],[c_72775,c_28])).

tff(c_767,plain,(
    ! [B_89] : k4_xboole_0(k4_xboole_0('#skF_3',B_89),'#skF_4') = k4_xboole_0('#skF_3',B_89) ),
    inference(resolution,[status(thm)],[c_743,c_28])).

tff(c_73130,plain,
    ( k4_xboole_0('#skF_3',k1_tarski('#skF_5')) = k4_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_72809,c_767])).

tff(c_73594,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_134,c_73130])).

tff(c_316,plain,(
    ! [A_66,A_20,B_21] :
      ( r1_xboole_0(A_66,k4_xboole_0(A_20,B_21))
      | ~ r1_tarski(A_66,B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_306])).

tff(c_75987,plain,(
    ! [A_1196] :
      ( r1_xboole_0(A_1196,'#skF_3')
      | ~ r1_tarski(A_1196,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73594,c_316])).

tff(c_76089,plain,(
    r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_75987])).

tff(c_76101,plain,(
    r1_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76089,c_4])).

tff(c_76110,plain,(
    k4_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_76101,c_28])).

tff(c_376,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_404,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_376])).

tff(c_76310,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_76110,c_404])).

tff(c_28932,plain,(
    ! [C_722,B_723,B_724] : k4_xboole_0(C_722,k3_xboole_0(k4_xboole_0(B_723,C_722),B_724)) = C_722 ),
    inference(resolution,[status(thm)],[c_3210,c_28])).

tff(c_29612,plain,(
    ! [C_722,B_2,B_723] : k4_xboole_0(C_722,k3_xboole_0(B_2,k4_xboole_0(B_723,C_722))) = C_722 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_28932])).

tff(c_76530,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_76310,c_29612])).

tff(c_76703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5505,c_76530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:04:47 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.49/11.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.49/11.86  
% 21.49/11.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.49/11.86  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 21.49/11.86  
% 21.49/11.86  %Foreground sorts:
% 21.49/11.86  
% 21.49/11.86  
% 21.49/11.86  %Background operators:
% 21.49/11.86  
% 21.49/11.86  
% 21.49/11.86  %Foreground operators:
% 21.49/11.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.49/11.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.49/11.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 21.49/11.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.49/11.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.49/11.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 21.49/11.86  tff('#skF_5', type, '#skF_5': $i).
% 21.49/11.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 21.49/11.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 21.49/11.86  tff('#skF_2', type, '#skF_2': $i).
% 21.49/11.86  tff('#skF_3', type, '#skF_3': $i).
% 21.49/11.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.49/11.86  tff('#skF_4', type, '#skF_4': $i).
% 21.49/11.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.49/11.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.49/11.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.49/11.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 21.49/11.86  
% 21.49/11.88  tff(f_81, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 21.49/11.88  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 21.49/11.88  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 21.49/11.88  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 21.49/11.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 21.49/11.88  tff(f_90, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 21.49/11.88  tff(f_77, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 21.49/11.88  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 21.49/11.88  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 21.49/11.88  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 21.49/11.88  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 21.49/11.88  tff(c_108, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k4_xboole_0(A_40, B_41)!=A_40)), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.49/11.88  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.49/11.88  tff(c_114, plain, (![B_41, A_40]: (r1_xboole_0(B_41, A_40) | k4_xboole_0(A_40, B_41)!=A_40)), inference(resolution, [status(thm)], [c_108, c_4])).
% 21.49/11.88  tff(c_42, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.49/11.88  tff(c_59, plain, (![B_34, A_35]: (r1_xboole_0(B_34, A_35) | ~r1_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.49/11.88  tff(c_65, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_59])).
% 21.49/11.88  tff(c_1951, plain, (![A_135, C_136, B_137]: (~r1_xboole_0(A_135, C_136) | ~r1_xboole_0(A_135, B_137) | r1_xboole_0(A_135, k2_xboole_0(B_137, C_136)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.49/11.88  tff(c_5468, plain, (![B_260, C_261, A_262]: (r1_xboole_0(k2_xboole_0(B_260, C_261), A_262) | ~r1_xboole_0(A_262, C_261) | ~r1_xboole_0(A_262, B_260))), inference(resolution, [status(thm)], [c_1951, c_4])).
% 21.49/11.88  tff(c_40, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.49/11.88  tff(c_5486, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_5468, c_40])).
% 21.49/11.88  tff(c_5494, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_5486])).
% 21.49/11.88  tff(c_5505, plain, (k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_114, c_5494])).
% 21.49/11.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.49/11.88  tff(c_46, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.49/11.88  tff(c_47, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 21.49/11.88  tff(c_116, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=A_42 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.49/11.88  tff(c_134, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_65, c_116])).
% 21.49/11.88  tff(c_28, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.49/11.88  tff(c_1968, plain, (![A_135, B_137, C_136]: (k4_xboole_0(A_135, k2_xboole_0(B_137, C_136))=A_135 | ~r1_xboole_0(A_135, C_136) | ~r1_xboole_0(A_135, B_137))), inference(resolution, [status(thm)], [c_1951, c_28])).
% 21.49/11.88  tff(c_254, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k1_tarski(B_58))=A_57 | r2_hidden(B_58, A_57))), inference(cnfTransformation, [status(thm)], [f_90])).
% 21.49/11.88  tff(c_26, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 21.49/11.88  tff(c_64, plain, (![B_21, A_20]: (r1_xboole_0(B_21, k4_xboole_0(A_20, B_21)))), inference(resolution, [status(thm)], [c_26, c_59])).
% 21.49/11.88  tff(c_263, plain, (![B_58, A_57]: (r1_xboole_0(k1_tarski(B_58), A_57) | r2_hidden(B_58, A_57))), inference(superposition, [status(thm), theory('equality')], [c_254, c_64])).
% 21.49/11.88  tff(c_1289, plain, (![A_109, B_110, C_111]: (r1_xboole_0(A_109, B_110) | ~r1_xboole_0(A_109, k2_xboole_0(B_110, C_111)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.49/11.88  tff(c_72429, plain, (![B_1151, B_1152, C_1153]: (r1_xboole_0(k1_tarski(B_1151), B_1152) | r2_hidden(B_1151, k2_xboole_0(B_1152, C_1153)))), inference(resolution, [status(thm)], [c_263, c_1289])).
% 21.49/11.88  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 21.49/11.88  tff(c_1550, plain, (![A_116, B_117, C_118]: (~r1_xboole_0(A_116, B_117) | ~r2_hidden(C_118, B_117) | ~r2_hidden(C_118, A_116))), inference(cnfTransformation, [status(thm)], [f_49])).
% 21.49/11.88  tff(c_14314, plain, (![C_489, A_490, B_491]: (~r2_hidden(C_489, A_490) | ~r2_hidden(C_489, B_491) | k4_xboole_0(A_490, B_491)!=A_490)), inference(resolution, [status(thm)], [c_114, c_1550])).
% 21.49/11.88  tff(c_14323, plain, (![B_491]: (~r2_hidden('#skF_5', B_491) | k4_xboole_0('#skF_4', B_491)!='#skF_4')), inference(resolution, [status(thm)], [c_44, c_14314])).
% 21.49/11.88  tff(c_72510, plain, (![B_1154, C_1155]: (k4_xboole_0('#skF_4', k2_xboole_0(B_1154, C_1155))!='#skF_4' | r1_xboole_0(k1_tarski('#skF_5'), B_1154))), inference(resolution, [status(thm)], [c_72429, c_14323])).
% 21.49/11.88  tff(c_72522, plain, (![B_137, C_136]: (r1_xboole_0(k1_tarski('#skF_5'), B_137) | ~r1_xboole_0('#skF_4', C_136) | ~r1_xboole_0('#skF_4', B_137))), inference(superposition, [status(thm), theory('equality')], [c_1968, c_72510])).
% 21.49/11.88  tff(c_72730, plain, (![C_136]: (~r1_xboole_0('#skF_4', C_136))), inference(splitLeft, [status(thm)], [c_72522])).
% 21.49/11.88  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.49/11.88  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 21.49/11.88  tff(c_306, plain, (![A_66, C_67, B_68]: (r1_xboole_0(A_66, C_67) | ~r1_tarski(A_66, k4_xboole_0(B_68, C_67)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.49/11.88  tff(c_658, plain, (![B_85, C_86, B_87]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_85, C_86), B_87), C_86))), inference(resolution, [status(thm)], [c_16, c_306])).
% 21.49/11.88  tff(c_743, plain, (![B_89]: (r1_xboole_0(k4_xboole_0('#skF_3', B_89), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_658])).
% 21.49/11.88  tff(c_828, plain, (![B_92]: (r1_xboole_0('#skF_4', k4_xboole_0('#skF_3', B_92)))), inference(resolution, [status(thm)], [c_743, c_4])).
% 21.49/11.88  tff(c_852, plain, (![B_92]: (k4_xboole_0('#skF_4', k4_xboole_0('#skF_3', B_92))='#skF_4')), inference(resolution, [status(thm)], [c_828, c_28])).
% 21.49/11.88  tff(c_133, plain, (![B_21, A_20]: (k4_xboole_0(B_21, k4_xboole_0(A_20, B_21))=B_21)), inference(resolution, [status(thm)], [c_64, c_116])).
% 21.49/11.88  tff(c_2109, plain, (![B_144, C_145, B_146]: (r1_xboole_0(k3_xboole_0(k4_xboole_0(B_144, C_145), B_146), C_145))), inference(superposition, [status(thm), theory('equality')], [c_18, c_658])).
% 21.49/11.88  tff(c_3210, plain, (![C_186, B_187, B_188]: (r1_xboole_0(C_186, k3_xboole_0(k4_xboole_0(B_187, C_186), B_188)))), inference(resolution, [status(thm)], [c_2109, c_4])).
% 21.49/11.88  tff(c_3729, plain, (![A_207, B_208, B_209]: (r1_xboole_0(k4_xboole_0(A_207, B_208), k3_xboole_0(B_208, B_209)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_3210])).
% 21.49/11.88  tff(c_9177, plain, (![B_385, B_386]: (r1_xboole_0('#skF_4', k3_xboole_0(k4_xboole_0('#skF_3', B_385), B_386)))), inference(superposition, [status(thm), theory('equality')], [c_852, c_3729])).
% 21.49/11.88  tff(c_9640, plain, (![B_395, B_396]: (r1_xboole_0('#skF_4', k3_xboole_0(k3_xboole_0('#skF_3', B_395), B_396)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_9177])).
% 21.49/11.88  tff(c_9675, plain, (![A_1, B_396]: (r1_xboole_0('#skF_4', k3_xboole_0(k3_xboole_0(A_1, '#skF_3'), B_396)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9640])).
% 21.49/11.88  tff(c_72752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72730, c_9675])).
% 21.49/11.88  tff(c_72754, plain, (![B_1165]: (r1_xboole_0(k1_tarski('#skF_5'), B_1165) | ~r1_xboole_0('#skF_4', B_1165))), inference(splitRight, [status(thm)], [c_72522])).
% 21.49/11.88  tff(c_72775, plain, (![B_1166]: (r1_xboole_0(B_1166, k1_tarski('#skF_5')) | ~r1_xboole_0('#skF_4', B_1166))), inference(resolution, [status(thm)], [c_72754, c_4])).
% 21.49/11.88  tff(c_72809, plain, (![B_1167]: (k4_xboole_0(B_1167, k1_tarski('#skF_5'))=B_1167 | ~r1_xboole_0('#skF_4', B_1167))), inference(resolution, [status(thm)], [c_72775, c_28])).
% 21.49/11.88  tff(c_767, plain, (![B_89]: (k4_xboole_0(k4_xboole_0('#skF_3', B_89), '#skF_4')=k4_xboole_0('#skF_3', B_89))), inference(resolution, [status(thm)], [c_743, c_28])).
% 21.49/11.88  tff(c_73130, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_5'))=k4_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_72809, c_767])).
% 21.49/11.88  tff(c_73594, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_134, c_73130])).
% 21.49/11.88  tff(c_316, plain, (![A_66, A_20, B_21]: (r1_xboole_0(A_66, k4_xboole_0(A_20, B_21)) | ~r1_tarski(A_66, B_21))), inference(superposition, [status(thm), theory('equality')], [c_133, c_306])).
% 21.49/11.88  tff(c_75987, plain, (![A_1196]: (r1_xboole_0(A_1196, '#skF_3') | ~r1_tarski(A_1196, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_73594, c_316])).
% 21.49/11.88  tff(c_76089, plain, (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_47, c_75987])).
% 21.49/11.88  tff(c_76101, plain, (r1_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_76089, c_4])).
% 21.49/11.88  tff(c_76110, plain, (k4_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_76101, c_28])).
% 21.49/11.88  tff(c_376, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.49/11.88  tff(c_404, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k3_xboole_0(A_15, k4_xboole_0(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_376])).
% 21.49/11.88  tff(c_76310, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_76110, c_404])).
% 21.49/11.88  tff(c_28932, plain, (![C_722, B_723, B_724]: (k4_xboole_0(C_722, k3_xboole_0(k4_xboole_0(B_723, C_722), B_724))=C_722)), inference(resolution, [status(thm)], [c_3210, c_28])).
% 21.49/11.88  tff(c_29612, plain, (![C_722, B_2, B_723]: (k4_xboole_0(C_722, k3_xboole_0(B_2, k4_xboole_0(B_723, C_722)))=C_722)), inference(superposition, [status(thm), theory('equality')], [c_2, c_28932])).
% 21.49/11.88  tff(c_76530, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_76310, c_29612])).
% 21.49/11.88  tff(c_76703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5505, c_76530])).
% 21.49/11.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.49/11.88  
% 21.49/11.88  Inference rules
% 21.49/11.88  ----------------------
% 21.49/11.88  #Ref     : 1
% 21.49/11.88  #Sup     : 19188
% 21.49/11.88  #Fact    : 0
% 21.49/11.88  #Define  : 0
% 21.49/11.88  #Split   : 7
% 21.49/11.88  #Chain   : 0
% 21.49/11.88  #Close   : 0
% 21.49/11.88  
% 21.49/11.88  Ordering : KBO
% 21.49/11.88  
% 21.49/11.88  Simplification rules
% 21.49/11.88  ----------------------
% 21.49/11.88  #Subsume      : 2285
% 21.49/11.88  #Demod        : 13480
% 21.49/11.88  #Tautology    : 10745
% 21.49/11.88  #SimpNegUnit  : 165
% 21.49/11.88  #BackRed      : 96
% 21.49/11.88  
% 21.49/11.88  #Partial instantiations: 0
% 21.49/11.88  #Strategies tried      : 1
% 21.49/11.88  
% 21.49/11.88  Timing (in seconds)
% 21.49/11.88  ----------------------
% 21.49/11.88  Preprocessing        : 0.31
% 21.49/11.88  Parsing              : 0.16
% 21.49/11.88  CNF conversion       : 0.02
% 21.49/11.88  Main loop            : 10.81
% 21.49/11.88  Inferencing          : 1.45
% 21.49/11.88  Reduction            : 6.04
% 21.49/11.88  Demodulation         : 5.25
% 21.49/11.88  BG Simplification    : 0.14
% 21.49/11.88  Subsumption          : 2.57
% 21.49/11.88  Abstraction          : 0.20
% 21.49/11.88  MUC search           : 0.00
% 21.49/11.88  Cooper               : 0.00
% 21.49/11.88  Total                : 11.16
% 21.49/11.88  Index Insertion      : 0.00
% 21.49/11.88  Index Deletion       : 0.00
% 21.49/11.88  Index Matching       : 0.00
% 21.49/11.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
