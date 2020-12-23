%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:11 EST 2020

% Result     : Theorem 4.24s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 134 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 164 expanded)
%              Number of equality atoms :   53 (  78 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_79,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_77,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_3421,plain,(
    ! [A_175,B_176] :
      ( r1_xboole_0(A_175,B_176)
      | k3_xboole_0(A_175,B_176) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_118,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_26,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ! [A_31] : r1_xboole_0(A_31,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_225,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = k1_xboole_0
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_233,plain,(
    ! [A_31] : k3_xboole_0(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_225])).

tff(c_30,plain,(
    ! [A_28] : k4_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_446,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_473,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k3_xboole_0(A_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_446])).

tff(c_476,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_473])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_531,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_561,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_531])).

tff(c_565,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_561])).

tff(c_46,plain,(
    r1_tarski('#skF_3',k4_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_207,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,B_53) = A_52
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_219,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_207])).

tff(c_552,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_531])).

tff(c_777,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_552])).

tff(c_954,plain,(
    ! [A_97,B_98] : k2_xboole_0(A_97,k4_xboole_0(B_98,A_97)) = k2_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_979,plain,(
    k2_xboole_0(k4_xboole_0('#skF_4','#skF_5'),k1_xboole_0) = k2_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_777,c_954])).

tff(c_1000,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22,c_979])).

tff(c_20,plain,(
    ! [A_18,C_20,B_19] :
      ( r1_tarski(A_18,C_20)
      | ~ r1_tarski(k2_xboole_0(A_18,B_19),C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3238,plain,(
    ! [C_168] :
      ( r1_tarski('#skF_3',C_168)
      | ~ r1_tarski(k4_xboole_0('#skF_4','#skF_5'),C_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1000,c_20])).

tff(c_3270,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_3238])).

tff(c_3285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_3270])).

tff(c_3286,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_3425,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3421,c_3286])).

tff(c_42,plain,(
    ! [A_35,B_36] : r1_xboole_0(k4_xboole_0(A_35,B_36),B_36) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3426,plain,(
    ! [A_177,B_178] :
      ( k3_xboole_0(A_177,B_178) = k1_xboole_0
      | ~ r1_xboole_0(A_177,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3437,plain,(
    ! [A_35,B_36] : k3_xboole_0(k4_xboole_0(A_35,B_36),B_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_3426])).

tff(c_3650,plain,(
    ! [A_191,B_192,C_193] :
      ( ~ r1_xboole_0(A_191,B_192)
      | ~ r2_hidden(C_193,k3_xboole_0(A_191,B_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3653,plain,(
    ! [A_35,B_36,C_193] :
      ( ~ r1_xboole_0(k4_xboole_0(A_35,B_36),B_36)
      | ~ r2_hidden(C_193,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3437,c_3650])).

tff(c_3683,plain,(
    ! [C_193] : ~ r2_hidden(C_193,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3653])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3540,plain,(
    ! [A_184,B_185] : k3_xboole_0(k4_xboole_0(A_184,B_185),B_185) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_3426])).

tff(c_3564,plain,(
    ! [A_3,A_184] : k3_xboole_0(A_3,k4_xboole_0(A_184,A_3)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3540])).

tff(c_4586,plain,(
    ! [A_232,B_233] :
      ( r2_hidden('#skF_1'(A_232,B_233),k3_xboole_0(A_232,B_233))
      | r1_xboole_0(A_232,B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4601,plain,(
    ! [A_3,A_184] :
      ( r2_hidden('#skF_1'(A_3,k4_xboole_0(A_184,A_3)),k1_xboole_0)
      | r1_xboole_0(A_3,k4_xboole_0(A_184,A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3564,c_4586])).

tff(c_4631,plain,(
    ! [A_3,A_184] : r1_xboole_0(A_3,k4_xboole_0(A_184,A_3)) ),
    inference(negUnitSimplification,[status(thm)],[c_3683,c_4601])).

tff(c_3438,plain,(
    ! [A_31] : k3_xboole_0(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_3426])).

tff(c_3573,plain,(
    ! [A_186,B_187] : k4_xboole_0(A_186,k4_xboole_0(A_186,B_187)) = k3_xboole_0(A_186,B_187) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3597,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k3_xboole_0(A_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3573])).

tff(c_3600,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3438,c_3597])).

tff(c_4012,plain,(
    ! [A_215,B_216] : k5_xboole_0(A_215,k3_xboole_0(A_215,B_216)) = k4_xboole_0(A_215,B_216) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4048,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_4012])).

tff(c_4052,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3600,c_4048])).

tff(c_3376,plain,(
    ! [A_173,B_174] :
      ( k3_xboole_0(A_173,B_174) = A_173
      | ~ r1_tarski(A_173,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3392,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_3376])).

tff(c_4039,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3392,c_4012])).

tff(c_4108,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4052,c_4039])).

tff(c_28,plain,(
    ! [A_26,B_27] : k2_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4115,plain,(
    k2_xboole_0(k4_xboole_0('#skF_4','#skF_5'),k1_xboole_0) = k2_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4108,c_28])).

tff(c_4131,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22,c_4115])).

tff(c_40,plain,(
    ! [A_32,B_33,C_34] :
      ( r1_xboole_0(A_32,B_33)
      | ~ r1_xboole_0(A_32,k2_xboole_0(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5008,plain,(
    ! [A_248] :
      ( r1_xboole_0(A_248,'#skF_3')
      | ~ r1_xboole_0(A_248,k4_xboole_0('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4131,c_40])).

tff(c_5035,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_4631,c_5008])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5043,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5035,c_6])).

tff(c_5065,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5043,c_4])).

tff(c_5086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3425,c_5065])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:59:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.24/1.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.93  
% 4.24/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.94  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 4.24/1.94  
% 4.24/1.94  %Foreground sorts:
% 4.24/1.94  
% 4.24/1.94  
% 4.24/1.94  %Background operators:
% 4.24/1.94  
% 4.24/1.94  
% 4.24/1.94  %Foreground operators:
% 4.24/1.94  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.24/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.24/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.24/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.24/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.24/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.24/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.24/1.94  tff('#skF_5', type, '#skF_5': $i).
% 4.24/1.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.24/1.94  tff('#skF_3', type, '#skF_3': $i).
% 4.24/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.24/1.94  tff('#skF_4', type, '#skF_4': $i).
% 4.24/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.24/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.24/1.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.24/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.24/1.94  
% 4.24/1.95  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.24/1.95  tff(f_104, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.24/1.95  tff(f_71, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.24/1.95  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.24/1.95  tff(f_65, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.24/1.95  tff(f_79, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.24/1.95  tff(f_75, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.24/1.95  tff(f_77, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.24/1.95  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.24/1.95  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.24/1.95  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.24/1.95  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.24/1.95  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.24/1.95  tff(f_97, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.24/1.95  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.24/1.95  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.24/1.95  tff(f_95, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.24/1.95  tff(c_3421, plain, (![A_175, B_176]: (r1_xboole_0(A_175, B_176) | k3_xboole_0(A_175, B_176)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.24/1.95  tff(c_44, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.24/1.95  tff(c_118, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 4.24/1.95  tff(c_26, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.24/1.95  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.24/1.95  tff(c_22, plain, (![A_21]: (k2_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.24/1.95  tff(c_34, plain, (![A_31]: (r1_xboole_0(A_31, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.24/1.95  tff(c_225, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=k1_xboole_0 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.24/1.95  tff(c_233, plain, (![A_31]: (k3_xboole_0(A_31, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_225])).
% 4.24/1.95  tff(c_30, plain, (![A_28]: (k4_xboole_0(A_28, k1_xboole_0)=A_28)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.24/1.95  tff(c_446, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.24/1.95  tff(c_473, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k3_xboole_0(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_446])).
% 4.24/1.95  tff(c_476, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_233, c_473])).
% 4.24/1.95  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.24/1.95  tff(c_531, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.24/1.95  tff(c_561, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_531])).
% 4.24/1.95  tff(c_565, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_476, c_561])).
% 4.24/1.95  tff(c_46, plain, (r1_tarski('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.24/1.95  tff(c_207, plain, (![A_52, B_53]: (k3_xboole_0(A_52, B_53)=A_52 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.24/1.95  tff(c_219, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_207])).
% 4.24/1.95  tff(c_552, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_219, c_531])).
% 4.24/1.95  tff(c_777, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_565, c_552])).
% 4.24/1.95  tff(c_954, plain, (![A_97, B_98]: (k2_xboole_0(A_97, k4_xboole_0(B_98, A_97))=k2_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.24/1.95  tff(c_979, plain, (k2_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), k1_xboole_0)=k2_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_777, c_954])).
% 4.60/1.95  tff(c_1000, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22, c_979])).
% 4.60/1.95  tff(c_20, plain, (![A_18, C_20, B_19]: (r1_tarski(A_18, C_20) | ~r1_tarski(k2_xboole_0(A_18, B_19), C_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.60/1.95  tff(c_3238, plain, (![C_168]: (r1_tarski('#skF_3', C_168) | ~r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), C_168))), inference(superposition, [status(thm), theory('equality')], [c_1000, c_20])).
% 4.60/1.95  tff(c_3270, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_3238])).
% 4.60/1.95  tff(c_3285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_3270])).
% 4.60/1.95  tff(c_3286, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 4.60/1.95  tff(c_3425, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3421, c_3286])).
% 4.60/1.95  tff(c_42, plain, (![A_35, B_36]: (r1_xboole_0(k4_xboole_0(A_35, B_36), B_36))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.60/1.95  tff(c_3426, plain, (![A_177, B_178]: (k3_xboole_0(A_177, B_178)=k1_xboole_0 | ~r1_xboole_0(A_177, B_178))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.60/1.95  tff(c_3437, plain, (![A_35, B_36]: (k3_xboole_0(k4_xboole_0(A_35, B_36), B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_3426])).
% 4.60/1.95  tff(c_3650, plain, (![A_191, B_192, C_193]: (~r1_xboole_0(A_191, B_192) | ~r2_hidden(C_193, k3_xboole_0(A_191, B_192)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.60/1.95  tff(c_3653, plain, (![A_35, B_36, C_193]: (~r1_xboole_0(k4_xboole_0(A_35, B_36), B_36) | ~r2_hidden(C_193, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3437, c_3650])).
% 4.60/1.95  tff(c_3683, plain, (![C_193]: (~r2_hidden(C_193, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3653])).
% 4.60/1.95  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.60/1.95  tff(c_3540, plain, (![A_184, B_185]: (k3_xboole_0(k4_xboole_0(A_184, B_185), B_185)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_3426])).
% 4.60/1.95  tff(c_3564, plain, (![A_3, A_184]: (k3_xboole_0(A_3, k4_xboole_0(A_184, A_3))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_3540])).
% 4.60/1.95  tff(c_4586, plain, (![A_232, B_233]: (r2_hidden('#skF_1'(A_232, B_233), k3_xboole_0(A_232, B_233)) | r1_xboole_0(A_232, B_233))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.60/1.95  tff(c_4601, plain, (![A_3, A_184]: (r2_hidden('#skF_1'(A_3, k4_xboole_0(A_184, A_3)), k1_xboole_0) | r1_xboole_0(A_3, k4_xboole_0(A_184, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_3564, c_4586])).
% 4.60/1.95  tff(c_4631, plain, (![A_3, A_184]: (r1_xboole_0(A_3, k4_xboole_0(A_184, A_3)))), inference(negUnitSimplification, [status(thm)], [c_3683, c_4601])).
% 4.60/1.95  tff(c_3438, plain, (![A_31]: (k3_xboole_0(A_31, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_3426])).
% 4.60/1.95  tff(c_3573, plain, (![A_186, B_187]: (k4_xboole_0(A_186, k4_xboole_0(A_186, B_187))=k3_xboole_0(A_186, B_187))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.60/1.95  tff(c_3597, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k3_xboole_0(A_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_3573])).
% 4.60/1.95  tff(c_3600, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3438, c_3597])).
% 4.60/1.95  tff(c_4012, plain, (![A_215, B_216]: (k5_xboole_0(A_215, k3_xboole_0(A_215, B_216))=k4_xboole_0(A_215, B_216))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.60/1.95  tff(c_4048, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_4012])).
% 4.60/1.95  tff(c_4052, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3600, c_4048])).
% 4.60/1.95  tff(c_3376, plain, (![A_173, B_174]: (k3_xboole_0(A_173, B_174)=A_173 | ~r1_tarski(A_173, B_174))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.60/1.95  tff(c_3392, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_3376])).
% 4.60/1.95  tff(c_4039, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k5_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3392, c_4012])).
% 4.60/1.95  tff(c_4108, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4052, c_4039])).
% 4.60/1.95  tff(c_28, plain, (![A_26, B_27]: (k2_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.60/1.95  tff(c_4115, plain, (k2_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), k1_xboole_0)=k2_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4108, c_28])).
% 4.60/1.95  tff(c_4131, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22, c_4115])).
% 4.60/1.95  tff(c_40, plain, (![A_32, B_33, C_34]: (r1_xboole_0(A_32, B_33) | ~r1_xboole_0(A_32, k2_xboole_0(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.60/1.95  tff(c_5008, plain, (![A_248]: (r1_xboole_0(A_248, '#skF_3') | ~r1_xboole_0(A_248, k4_xboole_0('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_4131, c_40])).
% 4.60/1.95  tff(c_5035, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_4631, c_5008])).
% 4.60/1.95  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.60/1.95  tff(c_5043, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_5035, c_6])).
% 4.60/1.95  tff(c_5065, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5043, c_4])).
% 4.60/1.95  tff(c_5086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3425, c_5065])).
% 4.60/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.95  
% 4.60/1.95  Inference rules
% 4.60/1.95  ----------------------
% 4.60/1.95  #Ref     : 0
% 4.60/1.95  #Sup     : 1253
% 4.60/1.95  #Fact    : 0
% 4.60/1.95  #Define  : 0
% 4.60/1.95  #Split   : 6
% 4.60/1.95  #Chain   : 0
% 4.60/1.95  #Close   : 0
% 4.60/1.95  
% 4.60/1.95  Ordering : KBO
% 4.60/1.95  
% 4.60/1.95  Simplification rules
% 4.60/1.95  ----------------------
% 4.60/1.95  #Subsume      : 54
% 4.60/1.95  #Demod        : 799
% 4.60/1.95  #Tautology    : 878
% 4.60/1.95  #SimpNegUnit  : 21
% 4.60/1.95  #BackRed      : 0
% 4.60/1.95  
% 4.60/1.95  #Partial instantiations: 0
% 4.60/1.95  #Strategies tried      : 1
% 4.60/1.95  
% 4.60/1.95  Timing (in seconds)
% 4.60/1.95  ----------------------
% 4.60/1.95  Preprocessing        : 0.30
% 4.60/1.95  Parsing              : 0.17
% 4.60/1.95  CNF conversion       : 0.02
% 4.60/1.95  Main loop            : 0.79
% 4.60/1.96  Inferencing          : 0.26
% 4.60/1.96  Reduction            : 0.33
% 4.60/1.96  Demodulation         : 0.26
% 4.60/1.96  BG Simplification    : 0.03
% 4.60/1.96  Subsumption          : 0.12
% 4.60/1.96  Abstraction          : 0.03
% 4.60/1.96  MUC search           : 0.00
% 4.60/1.96  Cooper               : 0.00
% 4.60/1.96  Total                : 1.13
% 4.60/1.96  Index Insertion      : 0.00
% 4.60/1.96  Index Deletion       : 0.00
% 4.60/1.96  Index Matching       : 0.00
% 4.60/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
