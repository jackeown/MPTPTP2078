%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:12 EST 2020

% Result     : Theorem 18.30s
% Output     : CNFRefutation 18.37s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 231 expanded)
%              Number of leaves         :   28 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  152 ( 398 expanded)
%              Number of equality atoms :   31 ( 119 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k9_relat_1(B,A),k9_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( k5_relat_1(k6_relat_1(A_25),B_26) = k7_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_107,plain,(
    ! [A_44] :
      ( k9_relat_1(A_44,k1_relat_1(A_44)) = k2_relat_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    ! [A_20] :
      ( k9_relat_1(k6_relat_1(A_20),A_20) = k2_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_107])).

tff(c_120,plain,(
    ! [A_20] : k9_relat_1(k6_relat_1(A_20),A_20) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_24,c_116])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k5_relat_1(B_22,k6_relat_1(A_21)),B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_784,plain,(
    ! [B_100,C_101,A_102] :
      ( k9_relat_1(k5_relat_1(B_100,C_101),A_102) = k9_relat_1(C_101,k9_relat_1(B_100,A_102))
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [B_13,A_12,C_15] :
      ( r1_tarski(k9_relat_1(B_13,A_12),k9_relat_1(C_15,A_12))
      | ~ r1_tarski(B_13,C_15)
      | ~ v1_relat_1(C_15)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5401,plain,(
    ! [C_257,B_258,A_259,C_260] :
      ( r1_tarski(k9_relat_1(C_257,k9_relat_1(B_258,A_259)),k9_relat_1(C_260,A_259))
      | ~ r1_tarski(k5_relat_1(B_258,C_257),C_260)
      | ~ v1_relat_1(C_260)
      | ~ v1_relat_1(k5_relat_1(B_258,C_257))
      | ~ v1_relat_1(C_257)
      | ~ v1_relat_1(B_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_18])).

tff(c_5499,plain,(
    ! [C_257,A_20,C_260] :
      ( r1_tarski(k9_relat_1(C_257,A_20),k9_relat_1(C_260,A_20))
      | ~ r1_tarski(k5_relat_1(k6_relat_1(A_20),C_257),C_260)
      | ~ v1_relat_1(C_260)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_20),C_257))
      | ~ v1_relat_1(C_257)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_5401])).

tff(c_40721,plain,(
    ! [C_830,A_831,C_832] :
      ( r1_tarski(k9_relat_1(C_830,A_831),k9_relat_1(C_832,A_831))
      | ~ r1_tarski(k5_relat_1(k6_relat_1(A_831),C_830),C_832)
      | ~ v1_relat_1(C_832)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_831),C_830))
      | ~ v1_relat_1(C_830) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_5499])).

tff(c_40845,plain,(
    ! [A_21,A_831] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_21),A_831),k9_relat_1(k6_relat_1(A_831),A_831))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_831),k6_relat_1(A_21)))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_831)) ) ),
    inference(resolution,[status(thm)],[c_28,c_40721])).

tff(c_40962,plain,(
    ! [A_833,A_834] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_833),A_834),A_834)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_834),k6_relat_1(A_833))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_120,c_40845])).

tff(c_40976,plain,(
    ! [A_833,A_25] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_833),A_25),A_25)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_833),A_25))
      | ~ v1_relat_1(k6_relat_1(A_833)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_40962])).

tff(c_41523,plain,(
    ! [A_839,A_840] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_839),A_840),A_840)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_839),A_840)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40976])).

tff(c_65,plain,(
    ! [A_38] :
      ( k7_relat_1(A_38,k1_relat_1(A_38)) = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_77,plain,(
    ! [A_20] :
      ( k7_relat_1(k6_relat_1(A_20),A_20) = k6_relat_1(A_20)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_65])).

tff(c_81,plain,(
    ! [A_20] : k7_relat_1(k6_relat_1(A_20),A_20) = k6_relat_1(A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,A_23)),A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_169,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(B_54,C_53)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_185,plain,(
    ! [A_55] :
      ( r1_tarski(A_55,'#skF_3')
      | ~ r1_tarski(A_55,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_169])).

tff(c_204,plain,(
    ! [B_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_24,'#skF_2')),'#skF_3')
      | ~ v1_relat_1(B_24) ) ),
    inference(resolution,[status(thm)],[c_30,c_185])).

tff(c_276,plain,(
    ! [B_63,A_64] :
      ( k7_relat_1(B_63,A_64) = B_63
      | ~ r1_tarski(k1_relat_1(B_63),A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1191,plain,(
    ! [B_129] :
      ( k7_relat_1(k7_relat_1(B_129,'#skF_2'),'#skF_3') = k7_relat_1(B_129,'#skF_2')
      | ~ v1_relat_1(k7_relat_1(B_129,'#skF_2'))
      | ~ v1_relat_1(B_129) ) ),
    inference(resolution,[status(thm)],[c_204,c_276])).

tff(c_1199,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1('#skF_2'),'#skF_2'),'#skF_3') = k7_relat_1(k6_relat_1('#skF_2'),'#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_1191])).

tff(c_1207,plain,(
    k7_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k6_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_81,c_81,c_1199])).

tff(c_151,plain,(
    ! [A_50,B_51] :
      ( k5_relat_1(k6_relat_1(A_50),B_51) = k7_relat_1(B_51,A_50)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_158,plain,(
    ! [A_21,A_50] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_21),A_50),k6_relat_1(A_50))
      | ~ v1_relat_1(k6_relat_1(A_50))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_28])).

tff(c_167,plain,(
    ! [A_21,A_50] : r1_tarski(k7_relat_1(k6_relat_1(A_21),A_50),k6_relat_1(A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_158])).

tff(c_1248,plain,(
    r1_tarski(k6_relat_1('#skF_2'),k6_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1207,c_167])).

tff(c_507,plain,(
    ! [B_78,A_79,C_80] :
      ( r1_tarski(k9_relat_1(B_78,A_79),k9_relat_1(C_80,A_79))
      | ~ r1_tarski(B_78,C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_522,plain,(
    ! [A_20,C_80] :
      ( r1_tarski(A_20,k9_relat_1(C_80,A_20))
      | ~ r1_tarski(k6_relat_1(A_20),C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_507])).

tff(c_540,plain,(
    ! [A_20,C_80] :
      ( r1_tarski(A_20,k9_relat_1(C_80,A_20))
      | ~ r1_tarski(k6_relat_1(A_20),C_80)
      | ~ v1_relat_1(C_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_522])).

tff(c_1327,plain,
    ( r1_tarski('#skF_2',k9_relat_1(k6_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1248,c_540])).

tff(c_1337,plain,(
    r1_tarski('#skF_2',k9_relat_1(k6_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1327])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1353,plain,
    ( k9_relat_1(k6_relat_1('#skF_3'),'#skF_2') = '#skF_2'
    | ~ r1_tarski(k9_relat_1(k6_relat_1('#skF_3'),'#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1337,c_2])).

tff(c_4997,plain,(
    ~ r1_tarski(k9_relat_1(k6_relat_1('#skF_3'),'#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1353])).

tff(c_41856,plain,(
    ~ v1_relat_1(k7_relat_1(k6_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_41523,c_4997])).

tff(c_41907,plain,(
    ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_41856])).

tff(c_41915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_41907])).

tff(c_41916,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1353])).

tff(c_803,plain,(
    ! [B_26,A_25,A_102] :
      ( k9_relat_1(B_26,k9_relat_1(k6_relat_1(A_25),A_102)) = k9_relat_1(k7_relat_1(B_26,A_25),A_102)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_784])).

tff(c_811,plain,(
    ! [B_26,A_25,A_102] :
      ( k9_relat_1(B_26,k9_relat_1(k6_relat_1(A_25),A_102)) = k9_relat_1(k7_relat_1(B_26,A_25),A_102)
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_803])).

tff(c_42016,plain,(
    ! [B_841] :
      ( k9_relat_1(k7_relat_1(B_841,'#skF_3'),'#skF_2') = k9_relat_1(B_841,'#skF_2')
      | ~ v1_relat_1(B_841) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41916,c_811])).

tff(c_38,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42051,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_42016,c_38])).

tff(c_42077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42051])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.30/9.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.30/9.62  
% 18.30/9.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.30/9.62  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 18.30/9.62  
% 18.30/9.62  %Foreground sorts:
% 18.30/9.62  
% 18.30/9.62  
% 18.30/9.62  %Background operators:
% 18.30/9.62  
% 18.30/9.62  
% 18.30/9.62  %Foreground operators:
% 18.30/9.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.30/9.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 18.30/9.62  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.30/9.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.30/9.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.30/9.62  tff('#skF_2', type, '#skF_2': $i).
% 18.30/9.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 18.30/9.62  tff('#skF_3', type, '#skF_3': $i).
% 18.30/9.62  tff('#skF_1', type, '#skF_1': $i).
% 18.30/9.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.30/9.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.30/9.62  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.30/9.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.30/9.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.30/9.62  
% 18.37/9.66  tff(f_103, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 18.37/9.66  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 18.37/9.66  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 18.37/9.66  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 18.37/9.66  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 18.37/9.66  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 18.37/9.66  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 18.37/9.66  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 18.37/9.66  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k9_relat_1(B, A), k9_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 18.37/9.66  tff(f_95, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 18.37/9.66  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 18.37/9.66  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 18.37/9.66  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 18.37/9.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.37/9.66  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.37/9.66  tff(c_10, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.37/9.66  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.37/9.66  tff(c_32, plain, (![A_25, B_26]: (k5_relat_1(k6_relat_1(A_25), B_26)=k7_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_85])).
% 18.37/9.66  tff(c_24, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_71])).
% 18.37/9.66  tff(c_22, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_71])).
% 18.37/9.66  tff(c_107, plain, (![A_44]: (k9_relat_1(A_44, k1_relat_1(A_44))=k2_relat_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.37/9.66  tff(c_116, plain, (![A_20]: (k9_relat_1(k6_relat_1(A_20), A_20)=k2_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_107])).
% 18.37/9.66  tff(c_120, plain, (![A_20]: (k9_relat_1(k6_relat_1(A_20), A_20)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_24, c_116])).
% 18.37/9.66  tff(c_28, plain, (![B_22, A_21]: (r1_tarski(k5_relat_1(B_22, k6_relat_1(A_21)), B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.37/9.66  tff(c_784, plain, (![B_100, C_101, A_102]: (k9_relat_1(k5_relat_1(B_100, C_101), A_102)=k9_relat_1(C_101, k9_relat_1(B_100, A_102)) | ~v1_relat_1(C_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.37/9.66  tff(c_18, plain, (![B_13, A_12, C_15]: (r1_tarski(k9_relat_1(B_13, A_12), k9_relat_1(C_15, A_12)) | ~r1_tarski(B_13, C_15) | ~v1_relat_1(C_15) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.37/9.66  tff(c_5401, plain, (![C_257, B_258, A_259, C_260]: (r1_tarski(k9_relat_1(C_257, k9_relat_1(B_258, A_259)), k9_relat_1(C_260, A_259)) | ~r1_tarski(k5_relat_1(B_258, C_257), C_260) | ~v1_relat_1(C_260) | ~v1_relat_1(k5_relat_1(B_258, C_257)) | ~v1_relat_1(C_257) | ~v1_relat_1(B_258))), inference(superposition, [status(thm), theory('equality')], [c_784, c_18])).
% 18.37/9.66  tff(c_5499, plain, (![C_257, A_20, C_260]: (r1_tarski(k9_relat_1(C_257, A_20), k9_relat_1(C_260, A_20)) | ~r1_tarski(k5_relat_1(k6_relat_1(A_20), C_257), C_260) | ~v1_relat_1(C_260) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_20), C_257)) | ~v1_relat_1(C_257) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_5401])).
% 18.37/9.66  tff(c_40721, plain, (![C_830, A_831, C_832]: (r1_tarski(k9_relat_1(C_830, A_831), k9_relat_1(C_832, A_831)) | ~r1_tarski(k5_relat_1(k6_relat_1(A_831), C_830), C_832) | ~v1_relat_1(C_832) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_831), C_830)) | ~v1_relat_1(C_830))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_5499])).
% 18.37/9.66  tff(c_40845, plain, (![A_21, A_831]: (r1_tarski(k9_relat_1(k6_relat_1(A_21), A_831), k9_relat_1(k6_relat_1(A_831), A_831)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_831), k6_relat_1(A_21))) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_831)))), inference(resolution, [status(thm)], [c_28, c_40721])).
% 18.37/9.66  tff(c_40962, plain, (![A_833, A_834]: (r1_tarski(k9_relat_1(k6_relat_1(A_833), A_834), A_834) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_834), k6_relat_1(A_833))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_120, c_40845])).
% 18.37/9.66  tff(c_40976, plain, (![A_833, A_25]: (r1_tarski(k9_relat_1(k6_relat_1(A_833), A_25), A_25) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_833), A_25)) | ~v1_relat_1(k6_relat_1(A_833)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_40962])).
% 18.37/9.66  tff(c_41523, plain, (![A_839, A_840]: (r1_tarski(k9_relat_1(k6_relat_1(A_839), A_840), A_840) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_839), A_840)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_40976])).
% 18.37/9.66  tff(c_65, plain, (![A_38]: (k7_relat_1(A_38, k1_relat_1(A_38))=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.37/9.66  tff(c_77, plain, (![A_20]: (k7_relat_1(k6_relat_1(A_20), A_20)=k6_relat_1(A_20) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_65])).
% 18.37/9.66  tff(c_81, plain, (![A_20]: (k7_relat_1(k6_relat_1(A_20), A_20)=k6_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_77])).
% 18.37/9.66  tff(c_30, plain, (![B_24, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, A_23)), A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.37/9.66  tff(c_40, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.37/9.66  tff(c_169, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(B_54, C_53) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.37/9.66  tff(c_185, plain, (![A_55]: (r1_tarski(A_55, '#skF_3') | ~r1_tarski(A_55, '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_169])).
% 18.37/9.66  tff(c_204, plain, (![B_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_24, '#skF_2')), '#skF_3') | ~v1_relat_1(B_24))), inference(resolution, [status(thm)], [c_30, c_185])).
% 18.37/9.66  tff(c_276, plain, (![B_63, A_64]: (k7_relat_1(B_63, A_64)=B_63 | ~r1_tarski(k1_relat_1(B_63), A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.37/9.66  tff(c_1191, plain, (![B_129]: (k7_relat_1(k7_relat_1(B_129, '#skF_2'), '#skF_3')=k7_relat_1(B_129, '#skF_2') | ~v1_relat_1(k7_relat_1(B_129, '#skF_2')) | ~v1_relat_1(B_129))), inference(resolution, [status(thm)], [c_204, c_276])).
% 18.37/9.66  tff(c_1199, plain, (k7_relat_1(k7_relat_1(k6_relat_1('#skF_2'), '#skF_2'), '#skF_3')=k7_relat_1(k6_relat_1('#skF_2'), '#skF_2') | ~v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_1191])).
% 18.37/9.66  tff(c_1207, plain, (k7_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k6_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_81, c_81, c_1199])).
% 18.37/9.66  tff(c_151, plain, (![A_50, B_51]: (k5_relat_1(k6_relat_1(A_50), B_51)=k7_relat_1(B_51, A_50) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_85])).
% 18.37/9.66  tff(c_158, plain, (![A_21, A_50]: (r1_tarski(k7_relat_1(k6_relat_1(A_21), A_50), k6_relat_1(A_50)) | ~v1_relat_1(k6_relat_1(A_50)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_28])).
% 18.37/9.66  tff(c_167, plain, (![A_21, A_50]: (r1_tarski(k7_relat_1(k6_relat_1(A_21), A_50), k6_relat_1(A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_158])).
% 18.37/9.66  tff(c_1248, plain, (r1_tarski(k6_relat_1('#skF_2'), k6_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1207, c_167])).
% 18.37/9.66  tff(c_507, plain, (![B_78, A_79, C_80]: (r1_tarski(k9_relat_1(B_78, A_79), k9_relat_1(C_80, A_79)) | ~r1_tarski(B_78, C_80) | ~v1_relat_1(C_80) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.37/9.66  tff(c_522, plain, (![A_20, C_80]: (r1_tarski(A_20, k9_relat_1(C_80, A_20)) | ~r1_tarski(k6_relat_1(A_20), C_80) | ~v1_relat_1(C_80) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_507])).
% 18.37/9.66  tff(c_540, plain, (![A_20, C_80]: (r1_tarski(A_20, k9_relat_1(C_80, A_20)) | ~r1_tarski(k6_relat_1(A_20), C_80) | ~v1_relat_1(C_80))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_522])).
% 18.37/9.66  tff(c_1327, plain, (r1_tarski('#skF_2', k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1248, c_540])).
% 18.37/9.66  tff(c_1337, plain, (r1_tarski('#skF_2', k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1327])).
% 18.37/9.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.37/9.66  tff(c_1353, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')='#skF_2' | ~r1_tarski(k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_1337, c_2])).
% 18.37/9.66  tff(c_4997, plain, (~r1_tarski(k9_relat_1(k6_relat_1('#skF_3'), '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1353])).
% 18.37/9.66  tff(c_41856, plain, (~v1_relat_1(k7_relat_1(k6_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_41523, c_4997])).
% 18.37/9.66  tff(c_41907, plain, (~v1_relat_1(k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_41856])).
% 18.37/9.66  tff(c_41915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_41907])).
% 18.37/9.66  tff(c_41916, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_1353])).
% 18.37/9.66  tff(c_803, plain, (![B_26, A_25, A_102]: (k9_relat_1(B_26, k9_relat_1(k6_relat_1(A_25), A_102))=k9_relat_1(k7_relat_1(B_26, A_25), A_102) | ~v1_relat_1(B_26) | ~v1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_32, c_784])).
% 18.37/9.66  tff(c_811, plain, (![B_26, A_25, A_102]: (k9_relat_1(B_26, k9_relat_1(k6_relat_1(A_25), A_102))=k9_relat_1(k7_relat_1(B_26, A_25), A_102) | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_803])).
% 18.37/9.66  tff(c_42016, plain, (![B_841]: (k9_relat_1(k7_relat_1(B_841, '#skF_3'), '#skF_2')=k9_relat_1(B_841, '#skF_2') | ~v1_relat_1(B_841))), inference(superposition, [status(thm), theory('equality')], [c_41916, c_811])).
% 18.37/9.66  tff(c_38, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.37/9.66  tff(c_42051, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_42016, c_38])).
% 18.37/9.66  tff(c_42077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_42051])).
% 18.37/9.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.37/9.66  
% 18.37/9.66  Inference rules
% 18.37/9.66  ----------------------
% 18.37/9.66  #Ref     : 0
% 18.37/9.66  #Sup     : 9971
% 18.37/9.66  #Fact    : 0
% 18.37/9.66  #Define  : 0
% 18.37/9.66  #Split   : 26
% 18.37/9.66  #Chain   : 0
% 18.37/9.66  #Close   : 0
% 18.37/9.66  
% 18.37/9.66  Ordering : KBO
% 18.37/9.66  
% 18.37/9.66  Simplification rules
% 18.37/9.66  ----------------------
% 18.37/9.66  #Subsume      : 2587
% 18.37/9.66  #Demod        : 5571
% 18.37/9.66  #Tautology    : 1245
% 18.37/9.66  #SimpNegUnit  : 21
% 18.37/9.66  #BackRed      : 3
% 18.37/9.66  
% 18.37/9.66  #Partial instantiations: 0
% 18.37/9.66  #Strategies tried      : 1
% 18.37/9.66  
% 18.37/9.66  Timing (in seconds)
% 18.37/9.66  ----------------------
% 18.37/9.67  Preprocessing        : 0.31
% 18.37/9.67  Parsing              : 0.18
% 18.37/9.67  CNF conversion       : 0.02
% 18.37/9.67  Main loop            : 8.55
% 18.37/9.67  Inferencing          : 1.33
% 18.37/9.67  Reduction            : 2.40
% 18.37/9.67  Demodulation         : 1.82
% 18.37/9.67  BG Simplification    : 0.15
% 18.37/9.67  Subsumption          : 4.24
% 18.37/9.67  Abstraction          : 0.22
% 18.37/9.67  MUC search           : 0.00
% 18.37/9.67  Cooper               : 0.00
% 18.37/9.67  Total                : 8.92
% 18.37/9.67  Index Insertion      : 0.00
% 18.37/9.67  Index Deletion       : 0.00
% 18.37/9.67  Index Matching       : 0.00
% 18.37/9.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
