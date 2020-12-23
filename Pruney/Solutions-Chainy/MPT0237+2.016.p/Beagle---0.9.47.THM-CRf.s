%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:47 EST 2020

% Result     : Theorem 6.17s
% Output     : CNFRefutation 6.38s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 346 expanded)
%              Number of leaves         :   39 ( 133 expanded)
%              Depth                    :   12
%              Number of atoms          :   96 ( 424 expanded)
%              Number of equality atoms :   73 ( 336 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_83,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_40,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_122,plain,(
    ! [A_73,B_74] : k1_enumset1(A_73,A_73,B_74) = k2_tarski(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [E_19,A_13,C_15] : r2_hidden(E_19,k1_enumset1(A_13,E_19,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_140,plain,(
    ! [A_75,B_76] : r2_hidden(A_75,k2_tarski(A_75,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_20])).

tff(c_143,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_140])).

tff(c_152,plain,(
    ! [A_82,B_83] :
      ( r1_xboole_0(k1_tarski(A_82),k1_tarski(B_83))
      | B_83 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(k1_tarski(A_82),k1_tarski(B_83)) = k1_tarski(A_82)
      | B_83 = A_82 ) ),
    inference(resolution,[status(thm)],[c_152,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_208,plain,(
    ! [A_92,B_93] : k5_xboole_0(A_92,k3_xboole_0(A_92,B_93)) = k4_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_217,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_208])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] : k5_xboole_0(k5_xboole_0(A_8,B_9),C_10) = k5_xboole_0(A_8,k5_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_601,plain,(
    ! [A_120,B_121] : k5_xboole_0(k5_xboole_0(A_120,B_121),k3_xboole_0(A_120,B_121)) = k2_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_629,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k5_xboole_0(B_9,k3_xboole_0(A_8,B_9))) = k2_xboole_0(A_8,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_601])).

tff(c_817,plain,(
    ! [A_135,B_136] : k5_xboole_0(A_135,k4_xboole_0(B_136,A_135)) = k2_xboole_0(A_135,B_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_629])).

tff(c_3262,plain,(
    ! [B_246,A_247] :
      ( k5_xboole_0(k1_tarski(B_246),k1_tarski(A_247)) = k2_xboole_0(k1_tarski(B_246),k1_tarski(A_247))
      | B_246 = A_247 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_817])).

tff(c_64,plain,(
    ! [A_58,B_59] :
      ( k5_xboole_0(k1_tarski(A_58),k1_tarski(B_59)) = k2_tarski(A_58,B_59)
      | B_59 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5700,plain,(
    ! [B_279,A_280] :
      ( k2_xboole_0(k1_tarski(B_279),k1_tarski(A_280)) = k2_tarski(B_279,A_280)
      | B_279 = A_280
      | B_279 = A_280 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3262,c_64])).

tff(c_56,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_66,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_67,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66])).

tff(c_5746,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5700,c_67])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_56,B_57] : k4_xboole_0(k1_tarski(A_56),k2_tarski(A_56,B_57)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_223,plain,(
    ! [A_94,B_95] : k3_xboole_0(k1_tarski(A_94),k2_tarski(A_94,B_95)) = k1_tarski(A_94) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_229,plain,(
    ! [A_94,B_95] : k5_xboole_0(k1_tarski(A_94),k1_tarski(A_94)) = k4_xboole_0(k1_tarski(A_94),k2_tarski(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_4])).

tff(c_237,plain,(
    ! [A_94] : k5_xboole_0(k1_tarski(A_94),k1_tarski(A_94)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_229])).

tff(c_54,plain,(
    ! [B_49,A_48] :
      ( k3_xboole_0(B_49,k1_tarski(A_48)) = k1_tarski(A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_638,plain,(
    ! [B_49,A_48] :
      ( k5_xboole_0(k5_xboole_0(B_49,k1_tarski(A_48)),k1_tarski(A_48)) = k2_xboole_0(B_49,k1_tarski(A_48))
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_601])).

tff(c_782,plain,(
    ! [B_132,A_133] :
      ( k2_xboole_0(B_132,k1_tarski(A_133)) = B_132
      | ~ r2_hidden(A_133,B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_237,c_12,c_638])).

tff(c_792,plain,
    ( k2_tarski('#skF_3','#skF_4') != k1_tarski('#skF_3')
    | ~ r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_782,c_67])).

tff(c_816,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_792])).

tff(c_5752,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_816])).

tff(c_5756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_5752])).

tff(c_5758,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_792])).

tff(c_382,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(k1_tarski(A_107),k1_tarski(B_108)) = k1_tarski(A_107)
      | B_108 = A_107 ) ),
    inference(resolution,[status(thm)],[c_152,c_8])).

tff(c_303,plain,(
    ! [B_103,A_104] :
      ( k3_xboole_0(B_103,k1_tarski(A_104)) = k1_tarski(A_104)
      | ~ r2_hidden(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_309,plain,(
    ! [A_104,B_103] :
      ( k5_xboole_0(k1_tarski(A_104),k1_tarski(A_104)) = k4_xboole_0(k1_tarski(A_104),B_103)
      | ~ r2_hidden(A_104,B_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_217])).

tff(c_338,plain,(
    ! [A_104,B_103] :
      ( k4_xboole_0(k1_tarski(A_104),B_103) = k1_xboole_0
      | ~ r2_hidden(A_104,B_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_309])).

tff(c_388,plain,(
    ! [A_107,B_108] :
      ( k1_tarski(A_107) = k1_xboole_0
      | ~ r2_hidden(A_107,k1_tarski(B_108))
      | B_108 = A_107 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_338])).

tff(c_5762,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5758,c_388])).

tff(c_5763,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5762])).

tff(c_5757,plain,(
    k2_tarski('#skF_3','#skF_4') != k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_792])).

tff(c_5764,plain,(
    k2_tarski('#skF_4','#skF_4') != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5763,c_5763,c_5757])).

tff(c_5769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5764])).

tff(c_5771,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5762])).

tff(c_5770,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5762])).

tff(c_5791,plain,(
    ! [A_58] :
      ( k5_xboole_0(k1_tarski(A_58),k1_xboole_0) = k2_tarski(A_58,'#skF_4')
      | A_58 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5770,c_64])).

tff(c_5984,plain,(
    ! [A_303] :
      ( k2_tarski(A_303,'#skF_4') = k1_tarski(A_303)
      | A_303 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5791])).

tff(c_5998,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5984,c_5757])).

tff(c_6033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5771,c_5998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.17/2.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.17/2.34  
% 6.17/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.17/2.34  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.17/2.34  
% 6.17/2.34  %Foreground sorts:
% 6.17/2.34  
% 6.17/2.34  
% 6.17/2.34  %Background operators:
% 6.17/2.34  
% 6.17/2.34  
% 6.17/2.34  %Foreground operators:
% 6.17/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.17/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.17/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.17/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.17/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.17/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.17/2.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.17/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.17/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.17/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.17/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.17/2.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.17/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.17/2.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.17/2.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.17/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.17/2.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.17/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.17/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.17/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.17/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.17/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.17/2.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.17/2.34  
% 6.38/2.36  tff(f_56, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.38/2.36  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.38/2.36  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.38/2.36  tff(f_79, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 6.38/2.36  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.38/2.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.38/2.36  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.38/2.36  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.38/2.36  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.38/2.36  tff(f_88, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 6.38/2.36  tff(f_74, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.38/2.36  tff(f_91, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 6.38/2.36  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.38/2.36  tff(f_83, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 6.38/2.36  tff(f_81, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 6.38/2.36  tff(f_72, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 6.38/2.36  tff(c_40, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.38/2.36  tff(c_122, plain, (![A_73, B_74]: (k1_enumset1(A_73, A_73, B_74)=k2_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.38/2.36  tff(c_20, plain, (![E_19, A_13, C_15]: (r2_hidden(E_19, k1_enumset1(A_13, E_19, C_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.38/2.36  tff(c_140, plain, (![A_75, B_76]: (r2_hidden(A_75, k2_tarski(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_20])).
% 6.38/2.36  tff(c_143, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_140])).
% 6.38/2.36  tff(c_152, plain, (![A_82, B_83]: (r1_xboole_0(k1_tarski(A_82), k1_tarski(B_83)) | B_83=A_82)), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.38/2.36  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.38/2.36  tff(c_156, plain, (![A_82, B_83]: (k4_xboole_0(k1_tarski(A_82), k1_tarski(B_83))=k1_tarski(A_82) | B_83=A_82)), inference(resolution, [status(thm)], [c_152, c_8])).
% 6.38/2.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.38/2.36  tff(c_208, plain, (![A_92, B_93]: (k5_xboole_0(A_92, k3_xboole_0(A_92, B_93))=k4_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.38/2.36  tff(c_217, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_208])).
% 6.38/2.36  tff(c_12, plain, (![A_8, B_9, C_10]: (k5_xboole_0(k5_xboole_0(A_8, B_9), C_10)=k5_xboole_0(A_8, k5_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.38/2.36  tff(c_601, plain, (![A_120, B_121]: (k5_xboole_0(k5_xboole_0(A_120, B_121), k3_xboole_0(A_120, B_121))=k2_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.38/2.36  tff(c_629, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k5_xboole_0(B_9, k3_xboole_0(A_8, B_9)))=k2_xboole_0(A_8, B_9))), inference(superposition, [status(thm), theory('equality')], [c_12, c_601])).
% 6.38/2.36  tff(c_817, plain, (![A_135, B_136]: (k5_xboole_0(A_135, k4_xboole_0(B_136, A_135))=k2_xboole_0(A_135, B_136))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_629])).
% 6.38/2.36  tff(c_3262, plain, (![B_246, A_247]: (k5_xboole_0(k1_tarski(B_246), k1_tarski(A_247))=k2_xboole_0(k1_tarski(B_246), k1_tarski(A_247)) | B_246=A_247)), inference(superposition, [status(thm), theory('equality')], [c_156, c_817])).
% 6.38/2.36  tff(c_64, plain, (![A_58, B_59]: (k5_xboole_0(k1_tarski(A_58), k1_tarski(B_59))=k2_tarski(A_58, B_59) | B_59=A_58)), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.38/2.36  tff(c_5700, plain, (![B_279, A_280]: (k2_xboole_0(k1_tarski(B_279), k1_tarski(A_280))=k2_tarski(B_279, A_280) | B_279=A_280 | B_279=A_280)), inference(superposition, [status(thm), theory('equality')], [c_3262, c_64])).
% 6.38/2.36  tff(c_56, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.38/2.36  tff(c_66, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.38/2.36  tff(c_67, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_66])).
% 6.38/2.36  tff(c_5746, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5700, c_67])).
% 6.38/2.36  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.38/2.36  tff(c_62, plain, (![A_56, B_57]: (k4_xboole_0(k1_tarski(A_56), k2_tarski(A_56, B_57))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.38/2.36  tff(c_223, plain, (![A_94, B_95]: (k3_xboole_0(k1_tarski(A_94), k2_tarski(A_94, B_95))=k1_tarski(A_94))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.38/2.36  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.38/2.36  tff(c_229, plain, (![A_94, B_95]: (k5_xboole_0(k1_tarski(A_94), k1_tarski(A_94))=k4_xboole_0(k1_tarski(A_94), k2_tarski(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_223, c_4])).
% 6.38/2.36  tff(c_237, plain, (![A_94]: (k5_xboole_0(k1_tarski(A_94), k1_tarski(A_94))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_229])).
% 6.38/2.36  tff(c_54, plain, (![B_49, A_48]: (k3_xboole_0(B_49, k1_tarski(A_48))=k1_tarski(A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.38/2.36  tff(c_638, plain, (![B_49, A_48]: (k5_xboole_0(k5_xboole_0(B_49, k1_tarski(A_48)), k1_tarski(A_48))=k2_xboole_0(B_49, k1_tarski(A_48)) | ~r2_hidden(A_48, B_49))), inference(superposition, [status(thm), theory('equality')], [c_54, c_601])).
% 6.38/2.36  tff(c_782, plain, (![B_132, A_133]: (k2_xboole_0(B_132, k1_tarski(A_133))=B_132 | ~r2_hidden(A_133, B_132))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_237, c_12, c_638])).
% 6.38/2.36  tff(c_792, plain, (k2_tarski('#skF_3', '#skF_4')!=k1_tarski('#skF_3') | ~r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_782, c_67])).
% 6.38/2.36  tff(c_816, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_792])).
% 6.38/2.36  tff(c_5752, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5746, c_816])).
% 6.38/2.36  tff(c_5756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_5752])).
% 6.38/2.36  tff(c_5758, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_792])).
% 6.38/2.36  tff(c_382, plain, (![A_107, B_108]: (k4_xboole_0(k1_tarski(A_107), k1_tarski(B_108))=k1_tarski(A_107) | B_108=A_107)), inference(resolution, [status(thm)], [c_152, c_8])).
% 6.38/2.36  tff(c_303, plain, (![B_103, A_104]: (k3_xboole_0(B_103, k1_tarski(A_104))=k1_tarski(A_104) | ~r2_hidden(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.38/2.36  tff(c_309, plain, (![A_104, B_103]: (k5_xboole_0(k1_tarski(A_104), k1_tarski(A_104))=k4_xboole_0(k1_tarski(A_104), B_103) | ~r2_hidden(A_104, B_103))), inference(superposition, [status(thm), theory('equality')], [c_303, c_217])).
% 6.38/2.36  tff(c_338, plain, (![A_104, B_103]: (k4_xboole_0(k1_tarski(A_104), B_103)=k1_xboole_0 | ~r2_hidden(A_104, B_103))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_309])).
% 6.38/2.36  tff(c_388, plain, (![A_107, B_108]: (k1_tarski(A_107)=k1_xboole_0 | ~r2_hidden(A_107, k1_tarski(B_108)) | B_108=A_107)), inference(superposition, [status(thm), theory('equality')], [c_382, c_338])).
% 6.38/2.36  tff(c_5762, plain, (k1_tarski('#skF_4')=k1_xboole_0 | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_5758, c_388])).
% 6.38/2.36  tff(c_5763, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_5762])).
% 6.38/2.36  tff(c_5757, plain, (k2_tarski('#skF_3', '#skF_4')!=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_792])).
% 6.38/2.36  tff(c_5764, plain, (k2_tarski('#skF_4', '#skF_4')!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5763, c_5763, c_5757])).
% 6.38/2.36  tff(c_5769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_5764])).
% 6.38/2.36  tff(c_5771, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_5762])).
% 6.38/2.36  tff(c_5770, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_5762])).
% 6.38/2.36  tff(c_5791, plain, (![A_58]: (k5_xboole_0(k1_tarski(A_58), k1_xboole_0)=k2_tarski(A_58, '#skF_4') | A_58='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5770, c_64])).
% 6.38/2.36  tff(c_5984, plain, (![A_303]: (k2_tarski(A_303, '#skF_4')=k1_tarski(A_303) | A_303='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5791])).
% 6.38/2.36  tff(c_5998, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5984, c_5757])).
% 6.38/2.36  tff(c_6033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5771, c_5998])).
% 6.38/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.36  
% 6.38/2.36  Inference rules
% 6.38/2.36  ----------------------
% 6.38/2.36  #Ref     : 0
% 6.38/2.36  #Sup     : 1404
% 6.38/2.36  #Fact    : 0
% 6.38/2.36  #Define  : 0
% 6.38/2.36  #Split   : 2
% 6.38/2.36  #Chain   : 0
% 6.38/2.36  #Close   : 0
% 6.38/2.36  
% 6.38/2.36  Ordering : KBO
% 6.38/2.36  
% 6.38/2.36  Simplification rules
% 6.38/2.36  ----------------------
% 6.38/2.36  #Subsume      : 76
% 6.38/2.36  #Demod        : 1251
% 6.38/2.36  #Tautology    : 579
% 6.38/2.36  #SimpNegUnit  : 1
% 6.38/2.36  #BackRed      : 7
% 6.38/2.36  
% 6.38/2.36  #Partial instantiations: 0
% 6.38/2.36  #Strategies tried      : 1
% 6.38/2.36  
% 6.38/2.36  Timing (in seconds)
% 6.38/2.36  ----------------------
% 6.38/2.36  Preprocessing        : 0.35
% 6.38/2.36  Parsing              : 0.18
% 6.38/2.36  CNF conversion       : 0.02
% 6.38/2.36  Main loop            : 1.20
% 6.38/2.36  Inferencing          : 0.35
% 6.38/2.36  Reduction            : 0.58
% 6.38/2.36  Demodulation         : 0.49
% 6.38/2.36  BG Simplification    : 0.05
% 6.38/2.36  Subsumption          : 0.16
% 6.38/2.36  Abstraction          : 0.07
% 6.38/2.36  MUC search           : 0.00
% 6.38/2.36  Cooper               : 0.00
% 6.38/2.36  Total                : 1.58
% 6.38/2.36  Index Insertion      : 0.00
% 6.38/2.36  Index Deletion       : 0.00
% 6.38/2.36  Index Matching       : 0.00
% 6.38/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
