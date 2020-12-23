%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:00 EST 2020

% Result     : Theorem 5.78s
% Output     : CNFRefutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 144 expanded)
%              Number of leaves         :   25 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 297 expanded)
%              Number of equality atoms :   47 ( 118 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_54,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_114,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_192,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden('#skF_1'(A_76,B_77,C_78),A_76)
      | r2_hidden('#skF_2'(A_76,B_77,C_78),C_78)
      | k4_xboole_0(A_76,B_77) = C_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_240,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_2'(A_76,B_77,A_76),A_76)
      | k4_xboole_0(A_76,B_77) = A_76 ) ),
    inference(resolution,[status(thm)],[c_192,c_14])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_877,plain,(
    ! [A_129,B_130,C_131] :
      ( ~ r2_hidden('#skF_1'(A_129,B_130,C_131),C_131)
      | r2_hidden('#skF_2'(A_129,B_130,C_131),B_130)
      | ~ r2_hidden('#skF_2'(A_129,B_130,C_131),A_129)
      | k4_xboole_0(A_129,B_130) = C_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2267,plain,(
    ! [A_178,B_179] :
      ( r2_hidden('#skF_2'(A_178,B_179,A_178),B_179)
      | ~ r2_hidden('#skF_2'(A_178,B_179,A_178),A_178)
      | k4_xboole_0(A_178,B_179) = A_178 ) ),
    inference(resolution,[status(thm)],[c_12,c_877])).

tff(c_2290,plain,(
    ! [A_180,B_181] :
      ( r2_hidden('#skF_2'(A_180,B_181,A_180),B_181)
      | k4_xboole_0(A_180,B_181) = A_180 ) ),
    inference(resolution,[status(thm)],[c_240,c_2267])).

tff(c_46,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_142,plain,(
    ! [E_61,C_62,B_63,A_64] :
      ( E_61 = C_62
      | E_61 = B_63
      | E_61 = A_64
      | ~ r2_hidden(E_61,k1_enumset1(A_64,B_63,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_161,plain,(
    ! [E_65,B_66,A_67] :
      ( E_65 = B_66
      | E_65 = A_67
      | E_65 = A_67
      | ~ r2_hidden(E_65,k2_tarski(A_67,B_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_142])).

tff(c_170,plain,(
    ! [E_65,A_16] :
      ( E_65 = A_16
      | E_65 = A_16
      | E_65 = A_16
      | ~ r2_hidden(E_65,k1_tarski(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_161])).

tff(c_2338,plain,(
    ! [A_180,A_16] :
      ( '#skF_2'(A_180,k1_tarski(A_16),A_180) = A_16
      | k4_xboole_0(A_180,k1_tarski(A_16)) = A_180 ) ),
    inference(resolution,[status(thm)],[c_2290,c_170])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5053,plain,(
    ! [A_223,A_224,B_225] :
      ( ~ r2_hidden('#skF_2'(A_223,k4_xboole_0(A_224,B_225),A_223),B_225)
      | k4_xboole_0(A_223,k4_xboole_0(A_224,B_225)) = A_223 ) ),
    inference(resolution,[status(thm)],[c_2290,c_4])).

tff(c_5151,plain,(
    ! [A_226,A_227] : k4_xboole_0(A_226,k4_xboole_0(A_227,A_226)) = A_226 ),
    inference(resolution,[status(thm)],[c_240,c_5053])).

tff(c_6319,plain,(
    ! [A_243,A_244] :
      ( k4_xboole_0(k1_tarski(A_243),A_244) = k1_tarski(A_243)
      | '#skF_2'(A_244,k1_tarski(A_243),A_244) = A_243 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2338,c_5151])).

tff(c_6505,plain,(
    '#skF_2'('#skF_6',k1_tarski('#skF_5'),'#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6319,c_114])).

tff(c_6535,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6505,c_240])).

tff(c_6546,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6535])).

tff(c_5149,plain,(
    ! [A_76,A_224] : k4_xboole_0(A_76,k4_xboole_0(A_224,A_76)) = A_76 ),
    inference(resolution,[status(thm)],[c_240,c_5053])).

tff(c_6569,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6546,c_5149])).

tff(c_6608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_6569])).

tff(c_6609,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_74,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [E_15,B_10,C_11] : r2_hidden(E_15,k1_enumset1(E_15,B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_92,plain,(
    ! [A_38,B_39] : r2_hidden(A_38,k2_tarski(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_28])).

tff(c_95,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_92])).

tff(c_6610,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_58,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6658,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6610,c_58])).

tff(c_6672,plain,(
    ! [D_256] :
      ( ~ r2_hidden(D_256,'#skF_8')
      | ~ r2_hidden(D_256,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6658,c_4])).

tff(c_6676,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_95,c_6672])).

tff(c_6680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6609,c_6676])).

tff(c_6681,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_6687,plain,(
    ! [A_266,B_267] : k1_enumset1(A_266,A_266,B_267) = k2_tarski(A_266,B_267) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [E_15,A_9,C_11] : r2_hidden(E_15,k1_enumset1(A_9,E_15,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6714,plain,(
    ! [A_270,B_271] : r2_hidden(A_270,k2_tarski(A_270,B_271)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6687,c_26])).

tff(c_6717,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_6714])).

tff(c_6682,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6721,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6682,c_60])).

tff(c_6735,plain,(
    ! [D_278,B_279,A_280] :
      ( ~ r2_hidden(D_278,B_279)
      | ~ r2_hidden(D_278,k4_xboole_0(A_280,B_279)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6739,plain,(
    ! [D_281] :
      ( ~ r2_hidden(D_281,'#skF_8')
      | ~ r2_hidden(D_281,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6721,c_6735])).

tff(c_6743,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_6717,c_6739])).

tff(c_6747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6681,c_6743])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.78/2.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.20  
% 5.78/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.78/2.20  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 5.78/2.20  
% 5.78/2.20  %Foreground sorts:
% 5.78/2.20  
% 5.78/2.20  
% 5.78/2.20  %Background operators:
% 5.78/2.20  
% 5.78/2.20  
% 5.78/2.20  %Foreground operators:
% 5.78/2.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.78/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.78/2.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.78/2.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.78/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.78/2.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.78/2.20  tff('#skF_7', type, '#skF_7': $i).
% 5.78/2.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.78/2.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.78/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.78/2.20  tff('#skF_5', type, '#skF_5': $i).
% 5.78/2.20  tff('#skF_6', type, '#skF_6': $i).
% 5.78/2.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.78/2.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.78/2.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.78/2.20  tff('#skF_8', type, '#skF_8': $i).
% 5.78/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.78/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.78/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.78/2.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.78/2.20  
% 6.15/2.22  tff(f_66, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 6.15/2.22  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.15/2.22  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.15/2.22  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.15/2.22  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.15/2.22  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5') | r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.15/2.22  tff(c_114, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 6.15/2.22  tff(c_56, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.15/2.22  tff(c_70, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_56])).
% 6.15/2.22  tff(c_192, plain, (![A_76, B_77, C_78]: (r2_hidden('#skF_1'(A_76, B_77, C_78), A_76) | r2_hidden('#skF_2'(A_76, B_77, C_78), C_78) | k4_xboole_0(A_76, B_77)=C_78)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.15/2.22  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.15/2.22  tff(c_240, plain, (![A_76, B_77]: (r2_hidden('#skF_2'(A_76, B_77, A_76), A_76) | k4_xboole_0(A_76, B_77)=A_76)), inference(resolution, [status(thm)], [c_192, c_14])).
% 6.15/2.22  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.15/2.22  tff(c_877, plain, (![A_129, B_130, C_131]: (~r2_hidden('#skF_1'(A_129, B_130, C_131), C_131) | r2_hidden('#skF_2'(A_129, B_130, C_131), B_130) | ~r2_hidden('#skF_2'(A_129, B_130, C_131), A_129) | k4_xboole_0(A_129, B_130)=C_131)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.15/2.22  tff(c_2267, plain, (![A_178, B_179]: (r2_hidden('#skF_2'(A_178, B_179, A_178), B_179) | ~r2_hidden('#skF_2'(A_178, B_179, A_178), A_178) | k4_xboole_0(A_178, B_179)=A_178)), inference(resolution, [status(thm)], [c_12, c_877])).
% 6.15/2.22  tff(c_2290, plain, (![A_180, B_181]: (r2_hidden('#skF_2'(A_180, B_181, A_180), B_181) | k4_xboole_0(A_180, B_181)=A_180)), inference(resolution, [status(thm)], [c_240, c_2267])).
% 6.15/2.22  tff(c_46, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.15/2.22  tff(c_48, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.15/2.22  tff(c_142, plain, (![E_61, C_62, B_63, A_64]: (E_61=C_62 | E_61=B_63 | E_61=A_64 | ~r2_hidden(E_61, k1_enumset1(A_64, B_63, C_62)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.15/2.22  tff(c_161, plain, (![E_65, B_66, A_67]: (E_65=B_66 | E_65=A_67 | E_65=A_67 | ~r2_hidden(E_65, k2_tarski(A_67, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_142])).
% 6.15/2.22  tff(c_170, plain, (![E_65, A_16]: (E_65=A_16 | E_65=A_16 | E_65=A_16 | ~r2_hidden(E_65, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_161])).
% 6.15/2.22  tff(c_2338, plain, (![A_180, A_16]: ('#skF_2'(A_180, k1_tarski(A_16), A_180)=A_16 | k4_xboole_0(A_180, k1_tarski(A_16))=A_180)), inference(resolution, [status(thm)], [c_2290, c_170])).
% 6.15/2.22  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.15/2.22  tff(c_5053, plain, (![A_223, A_224, B_225]: (~r2_hidden('#skF_2'(A_223, k4_xboole_0(A_224, B_225), A_223), B_225) | k4_xboole_0(A_223, k4_xboole_0(A_224, B_225))=A_223)), inference(resolution, [status(thm)], [c_2290, c_4])).
% 6.15/2.22  tff(c_5151, plain, (![A_226, A_227]: (k4_xboole_0(A_226, k4_xboole_0(A_227, A_226))=A_226)), inference(resolution, [status(thm)], [c_240, c_5053])).
% 6.15/2.22  tff(c_6319, plain, (![A_243, A_244]: (k4_xboole_0(k1_tarski(A_243), A_244)=k1_tarski(A_243) | '#skF_2'(A_244, k1_tarski(A_243), A_244)=A_243)), inference(superposition, [status(thm), theory('equality')], [c_2338, c_5151])).
% 6.15/2.22  tff(c_6505, plain, ('#skF_2'('#skF_6', k1_tarski('#skF_5'), '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6319, c_114])).
% 6.15/2.22  tff(c_6535, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_6505, c_240])).
% 6.15/2.22  tff(c_6546, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_70, c_6535])).
% 6.15/2.22  tff(c_5149, plain, (![A_76, A_224]: (k4_xboole_0(A_76, k4_xboole_0(A_224, A_76))=A_76)), inference(resolution, [status(thm)], [c_240, c_5053])).
% 6.15/2.22  tff(c_6569, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6546, c_5149])).
% 6.15/2.22  tff(c_6608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_6569])).
% 6.15/2.22  tff(c_6609, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_54])).
% 6.15/2.22  tff(c_74, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.15/2.22  tff(c_28, plain, (![E_15, B_10, C_11]: (r2_hidden(E_15, k1_enumset1(E_15, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.15/2.22  tff(c_92, plain, (![A_38, B_39]: (r2_hidden(A_38, k2_tarski(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_28])).
% 6.15/2.22  tff(c_95, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_92])).
% 6.15/2.22  tff(c_6610, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 6.15/2.22  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.15/2.22  tff(c_6658, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6610, c_58])).
% 6.15/2.22  tff(c_6672, plain, (![D_256]: (~r2_hidden(D_256, '#skF_8') | ~r2_hidden(D_256, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_6658, c_4])).
% 6.15/2.22  tff(c_6676, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_95, c_6672])).
% 6.15/2.22  tff(c_6680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6609, c_6676])).
% 6.15/2.22  tff(c_6681, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_56])).
% 6.15/2.22  tff(c_6687, plain, (![A_266, B_267]: (k1_enumset1(A_266, A_266, B_267)=k2_tarski(A_266, B_267))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.15/2.22  tff(c_26, plain, (![E_15, A_9, C_11]: (r2_hidden(E_15, k1_enumset1(A_9, E_15, C_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.15/2.22  tff(c_6714, plain, (![A_270, B_271]: (r2_hidden(A_270, k2_tarski(A_270, B_271)))), inference(superposition, [status(thm), theory('equality')], [c_6687, c_26])).
% 6.15/2.22  tff(c_6717, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_6714])).
% 6.15/2.22  tff(c_6682, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_56])).
% 6.15/2.22  tff(c_60, plain, (~r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.15/2.22  tff(c_6721, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6682, c_60])).
% 6.15/2.22  tff(c_6735, plain, (![D_278, B_279, A_280]: (~r2_hidden(D_278, B_279) | ~r2_hidden(D_278, k4_xboole_0(A_280, B_279)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.15/2.22  tff(c_6739, plain, (![D_281]: (~r2_hidden(D_281, '#skF_8') | ~r2_hidden(D_281, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_6721, c_6735])).
% 6.15/2.22  tff(c_6743, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_6717, c_6739])).
% 6.15/2.22  tff(c_6747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6681, c_6743])).
% 6.15/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.22  
% 6.15/2.22  Inference rules
% 6.15/2.22  ----------------------
% 6.15/2.22  #Ref     : 0
% 6.15/2.22  #Sup     : 1791
% 6.15/2.22  #Fact    : 0
% 6.15/2.22  #Define  : 0
% 6.15/2.22  #Split   : 2
% 6.15/2.22  #Chain   : 0
% 6.15/2.22  #Close   : 0
% 6.15/2.22  
% 6.15/2.22  Ordering : KBO
% 6.15/2.22  
% 6.15/2.22  Simplification rules
% 6.15/2.22  ----------------------
% 6.15/2.22  #Subsume      : 880
% 6.15/2.22  #Demod        : 529
% 6.15/2.22  #Tautology    : 372
% 6.15/2.22  #SimpNegUnit  : 67
% 6.15/2.22  #BackRed      : 2
% 6.15/2.22  
% 6.15/2.22  #Partial instantiations: 0
% 6.15/2.22  #Strategies tried      : 1
% 6.15/2.22  
% 6.15/2.22  Timing (in seconds)
% 6.15/2.22  ----------------------
% 6.15/2.22  Preprocessing        : 0.31
% 6.15/2.22  Parsing              : 0.15
% 6.15/2.22  CNF conversion       : 0.03
% 6.15/2.22  Main loop            : 1.11
% 6.15/2.22  Inferencing          : 0.41
% 6.15/2.22  Reduction            : 0.40
% 6.15/2.22  Demodulation         : 0.32
% 6.15/2.22  BG Simplification    : 0.05
% 6.15/2.22  Subsumption          : 0.18
% 6.15/2.22  Abstraction          : 0.09
% 6.15/2.22  MUC search           : 0.00
% 6.15/2.22  Cooper               : 0.00
% 6.15/2.22  Total                : 1.45
% 6.15/2.22  Index Insertion      : 0.00
% 6.15/2.22  Index Deletion       : 0.00
% 6.15/2.22  Index Matching       : 0.00
% 6.15/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
