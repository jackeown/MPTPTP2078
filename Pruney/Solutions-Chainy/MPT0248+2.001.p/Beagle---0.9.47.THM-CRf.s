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
% DateTime   : Thu Dec  3 09:50:04 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 206 expanded)
%              Number of leaves         :   36 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 406 expanded)
%              Number of equality atoms :   65 ( 312 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_95,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(c_72,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_134,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_66,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_70,plain,
    ( k1_xboole_0 != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_133,plain,(
    k1_tarski('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_76,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_139,plain,(
    ! [A_75,B_76] : r1_tarski(A_75,k2_xboole_0(A_75,B_76)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_142,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_139])).

tff(c_512,plain,(
    ! [B_111,A_112] :
      ( B_111 = A_112
      | ~ r1_tarski(B_111,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_522,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_142,c_512])).

tff(c_533,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_522])).

tff(c_542,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_533])).

tff(c_14,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_708,plain,(
    ! [C_125,B_126,A_127] :
      ( r2_hidden(C_125,B_126)
      | ~ r2_hidden(C_125,A_127)
      | ~ r1_tarski(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_725,plain,(
    ! [A_128,B_129] :
      ( r2_hidden('#skF_2'(A_128),B_129)
      | ~ r1_tarski(A_128,B_129)
      | k1_xboole_0 = A_128 ) ),
    inference(resolution,[status(thm)],[c_14,c_708])).

tff(c_38,plain,(
    ! [C_35,A_31] :
      ( C_35 = A_31
      | ~ r2_hidden(C_35,k1_tarski(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4551,plain,(
    ! [A_5319,A_5320] :
      ( A_5319 = '#skF_2'(A_5320)
      | ~ r1_tarski(A_5320,k1_tarski(A_5319))
      | k1_xboole_0 = A_5320 ) ),
    inference(resolution,[status(thm)],[c_725,c_38])).

tff(c_4573,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_142,c_4551])).

tff(c_4585,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_4573])).

tff(c_4593,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4585,c_14])).

tff(c_4598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_542,c_4593])).

tff(c_4599,plain,(
    k1_tarski('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_36,plain,(
    ! [B_30,A_29] : k2_tarski(B_30,A_29) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4765,plain,(
    ! [A_5444,B_5445] : k3_tarski(k2_tarski(A_5444,B_5445)) = k2_xboole_0(A_5444,B_5445) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4793,plain,(
    ! [B_5447,A_5448] : k3_tarski(k2_tarski(B_5447,A_5448)) = k2_xboole_0(A_5448,B_5447) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4765])).

tff(c_68,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4820,plain,(
    ! [B_5449,A_5450] : k2_xboole_0(B_5449,A_5450) = k2_xboole_0(A_5450,B_5449) ),
    inference(superposition,[status(thm),theory(equality)],[c_4793,c_68])).

tff(c_4600,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_24,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4605,plain,(
    ! [A_18] : k2_xboole_0(A_18,'#skF_6') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4600,c_24])).

tff(c_4850,plain,(
    ! [A_5450] : k2_xboole_0('#skF_6',A_5450) = A_5450 ),
    inference(superposition,[status(thm),theory(equality)],[c_4820,c_4605])).

tff(c_4901,plain,(
    k1_tarski('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4850,c_76])).

tff(c_4903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4599,c_4901])).

tff(c_4904,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_4905,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4934,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4905,c_4905,c_74])).

tff(c_4913,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4905,c_76])).

tff(c_5111,plain,(
    ! [A_5473,B_5474] : k3_tarski(k2_tarski(A_5473,B_5474)) = k2_xboole_0(A_5473,B_5474) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5181,plain,(
    ! [A_5479,B_5480] : k3_tarski(k2_tarski(A_5479,B_5480)) = k2_xboole_0(B_5480,A_5479) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5111])).

tff(c_5208,plain,(
    ! [B_5481,A_5482] : k2_xboole_0(B_5481,A_5482) = k2_xboole_0(A_5482,B_5481) ),
    inference(superposition,[status(thm),theory(equality)],[c_5181,c_68])).

tff(c_28,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5373,plain,(
    ! [A_5488,B_5489] : r1_tarski(A_5488,k2_xboole_0(B_5489,A_5488)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5208,c_28])).

tff(c_5391,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4913,c_5373])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5406,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_5391,c_16])).

tff(c_5409,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_4934,c_5406])).

tff(c_5563,plain,(
    ! [A_5501,B_5502] :
      ( r2_hidden('#skF_1'(A_5501,B_5502),A_5501)
      | r1_tarski(A_5501,B_5502) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4969,plain,(
    ! [C_5459,A_5460] :
      ( C_5459 = A_5460
      | ~ r2_hidden(C_5459,k1_tarski(A_5460)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4976,plain,(
    ! [C_5459] :
      ( C_5459 = '#skF_5'
      | ~ r2_hidden(C_5459,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4905,c_4969])).

tff(c_5580,plain,(
    ! [B_5503] :
      ( '#skF_1'('#skF_6',B_5503) = '#skF_5'
      | r1_tarski('#skF_6',B_5503) ) ),
    inference(resolution,[status(thm)],[c_5563,c_4976])).

tff(c_5600,plain,(
    '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5580,c_5409])).

tff(c_5640,plain,(
    ! [A_5505,B_5506] :
      ( ~ r2_hidden('#skF_1'(A_5505,B_5506),B_5506)
      | r1_tarski(A_5505,B_5506) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5649,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5600,c_5640])).

tff(c_5655,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_5409,c_5649])).

tff(c_5723,plain,(
    ! [C_5512,B_5513,A_5514] :
      ( r2_hidden(C_5512,B_5513)
      | ~ r2_hidden(C_5512,A_5514)
      | ~ r1_tarski(A_5514,B_5513) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8668,plain,(
    ! [A_11473,B_11474] :
      ( r2_hidden('#skF_2'(A_11473),B_11474)
      | ~ r1_tarski(A_11473,B_11474)
      | k1_xboole_0 = A_11473 ) ),
    inference(resolution,[status(thm)],[c_14,c_5723])).

tff(c_8695,plain,(
    ! [A_11527] :
      ( '#skF_2'(A_11527) = '#skF_5'
      | ~ r1_tarski(A_11527,'#skF_6')
      | k1_xboole_0 = A_11527 ) ),
    inference(resolution,[status(thm)],[c_8668,c_4976])).

tff(c_8702,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5391,c_8695])).

tff(c_8720,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_4904,c_8702])).

tff(c_8733,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_8720,c_14])).

tff(c_8738,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4904,c_5655,c_8733])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.32  
% 6.27/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.32  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 6.27/2.32  
% 6.27/2.32  %Foreground sorts:
% 6.27/2.32  
% 6.27/2.32  
% 6.27/2.32  %Background operators:
% 6.27/2.32  
% 6.27/2.32  
% 6.27/2.32  %Foreground operators:
% 6.27/2.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.27/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.27/2.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.27/2.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.27/2.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.27/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.27/2.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.27/2.32  tff('#skF_7', type, '#skF_7': $i).
% 6.27/2.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.27/2.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.27/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.27/2.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.27/2.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.27/2.32  tff('#skF_5', type, '#skF_5': $i).
% 6.27/2.32  tff('#skF_6', type, '#skF_6': $i).
% 6.27/2.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.27/2.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.27/2.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.27/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.27/2.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.27/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.27/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.27/2.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.27/2.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.27/2.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.27/2.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.27/2.32  
% 6.42/2.34  tff(f_114, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 6.42/2.34  tff(f_93, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.42/2.34  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.42/2.34  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.42/2.34  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.42/2.34  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.42/2.34  tff(f_75, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.42/2.34  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.42/2.34  tff(f_95, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.42/2.34  tff(f_56, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.42/2.34  tff(c_72, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.42/2.34  tff(c_134, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_72])).
% 6.42/2.34  tff(c_66, plain, (![A_64, B_65]: (r1_tarski(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.42/2.34  tff(c_70, plain, (k1_xboole_0!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.42/2.34  tff(c_133, plain, (k1_tarski('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_70])).
% 6.42/2.34  tff(c_76, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.42/2.34  tff(c_139, plain, (![A_75, B_76]: (r1_tarski(A_75, k2_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.42/2.34  tff(c_142, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_139])).
% 6.42/2.34  tff(c_512, plain, (![B_111, A_112]: (B_111=A_112 | ~r1_tarski(B_111, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.42/2.34  tff(c_522, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_142, c_512])).
% 6.42/2.34  tff(c_533, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_133, c_522])).
% 6.42/2.34  tff(c_542, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_533])).
% 6.42/2.34  tff(c_14, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.42/2.34  tff(c_708, plain, (![C_125, B_126, A_127]: (r2_hidden(C_125, B_126) | ~r2_hidden(C_125, A_127) | ~r1_tarski(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.42/2.34  tff(c_725, plain, (![A_128, B_129]: (r2_hidden('#skF_2'(A_128), B_129) | ~r1_tarski(A_128, B_129) | k1_xboole_0=A_128)), inference(resolution, [status(thm)], [c_14, c_708])).
% 6.42/2.34  tff(c_38, plain, (![C_35, A_31]: (C_35=A_31 | ~r2_hidden(C_35, k1_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.42/2.34  tff(c_4551, plain, (![A_5319, A_5320]: (A_5319='#skF_2'(A_5320) | ~r1_tarski(A_5320, k1_tarski(A_5319)) | k1_xboole_0=A_5320)), inference(resolution, [status(thm)], [c_725, c_38])).
% 6.42/2.34  tff(c_4573, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_142, c_4551])).
% 6.42/2.34  tff(c_4585, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_134, c_4573])).
% 6.42/2.34  tff(c_4593, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4585, c_14])).
% 6.42/2.34  tff(c_4598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_542, c_4593])).
% 6.42/2.34  tff(c_4599, plain, (k1_tarski('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_72])).
% 6.42/2.34  tff(c_36, plain, (![B_30, A_29]: (k2_tarski(B_30, A_29)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.42/2.34  tff(c_4765, plain, (![A_5444, B_5445]: (k3_tarski(k2_tarski(A_5444, B_5445))=k2_xboole_0(A_5444, B_5445))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.42/2.34  tff(c_4793, plain, (![B_5447, A_5448]: (k3_tarski(k2_tarski(B_5447, A_5448))=k2_xboole_0(A_5448, B_5447))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4765])).
% 6.42/2.34  tff(c_68, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.42/2.34  tff(c_4820, plain, (![B_5449, A_5450]: (k2_xboole_0(B_5449, A_5450)=k2_xboole_0(A_5450, B_5449))), inference(superposition, [status(thm), theory('equality')], [c_4793, c_68])).
% 6.42/2.34  tff(c_4600, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_72])).
% 6.42/2.34  tff(c_24, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.42/2.34  tff(c_4605, plain, (![A_18]: (k2_xboole_0(A_18, '#skF_6')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_4600, c_24])).
% 6.42/2.34  tff(c_4850, plain, (![A_5450]: (k2_xboole_0('#skF_6', A_5450)=A_5450)), inference(superposition, [status(thm), theory('equality')], [c_4820, c_4605])).
% 6.42/2.34  tff(c_4901, plain, (k1_tarski('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_4850, c_76])).
% 6.42/2.34  tff(c_4903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4599, c_4901])).
% 6.42/2.34  tff(c_4904, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_70])).
% 6.42/2.34  tff(c_4905, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_70])).
% 6.42/2.34  tff(c_74, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.42/2.34  tff(c_4934, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4905, c_4905, c_74])).
% 6.42/2.34  tff(c_4913, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4905, c_76])).
% 6.42/2.34  tff(c_5111, plain, (![A_5473, B_5474]: (k3_tarski(k2_tarski(A_5473, B_5474))=k2_xboole_0(A_5473, B_5474))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.42/2.34  tff(c_5181, plain, (![A_5479, B_5480]: (k3_tarski(k2_tarski(A_5479, B_5480))=k2_xboole_0(B_5480, A_5479))), inference(superposition, [status(thm), theory('equality')], [c_36, c_5111])).
% 6.42/2.34  tff(c_5208, plain, (![B_5481, A_5482]: (k2_xboole_0(B_5481, A_5482)=k2_xboole_0(A_5482, B_5481))), inference(superposition, [status(thm), theory('equality')], [c_5181, c_68])).
% 6.42/2.34  tff(c_28, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.42/2.34  tff(c_5373, plain, (![A_5488, B_5489]: (r1_tarski(A_5488, k2_xboole_0(B_5489, A_5488)))), inference(superposition, [status(thm), theory('equality')], [c_5208, c_28])).
% 6.42/2.34  tff(c_5391, plain, (r1_tarski('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4913, c_5373])).
% 6.42/2.34  tff(c_16, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.42/2.34  tff(c_5406, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_5391, c_16])).
% 6.42/2.34  tff(c_5409, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_4934, c_5406])).
% 6.42/2.34  tff(c_5563, plain, (![A_5501, B_5502]: (r2_hidden('#skF_1'(A_5501, B_5502), A_5501) | r1_tarski(A_5501, B_5502))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.42/2.34  tff(c_4969, plain, (![C_5459, A_5460]: (C_5459=A_5460 | ~r2_hidden(C_5459, k1_tarski(A_5460)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.42/2.34  tff(c_4976, plain, (![C_5459]: (C_5459='#skF_5' | ~r2_hidden(C_5459, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4905, c_4969])).
% 6.42/2.34  tff(c_5580, plain, (![B_5503]: ('#skF_1'('#skF_6', B_5503)='#skF_5' | r1_tarski('#skF_6', B_5503))), inference(resolution, [status(thm)], [c_5563, c_4976])).
% 6.42/2.34  tff(c_5600, plain, ('#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_5580, c_5409])).
% 6.42/2.34  tff(c_5640, plain, (![A_5505, B_5506]: (~r2_hidden('#skF_1'(A_5505, B_5506), B_5506) | r1_tarski(A_5505, B_5506))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.42/2.34  tff(c_5649, plain, (~r2_hidden('#skF_5', '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5600, c_5640])).
% 6.42/2.34  tff(c_5655, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_5409, c_5649])).
% 6.42/2.34  tff(c_5723, plain, (![C_5512, B_5513, A_5514]: (r2_hidden(C_5512, B_5513) | ~r2_hidden(C_5512, A_5514) | ~r1_tarski(A_5514, B_5513))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.42/2.34  tff(c_8668, plain, (![A_11473, B_11474]: (r2_hidden('#skF_2'(A_11473), B_11474) | ~r1_tarski(A_11473, B_11474) | k1_xboole_0=A_11473)), inference(resolution, [status(thm)], [c_14, c_5723])).
% 6.42/2.34  tff(c_8695, plain, (![A_11527]: ('#skF_2'(A_11527)='#skF_5' | ~r1_tarski(A_11527, '#skF_6') | k1_xboole_0=A_11527)), inference(resolution, [status(thm)], [c_8668, c_4976])).
% 6.42/2.34  tff(c_8702, plain, ('#skF_2'('#skF_7')='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_5391, c_8695])).
% 6.42/2.34  tff(c_8720, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_4904, c_8702])).
% 6.42/2.34  tff(c_8733, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_8720, c_14])).
% 6.42/2.34  tff(c_8738, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4904, c_5655, c_8733])).
% 6.42/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.34  
% 6.42/2.34  Inference rules
% 6.42/2.34  ----------------------
% 6.42/2.34  #Ref     : 0
% 6.42/2.34  #Sup     : 1627
% 6.42/2.34  #Fact    : 0
% 6.42/2.34  #Define  : 0
% 6.42/2.34  #Split   : 6
% 6.42/2.34  #Chain   : 0
% 6.42/2.34  #Close   : 0
% 6.42/2.34  
% 6.42/2.34  Ordering : KBO
% 6.42/2.34  
% 6.42/2.34  Simplification rules
% 6.42/2.34  ----------------------
% 6.42/2.34  #Subsume      : 54
% 6.42/2.34  #Demod        : 882
% 6.42/2.34  #Tautology    : 1004
% 6.42/2.34  #SimpNegUnit  : 33
% 6.42/2.34  #BackRed      : 8
% 6.42/2.34  
% 6.42/2.34  #Partial instantiations: 4515
% 6.42/2.34  #Strategies tried      : 1
% 6.42/2.34  
% 6.42/2.34  Timing (in seconds)
% 6.42/2.34  ----------------------
% 6.42/2.34  Preprocessing        : 0.36
% 6.42/2.34  Parsing              : 0.17
% 6.42/2.34  CNF conversion       : 0.03
% 6.42/2.34  Main loop            : 1.18
% 6.42/2.34  Inferencing          : 0.47
% 6.42/2.34  Reduction            : 0.42
% 6.42/2.34  Demodulation         : 0.33
% 6.42/2.34  BG Simplification    : 0.05
% 6.42/2.34  Subsumption          : 0.16
% 6.42/2.34  Abstraction          : 0.04
% 6.42/2.34  MUC search           : 0.00
% 6.42/2.34  Cooper               : 0.00
% 6.42/2.34  Total                : 1.58
% 6.42/2.34  Index Insertion      : 0.00
% 6.42/2.34  Index Deletion       : 0.00
% 6.42/2.34  Index Matching       : 0.00
% 6.42/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
