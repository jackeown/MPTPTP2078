%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:49 EST 2020

% Result     : Theorem 23.78s
% Output     : CNFRefutation 23.78s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 361 expanded)
%              Number of leaves         :   25 ( 129 expanded)
%              Depth                    :   16
%              Number of atoms          :  133 ( 614 expanded)
%              Number of equality atoms :   54 ( 258 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_32,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_57,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_28])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_199,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = k1_xboole_0
      | ~ r1_xboole_0(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_207,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_199])).

tff(c_239,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_258,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_239])).

tff(c_271,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_258])).

tff(c_689,plain,(
    ! [A_74,B_75,C_76] :
      ( r1_tarski(k4_xboole_0(A_74,B_75),C_76)
      | ~ r1_tarski(A_74,k2_xboole_0(B_75,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1588,plain,(
    ! [C_106] :
      ( r1_tarski('#skF_3',C_106)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_1',C_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_689])).

tff(c_1606,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_57,c_1588])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1616,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1606,c_8])).

tff(c_49,plain,(
    ! [A_35,B_36] : r1_tarski(k4_xboole_0(A_35,B_36),A_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_49])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k2_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_61])).

tff(c_2314,plain,(
    ! [A_124,B_125,C_126] :
      ( k4_xboole_0(k4_xboole_0(A_124,B_125),C_126) = k1_xboole_0
      | ~ r1_tarski(A_124,k2_xboole_0(B_125,C_126)) ) ),
    inference(resolution,[status(thm)],[c_689,c_8])).

tff(c_2401,plain,(
    ! [B_127,C_128] : k4_xboole_0(k4_xboole_0(k2_xboole_0(B_127,C_128),B_127),C_128) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_2314])).

tff(c_2516,plain,(
    ! [B_129] : k4_xboole_0(k2_xboole_0(B_129,k1_xboole_0),B_129) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2401,c_16])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | k4_xboole_0(B_9,A_8) != k4_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2558,plain,(
    ! [B_129] :
      ( k2_xboole_0(B_129,k1_xboole_0) = B_129
      | k4_xboole_0(B_129,k2_xboole_0(B_129,k1_xboole_0)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2516,c_12])).

tff(c_2627,plain,(
    ! [B_130] : k2_xboole_0(B_130,k1_xboole_0) = B_130 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2558])).

tff(c_2883,plain,(
    ! [A_134,B_135] :
      ( r1_tarski(A_134,B_135)
      | ~ r1_tarski(A_134,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2627,c_10])).

tff(c_2910,plain,(
    ! [A_3,B_135] :
      ( r1_tarski(A_3,B_135)
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_2883])).

tff(c_2944,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(A_136,B_137)
      | k1_xboole_0 != A_136 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2910])).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1121,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_xboole_0 = A_88
      | ~ r1_xboole_0(B_89,C_90)
      | ~ r1_tarski(A_88,C_90)
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1200,plain,(
    ! [A_93] :
      ( k1_xboole_0 = A_93
      | ~ r1_tarski(A_93,'#skF_2')
      | ~ r1_tarski(A_93,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_1121])).

tff(c_1252,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1200])).

tff(c_1260,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1252])).

tff(c_3001,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2944,c_1260])).

tff(c_1265,plain,(
    ! [A_94,C_95,B_96] :
      ( r1_tarski(k2_xboole_0(A_94,C_95),B_96)
      | ~ r1_tarski(C_95,B_96)
      | ~ r1_tarski(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4317,plain,(
    ! [A_156,C_157,B_158] :
      ( k4_xboole_0(k2_xboole_0(A_156,C_157),B_158) = k1_xboole_0
      | ~ r1_tarski(C_157,B_158)
      | ~ r1_tarski(A_156,B_158) ) ),
    inference(resolution,[status(thm)],[c_1265,c_8])).

tff(c_47120,plain,(
    ! [A_618,C_619,B_620] :
      ( k2_xboole_0(A_618,C_619) = B_620
      | k4_xboole_0(B_620,k2_xboole_0(A_618,C_619)) != k1_xboole_0
      | ~ r1_tarski(C_619,B_620)
      | ~ r1_tarski(A_618,B_620) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4317,c_12])).

tff(c_47220,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(B_28,A_27)
      | ~ r1_tarski(A_27,A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_47120])).

tff(c_47290,plain,(
    ! [A_623,B_624] :
      ( k2_xboole_0(A_623,B_624) = A_623
      | ~ r1_tarski(B_624,A_623) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_47220])).

tff(c_47375,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1606,c_47290])).

tff(c_1130,plain,(
    ! [A_88] :
      ( k1_xboole_0 = A_88
      | ~ r1_tarski(A_88,'#skF_1')
      | ~ r1_tarski(A_88,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_1121])).

tff(c_1288,plain,(
    ! [A_94,C_95] :
      ( k2_xboole_0(A_94,C_95) = k1_xboole_0
      | ~ r1_tarski(k2_xboole_0(A_94,C_95),'#skF_1')
      | ~ r1_tarski(C_95,'#skF_3')
      | ~ r1_tarski(A_94,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1265,c_1130])).

tff(c_47910,plain,
    ( k2_xboole_0('#skF_2','#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_47375,c_1288])).

tff(c_48037,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_47375,c_47910])).

tff(c_48038,plain,
    ( ~ r1_tarski('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_3001,c_48037])).

tff(c_49415,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48038])).

tff(c_49423,plain,(
    k4_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_49415])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(k4_xboole_0(A_13,B_14),C_15)
      | ~ r1_tarski(A_13,k2_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6851,plain,(
    ! [B_200] :
      ( k4_xboole_0('#skF_2',B_200) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0('#skF_2',B_200),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_1200])).

tff(c_99512,plain,(
    ! [B_912] :
      ( k4_xboole_0('#skF_2',B_912) = k1_xboole_0
      | ~ r1_tarski('#skF_2',k2_xboole_0(B_912,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18,c_6851])).

tff(c_99556,plain,
    ( k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_99512])).

tff(c_99568,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_49423,c_99556])).

tff(c_99594,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_99568])).

tff(c_99607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_99594])).

tff(c_99609,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48038])).

tff(c_99712,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99609,c_8])).

tff(c_99950,plain,
    ( '#skF_2' = '#skF_3'
    | k4_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99712,c_12])).

tff(c_100028,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_99950])).

tff(c_100030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_100028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.78/15.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.78/15.09  
% 23.78/15.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.78/15.10  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 23.78/15.10  
% 23.78/15.10  %Foreground sorts:
% 23.78/15.10  
% 23.78/15.10  
% 23.78/15.10  %Background operators:
% 23.78/15.10  
% 23.78/15.10  
% 23.78/15.10  %Foreground operators:
% 23.78/15.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.78/15.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.78/15.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.78/15.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.78/15.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 23.78/15.10  tff('#skF_2', type, '#skF_2': $i).
% 23.78/15.10  tff('#skF_3', type, '#skF_3': $i).
% 23.78/15.10  tff('#skF_1', type, '#skF_1': $i).
% 23.78/15.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.78/15.10  tff('#skF_4', type, '#skF_4': $i).
% 23.78/15.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.78/15.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.78/15.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.78/15.10  
% 23.78/15.11  tff(f_86, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 23.78/15.11  tff(f_71, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 23.78/15.11  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 23.78/15.11  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 23.78/15.11  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 23.78/15.11  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 23.78/15.11  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 23.78/15.11  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 23.78/15.11  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 23.78/15.11  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 23.78/15.11  tff(f_69, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 23.78/15.11  tff(f_77, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 23.78/15.11  tff(c_32, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.78/15.11  tff(c_38, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.78/15.11  tff(c_28, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 23.78/15.11  tff(c_57, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_28])).
% 23.78/15.11  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.78/15.11  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.78/15.11  tff(c_199, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=k1_xboole_0 | ~r1_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.78/15.11  tff(c_207, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_199])).
% 23.78/15.11  tff(c_239, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 23.78/15.11  tff(c_258, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_207, c_239])).
% 23.78/15.11  tff(c_271, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_258])).
% 23.78/15.11  tff(c_689, plain, (![A_74, B_75, C_76]: (r1_tarski(k4_xboole_0(A_74, B_75), C_76) | ~r1_tarski(A_74, k2_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 23.78/15.11  tff(c_1588, plain, (![C_106]: (r1_tarski('#skF_3', C_106) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_1', C_106)))), inference(superposition, [status(thm), theory('equality')], [c_271, c_689])).
% 23.78/15.11  tff(c_1606, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_57, c_1588])).
% 23.78/15.11  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.78/15.11  tff(c_1616, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1606, c_8])).
% 23.78/15.11  tff(c_49, plain, (![A_35, B_36]: (r1_tarski(k4_xboole_0(A_35, B_36), A_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.78/15.11  tff(c_52, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_49])).
% 23.78/15.11  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.78/15.11  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.78/15.11  tff(c_61, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.78/15.11  tff(c_77, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k2_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_61])).
% 23.78/15.11  tff(c_2314, plain, (![A_124, B_125, C_126]: (k4_xboole_0(k4_xboole_0(A_124, B_125), C_126)=k1_xboole_0 | ~r1_tarski(A_124, k2_xboole_0(B_125, C_126)))), inference(resolution, [status(thm)], [c_689, c_8])).
% 23.78/15.11  tff(c_2401, plain, (![B_127, C_128]: (k4_xboole_0(k4_xboole_0(k2_xboole_0(B_127, C_128), B_127), C_128)=k1_xboole_0)), inference(resolution, [status(thm)], [c_52, c_2314])).
% 23.78/15.11  tff(c_2516, plain, (![B_129]: (k4_xboole_0(k2_xboole_0(B_129, k1_xboole_0), B_129)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2401, c_16])).
% 23.78/15.11  tff(c_12, plain, (![B_9, A_8]: (B_9=A_8 | k4_xboole_0(B_9, A_8)!=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.78/15.11  tff(c_2558, plain, (![B_129]: (k2_xboole_0(B_129, k1_xboole_0)=B_129 | k4_xboole_0(B_129, k2_xboole_0(B_129, k1_xboole_0))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2516, c_12])).
% 23.78/15.11  tff(c_2627, plain, (![B_130]: (k2_xboole_0(B_130, k1_xboole_0)=B_130)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2558])).
% 23.78/15.11  tff(c_2883, plain, (![A_134, B_135]: (r1_tarski(A_134, B_135) | ~r1_tarski(A_134, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2627, c_10])).
% 23.78/15.11  tff(c_2910, plain, (![A_3, B_135]: (r1_tarski(A_3, B_135) | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2883])).
% 23.78/15.11  tff(c_2944, plain, (![A_136, B_137]: (r1_tarski(A_136, B_137) | k1_xboole_0!=A_136)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2910])).
% 23.78/15.11  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.78/15.11  tff(c_1121, plain, (![A_88, B_89, C_90]: (k1_xboole_0=A_88 | ~r1_xboole_0(B_89, C_90) | ~r1_tarski(A_88, C_90) | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_69])).
% 23.78/15.11  tff(c_1200, plain, (![A_93]: (k1_xboole_0=A_93 | ~r1_tarski(A_93, '#skF_2') | ~r1_tarski(A_93, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_1121])).
% 23.78/15.11  tff(c_1252, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1200])).
% 23.78/15.11  tff(c_1260, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_1252])).
% 23.78/15.11  tff(c_3001, plain, (k1_xboole_0!='#skF_2'), inference(resolution, [status(thm)], [c_2944, c_1260])).
% 23.78/15.11  tff(c_1265, plain, (![A_94, C_95, B_96]: (r1_tarski(k2_xboole_0(A_94, C_95), B_96) | ~r1_tarski(C_95, B_96) | ~r1_tarski(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_77])).
% 23.78/15.11  tff(c_4317, plain, (![A_156, C_157, B_158]: (k4_xboole_0(k2_xboole_0(A_156, C_157), B_158)=k1_xboole_0 | ~r1_tarski(C_157, B_158) | ~r1_tarski(A_156, B_158))), inference(resolution, [status(thm)], [c_1265, c_8])).
% 23.78/15.11  tff(c_47120, plain, (![A_618, C_619, B_620]: (k2_xboole_0(A_618, C_619)=B_620 | k4_xboole_0(B_620, k2_xboole_0(A_618, C_619))!=k1_xboole_0 | ~r1_tarski(C_619, B_620) | ~r1_tarski(A_618, B_620))), inference(superposition, [status(thm), theory('equality')], [c_4317, c_12])).
% 23.78/15.11  tff(c_47220, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(B_28, A_27) | ~r1_tarski(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_77, c_47120])).
% 23.78/15.11  tff(c_47290, plain, (![A_623, B_624]: (k2_xboole_0(A_623, B_624)=A_623 | ~r1_tarski(B_624, A_623))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_47220])).
% 23.78/15.11  tff(c_47375, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_1606, c_47290])).
% 23.78/15.11  tff(c_1130, plain, (![A_88]: (k1_xboole_0=A_88 | ~r1_tarski(A_88, '#skF_1') | ~r1_tarski(A_88, '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_1121])).
% 23.78/15.11  tff(c_1288, plain, (![A_94, C_95]: (k2_xboole_0(A_94, C_95)=k1_xboole_0 | ~r1_tarski(k2_xboole_0(A_94, C_95), '#skF_1') | ~r1_tarski(C_95, '#skF_3') | ~r1_tarski(A_94, '#skF_3'))), inference(resolution, [status(thm)], [c_1265, c_1130])).
% 23.78/15.11  tff(c_47910, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_2', '#skF_1') | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_47375, c_1288])).
% 23.78/15.11  tff(c_48037, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_47375, c_47910])).
% 23.78/15.11  tff(c_48038, plain, (~r1_tarski('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_3001, c_48037])).
% 23.78/15.11  tff(c_49415, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_48038])).
% 23.78/15.11  tff(c_49423, plain, (k4_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_49415])).
% 23.78/15.11  tff(c_18, plain, (![A_13, B_14, C_15]: (r1_tarski(k4_xboole_0(A_13, B_14), C_15) | ~r1_tarski(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 23.78/15.11  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.78/15.11  tff(c_6851, plain, (![B_200]: (k4_xboole_0('#skF_2', B_200)=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_2', B_200), '#skF_4'))), inference(resolution, [status(thm)], [c_14, c_1200])).
% 23.78/15.11  tff(c_99512, plain, (![B_912]: (k4_xboole_0('#skF_2', B_912)=k1_xboole_0 | ~r1_tarski('#skF_2', k2_xboole_0(B_912, '#skF_4')))), inference(resolution, [status(thm)], [c_18, c_6851])).
% 23.78/15.11  tff(c_99556, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_99512])).
% 23.78/15.11  tff(c_99568, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_49423, c_99556])).
% 23.78/15.11  tff(c_99594, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_99568])).
% 23.78/15.11  tff(c_99607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_99594])).
% 23.78/15.11  tff(c_99609, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48038])).
% 23.78/15.11  tff(c_99712, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_99609, c_8])).
% 23.78/15.11  tff(c_99950, plain, ('#skF_2'='#skF_3' | k4_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_99712, c_12])).
% 23.78/15.11  tff(c_100028, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_99950])).
% 23.78/15.11  tff(c_100030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_100028])).
% 23.78/15.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.78/15.11  
% 23.78/15.11  Inference rules
% 23.78/15.11  ----------------------
% 23.78/15.11  #Ref     : 6
% 23.78/15.11  #Sup     : 24602
% 23.78/15.11  #Fact    : 0
% 23.78/15.11  #Define  : 0
% 23.78/15.11  #Split   : 19
% 23.78/15.11  #Chain   : 0
% 23.78/15.11  #Close   : 0
% 23.78/15.11  
% 23.78/15.11  Ordering : KBO
% 23.78/15.11  
% 23.78/15.11  Simplification rules
% 23.78/15.11  ----------------------
% 23.78/15.11  #Subsume      : 9658
% 23.78/15.11  #Demod        : 17013
% 23.78/15.11  #Tautology    : 10998
% 23.78/15.11  #SimpNegUnit  : 990
% 23.78/15.11  #BackRed      : 205
% 23.78/15.11  
% 23.78/15.11  #Partial instantiations: 0
% 23.78/15.11  #Strategies tried      : 1
% 23.78/15.11  
% 23.78/15.11  Timing (in seconds)
% 23.78/15.11  ----------------------
% 23.78/15.12  Preprocessing        : 0.31
% 23.78/15.12  Parsing              : 0.16
% 23.78/15.12  CNF conversion       : 0.02
% 23.78/15.12  Main loop            : 14.00
% 23.78/15.12  Inferencing          : 1.55
% 23.78/15.12  Reduction            : 7.64
% 23.78/15.12  Demodulation         : 6.28
% 23.78/15.12  BG Simplification    : 0.15
% 23.78/15.12  Subsumption          : 4.21
% 23.78/15.12  Abstraction          : 0.26
% 23.78/15.12  MUC search           : 0.00
% 23.78/15.12  Cooper               : 0.00
% 23.78/15.12  Total                : 14.34
% 23.78/15.12  Index Insertion      : 0.00
% 23.78/15.12  Index Deletion       : 0.00
% 23.78/15.12  Index Matching       : 0.00
% 23.78/15.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
