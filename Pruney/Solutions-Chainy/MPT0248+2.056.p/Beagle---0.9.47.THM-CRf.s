%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:11 EST 2020

% Result     : Theorem 13.19s
% Output     : CNFRefutation 13.19s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 252 expanded)
%              Number of leaves         :   39 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 629 expanded)
%              Number of equality atoms :   78 ( 504 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_74,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_107,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_72,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_97,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_113,plain,(
    ! [A_64,B_65] : r1_tarski(A_64,k2_xboole_0(A_64,B_65)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_116,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_113])).

tff(c_716,plain,(
    ! [B_118,A_119] :
      ( k1_tarski(B_118) = A_119
      | k1_xboole_0 = A_119
      | ~ r1_tarski(A_119,k1_tarski(B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_723,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_116,c_716])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_97,c_723])).

tff(c_735,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_736,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_34,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_738,plain,(
    ! [A_18] : k5_xboole_0(A_18,'#skF_7') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_34])).

tff(c_784,plain,(
    ! [B_129,A_130] : k3_xboole_0(B_129,A_130) = k3_xboole_0(A_130,B_129) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_737,plain,(
    ! [A_17] : k3_xboole_0(A_17,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_736,c_32])).

tff(c_800,plain,(
    ! [A_130] : k3_xboole_0('#skF_7',A_130) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_737])).

tff(c_1119,plain,(
    ! [A_165,B_166] : k5_xboole_0(A_165,k3_xboole_0(A_165,B_166)) = k4_xboole_0(A_165,B_166) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1128,plain,(
    ! [A_130] : k5_xboole_0('#skF_7','#skF_7') = k4_xboole_0('#skF_7',A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_1119])).

tff(c_1140,plain,(
    ! [A_130] : k4_xboole_0('#skF_7',A_130) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_1128])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_864,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_24])).

tff(c_944,plain,(
    ! [A_143,B_144] :
      ( k2_xboole_0(A_143,B_144) = B_144
      | ~ r1_tarski(A_143,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2057,plain,(
    ! [A_5223,B_5224] :
      ( k2_xboole_0(A_5223,B_5224) = B_5224
      | k4_xboole_0(A_5223,B_5224) != '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_864,c_944])).

tff(c_2073,plain,(
    ! [A_130] : k2_xboole_0('#skF_7',A_130) = A_130 ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_2057])).

tff(c_2080,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2073,c_78])).

tff(c_2082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_735,c_2080])).

tff(c_2084,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2126,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_2084,c_76])).

tff(c_2116,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_78])).

tff(c_2083,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2627,plain,(
    ! [D_5262,B_5263,A_5264] :
      ( ~ r2_hidden(D_5262,B_5263)
      | r2_hidden(D_5262,k2_xboole_0(A_5264,B_5263)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2652,plain,(
    ! [D_5265] :
      ( ~ r2_hidden(D_5265,'#skF_8')
      | r2_hidden(D_5265,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2116,c_2627])).

tff(c_2127,plain,(
    ! [C_5229,A_5230] :
      ( C_5229 = A_5230
      | ~ r2_hidden(C_5229,k1_tarski(A_5230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2130,plain,(
    ! [C_5229] :
      ( C_5229 = '#skF_6'
      | ~ r2_hidden(C_5229,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2084,c_2127])).

tff(c_2657,plain,(
    ! [D_5266] :
      ( D_5266 = '#skF_6'
      | ~ r2_hidden(D_5266,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2652,c_2130])).

tff(c_2661,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_22,c_2657])).

tff(c_2664,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_2083,c_2661])).

tff(c_2668,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_2664,c_22])).

tff(c_2671,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2083,c_2668])).

tff(c_66069,plain,(
    ! [A_50237,B_50238,C_50239] :
      ( r2_hidden('#skF_1'(A_50237,B_50238,C_50239),B_50238)
      | r2_hidden('#skF_1'(A_50237,B_50238,C_50239),A_50237)
      | r2_hidden('#skF_2'(A_50237,B_50238,C_50239),C_50239)
      | k2_xboole_0(A_50237,B_50238) = C_50239 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66196,plain,(
    ! [A_50237,B_50238] :
      ( r2_hidden('#skF_1'(A_50237,B_50238,B_50238),A_50237)
      | r2_hidden('#skF_2'(A_50237,B_50238,B_50238),B_50238)
      | k2_xboole_0(A_50237,B_50238) = B_50238 ) ),
    inference(resolution,[status(thm)],[c_66069,c_18])).

tff(c_65919,plain,(
    ! [A_50234,B_50235,C_50236] :
      ( r2_hidden('#skF_1'(A_50234,B_50235,C_50236),B_50235)
      | r2_hidden('#skF_1'(A_50234,B_50235,C_50236),A_50234)
      | ~ r2_hidden('#skF_2'(A_50234,B_50235,C_50236),B_50235)
      | k2_xboole_0(A_50234,B_50235) = C_50236 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67268,plain,(
    ! [A_50260,B_50261] :
      ( r2_hidden('#skF_1'(A_50260,B_50261,B_50261),A_50260)
      | ~ r2_hidden('#skF_2'(A_50260,B_50261,B_50261),B_50261)
      | k2_xboole_0(A_50260,B_50261) = B_50261 ) ),
    inference(resolution,[status(thm)],[c_65919,c_10])).

tff(c_67464,plain,(
    ! [A_50267,B_50268] :
      ( r2_hidden('#skF_1'(A_50267,B_50268,B_50268),A_50267)
      | k2_xboole_0(A_50267,B_50268) = B_50268 ) ),
    inference(resolution,[status(thm)],[c_66196,c_67268])).

tff(c_67753,plain,(
    ! [B_50273] :
      ( '#skF_1'('#skF_7',B_50273,B_50273) = '#skF_6'
      | k2_xboole_0('#skF_7',B_50273) = B_50273 ) ),
    inference(resolution,[status(thm)],[c_67464,c_2130])).

tff(c_67827,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_1'('#skF_7','#skF_8','#skF_8') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_67753,c_2116])).

tff(c_67857,plain,(
    '#skF_1'('#skF_7','#skF_8','#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_2126,c_67827])).

tff(c_67885,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_8','#skF_8'),'#skF_8')
    | k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_67857,c_10])).

tff(c_67904,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7','#skF_8','#skF_8'),'#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2671,c_67885])).

tff(c_67905,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_8','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2126,c_67904])).

tff(c_67881,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | r2_hidden('#skF_2'('#skF_7','#skF_8','#skF_8'),'#skF_8')
    | k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_67857,c_18])).

tff(c_67898,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_8','#skF_8'),'#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2116,c_2671,c_67881])).

tff(c_67899,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_8','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2126,c_67898])).

tff(c_67929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67905,c_67899])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.19/5.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.19/5.41  
% 13.19/5.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.19/5.41  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 13.19/5.41  
% 13.19/5.41  %Foreground sorts:
% 13.19/5.41  
% 13.19/5.41  
% 13.19/5.41  %Background operators:
% 13.19/5.41  
% 13.19/5.41  
% 13.19/5.41  %Foreground operators:
% 13.19/5.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.19/5.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.19/5.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.19/5.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.19/5.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.19/5.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.19/5.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.19/5.41  tff('#skF_7', type, '#skF_7': $i).
% 13.19/5.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.19/5.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.19/5.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.19/5.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.19/5.41  tff('#skF_6', type, '#skF_6': $i).
% 13.19/5.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.19/5.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.19/5.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.19/5.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.19/5.41  tff('#skF_8', type, '#skF_8': $i).
% 13.19/5.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.19/5.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.19/5.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 13.19/5.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.19/5.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.19/5.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.19/5.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.19/5.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.19/5.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 13.19/5.41  
% 13.19/5.43  tff(f_108, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 13.19/5.43  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 13.19/5.43  tff(f_87, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 13.19/5.43  tff(f_58, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 13.19/5.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.19/5.43  tff(f_56, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 13.19/5.43  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.19/5.43  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.19/5.43  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.19/5.43  tff(f_44, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 13.19/5.43  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 13.19/5.43  tff(f_67, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 13.19/5.43  tff(c_74, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.19/5.43  tff(c_107, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_74])).
% 13.19/5.43  tff(c_72, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.19/5.43  tff(c_97, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_72])).
% 13.19/5.43  tff(c_78, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.19/5.43  tff(c_113, plain, (![A_64, B_65]: (r1_tarski(A_64, k2_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.19/5.43  tff(c_116, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_113])).
% 13.19/5.43  tff(c_716, plain, (![B_118, A_119]: (k1_tarski(B_118)=A_119 | k1_xboole_0=A_119 | ~r1_tarski(A_119, k1_tarski(B_118)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.19/5.43  tff(c_723, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_116, c_716])).
% 13.19/5.43  tff(c_734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_97, c_723])).
% 13.19/5.43  tff(c_735, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_74])).
% 13.19/5.43  tff(c_736, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_74])).
% 13.19/5.43  tff(c_34, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.19/5.43  tff(c_738, plain, (![A_18]: (k5_xboole_0(A_18, '#skF_7')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_736, c_34])).
% 13.19/5.43  tff(c_784, plain, (![B_129, A_130]: (k3_xboole_0(B_129, A_130)=k3_xboole_0(A_130, B_129))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.19/5.43  tff(c_32, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.19/5.43  tff(c_737, plain, (![A_17]: (k3_xboole_0(A_17, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_736, c_736, c_32])).
% 13.19/5.43  tff(c_800, plain, (![A_130]: (k3_xboole_0('#skF_7', A_130)='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_784, c_737])).
% 13.19/5.43  tff(c_1119, plain, (![A_165, B_166]: (k5_xboole_0(A_165, k3_xboole_0(A_165, B_166))=k4_xboole_0(A_165, B_166))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.19/5.43  tff(c_1128, plain, (![A_130]: (k5_xboole_0('#skF_7', '#skF_7')=k4_xboole_0('#skF_7', A_130))), inference(superposition, [status(thm), theory('equality')], [c_800, c_1119])).
% 13.19/5.43  tff(c_1140, plain, (![A_130]: (k4_xboole_0('#skF_7', A_130)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_738, c_1128])).
% 13.19/5.43  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.19/5.43  tff(c_864, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_736, c_24])).
% 13.19/5.43  tff(c_944, plain, (![A_143, B_144]: (k2_xboole_0(A_143, B_144)=B_144 | ~r1_tarski(A_143, B_144))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.19/5.43  tff(c_2057, plain, (![A_5223, B_5224]: (k2_xboole_0(A_5223, B_5224)=B_5224 | k4_xboole_0(A_5223, B_5224)!='#skF_7')), inference(resolution, [status(thm)], [c_864, c_944])).
% 13.19/5.43  tff(c_2073, plain, (![A_130]: (k2_xboole_0('#skF_7', A_130)=A_130)), inference(superposition, [status(thm), theory('equality')], [c_1140, c_2057])).
% 13.19/5.43  tff(c_2080, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2073, c_78])).
% 13.19/5.43  tff(c_2082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_735, c_2080])).
% 13.19/5.43  tff(c_2084, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_72])).
% 13.19/5.43  tff(c_76, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.19/5.43  tff(c_2126, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_2084, c_76])).
% 13.19/5.43  tff(c_2116, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_78])).
% 13.19/5.43  tff(c_2083, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_72])).
% 13.19/5.43  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.19/5.43  tff(c_2627, plain, (![D_5262, B_5263, A_5264]: (~r2_hidden(D_5262, B_5263) | r2_hidden(D_5262, k2_xboole_0(A_5264, B_5263)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.19/5.43  tff(c_2652, plain, (![D_5265]: (~r2_hidden(D_5265, '#skF_8') | r2_hidden(D_5265, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2116, c_2627])).
% 13.19/5.43  tff(c_2127, plain, (![C_5229, A_5230]: (C_5229=A_5230 | ~r2_hidden(C_5229, k1_tarski(A_5230)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.19/5.43  tff(c_2130, plain, (![C_5229]: (C_5229='#skF_6' | ~r2_hidden(C_5229, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2084, c_2127])).
% 13.19/5.43  tff(c_2657, plain, (![D_5266]: (D_5266='#skF_6' | ~r2_hidden(D_5266, '#skF_8'))), inference(resolution, [status(thm)], [c_2652, c_2130])).
% 13.19/5.43  tff(c_2661, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_22, c_2657])).
% 13.19/5.43  tff(c_2664, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_2083, c_2661])).
% 13.19/5.43  tff(c_2668, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_2664, c_22])).
% 13.19/5.43  tff(c_2671, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2083, c_2668])).
% 13.19/5.43  tff(c_66069, plain, (![A_50237, B_50238, C_50239]: (r2_hidden('#skF_1'(A_50237, B_50238, C_50239), B_50238) | r2_hidden('#skF_1'(A_50237, B_50238, C_50239), A_50237) | r2_hidden('#skF_2'(A_50237, B_50238, C_50239), C_50239) | k2_xboole_0(A_50237, B_50238)=C_50239)), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.19/5.43  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.19/5.43  tff(c_66196, plain, (![A_50237, B_50238]: (r2_hidden('#skF_1'(A_50237, B_50238, B_50238), A_50237) | r2_hidden('#skF_2'(A_50237, B_50238, B_50238), B_50238) | k2_xboole_0(A_50237, B_50238)=B_50238)), inference(resolution, [status(thm)], [c_66069, c_18])).
% 13.19/5.43  tff(c_65919, plain, (![A_50234, B_50235, C_50236]: (r2_hidden('#skF_1'(A_50234, B_50235, C_50236), B_50235) | r2_hidden('#skF_1'(A_50234, B_50235, C_50236), A_50234) | ~r2_hidden('#skF_2'(A_50234, B_50235, C_50236), B_50235) | k2_xboole_0(A_50234, B_50235)=C_50236)), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.19/5.43  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.19/5.43  tff(c_67268, plain, (![A_50260, B_50261]: (r2_hidden('#skF_1'(A_50260, B_50261, B_50261), A_50260) | ~r2_hidden('#skF_2'(A_50260, B_50261, B_50261), B_50261) | k2_xboole_0(A_50260, B_50261)=B_50261)), inference(resolution, [status(thm)], [c_65919, c_10])).
% 13.19/5.43  tff(c_67464, plain, (![A_50267, B_50268]: (r2_hidden('#skF_1'(A_50267, B_50268, B_50268), A_50267) | k2_xboole_0(A_50267, B_50268)=B_50268)), inference(resolution, [status(thm)], [c_66196, c_67268])).
% 13.19/5.43  tff(c_67753, plain, (![B_50273]: ('#skF_1'('#skF_7', B_50273, B_50273)='#skF_6' | k2_xboole_0('#skF_7', B_50273)=B_50273)), inference(resolution, [status(thm)], [c_67464, c_2130])).
% 13.19/5.43  tff(c_67827, plain, ('#skF_7'='#skF_8' | '#skF_1'('#skF_7', '#skF_8', '#skF_8')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_67753, c_2116])).
% 13.19/5.43  tff(c_67857, plain, ('#skF_1'('#skF_7', '#skF_8', '#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_2126, c_67827])).
% 13.19/5.43  tff(c_67885, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_2'('#skF_7', '#skF_8', '#skF_8'), '#skF_8') | k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_67857, c_10])).
% 13.19/5.43  tff(c_67904, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_8', '#skF_8'), '#skF_8') | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2671, c_67885])).
% 13.19/5.43  tff(c_67905, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_8', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2126, c_67904])).
% 13.19/5.43  tff(c_67881, plain, (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_2'('#skF_7', '#skF_8', '#skF_8'), '#skF_8') | k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_67857, c_18])).
% 13.19/5.43  tff(c_67898, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_8', '#skF_8'), '#skF_8') | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2116, c_2671, c_67881])).
% 13.19/5.43  tff(c_67899, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_8', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2126, c_67898])).
% 13.19/5.43  tff(c_67929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67905, c_67899])).
% 13.19/5.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.19/5.43  
% 13.19/5.43  Inference rules
% 13.19/5.43  ----------------------
% 13.19/5.43  #Ref     : 0
% 13.19/5.43  #Sup     : 10496
% 13.19/5.43  #Fact    : 23
% 13.19/5.43  #Define  : 0
% 13.19/5.43  #Split   : 23
% 13.19/5.43  #Chain   : 0
% 13.19/5.43  #Close   : 0
% 13.19/5.43  
% 13.19/5.43  Ordering : KBO
% 13.19/5.43  
% 13.19/5.43  Simplification rules
% 13.19/5.43  ----------------------
% 13.19/5.43  #Subsume      : 3351
% 13.19/5.43  #Demod        : 4671
% 13.19/5.43  #Tautology    : 2087
% 13.19/5.43  #SimpNegUnit  : 261
% 13.19/5.43  #BackRed      : 114
% 13.19/5.43  
% 13.19/5.43  #Partial instantiations: 17606
% 13.19/5.43  #Strategies tried      : 1
% 13.19/5.43  
% 13.19/5.43  Timing (in seconds)
% 13.19/5.43  ----------------------
% 13.19/5.43  Preprocessing        : 0.35
% 13.19/5.43  Parsing              : 0.18
% 13.19/5.43  CNF conversion       : 0.03
% 13.19/5.43  Main loop            : 4.31
% 13.19/5.43  Inferencing          : 1.41
% 13.19/5.43  Reduction            : 1.52
% 13.19/5.43  Demodulation         : 1.18
% 13.19/5.43  BG Simplification    : 0.16
% 13.19/5.43  Subsumption          : 0.88
% 13.19/5.43  Abstraction          : 0.25
% 13.19/5.43  MUC search           : 0.00
% 13.19/5.43  Cooper               : 0.00
% 13.19/5.43  Total                : 4.70
% 13.19/5.43  Index Insertion      : 0.00
% 13.19/5.43  Index Deletion       : 0.00
% 13.19/5.43  Index Matching       : 0.00
% 13.19/5.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
