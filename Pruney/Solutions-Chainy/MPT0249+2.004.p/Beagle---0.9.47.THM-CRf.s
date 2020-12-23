%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:24 EST 2020

% Result     : Theorem 18.71s
% Output     : CNFRefutation 18.71s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 211 expanded)
%              Number of leaves         :   36 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :  132 ( 367 expanded)
%              Number of equality atoms :   65 ( 207 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_80,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_72,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k1_tarski(A_60),B_61)
      | ~ r2_hidden(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_82,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_130,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,A_77) = k2_xboole_0(A_77,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_169,plain,(
    ! [A_78,B_79] : r1_tarski(A_78,k2_xboole_0(B_79,A_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_24])).

tff(c_178,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_169])).

tff(c_291,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_308,plain,
    ( k1_tarski('#skF_5') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_178,c_291])).

tff(c_359,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_367,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_359])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_446,plain,(
    ! [C_119,B_120,A_121] :
      ( r2_hidden(C_119,B_120)
      | ~ r2_hidden(C_119,A_121)
      | ~ r1_tarski(A_121,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5597,plain,(
    ! [A_298,B_299] :
      ( r2_hidden('#skF_2'(A_298),B_299)
      | ~ r1_tarski(A_298,B_299)
      | k1_xboole_0 = A_298 ) ),
    inference(resolution,[status(thm)],[c_10,c_446])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28873,plain,(
    ! [A_541,B_542,B_543] :
      ( r2_hidden('#skF_2'(A_541),B_542)
      | ~ r1_tarski(B_543,B_542)
      | ~ r1_tarski(A_541,B_543)
      | k1_xboole_0 = A_541 ) ),
    inference(resolution,[status(thm)],[c_5597,c_4])).

tff(c_28934,plain,(
    ! [A_544] :
      ( r2_hidden('#skF_2'(A_544),k1_tarski('#skF_5'))
      | ~ r1_tarski(A_544,'#skF_7')
      | k1_xboole_0 = A_544 ) ),
    inference(resolution,[status(thm)],[c_178,c_28873])).

tff(c_56,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_58,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1536,plain,(
    ! [E_171,C_172,B_173,A_174] :
      ( E_171 = C_172
      | E_171 = B_173
      | E_171 = A_174
      | ~ r2_hidden(E_171,k1_enumset1(A_174,B_173,C_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8511,plain,(
    ! [E_356,B_357,A_358] :
      ( E_356 = B_357
      | E_356 = A_358
      | E_356 = A_358
      | ~ r2_hidden(E_356,k2_tarski(A_358,B_357)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1536])).

tff(c_8540,plain,(
    ! [E_356,A_32] :
      ( E_356 = A_32
      | E_356 = A_32
      | E_356 = A_32
      | ~ r2_hidden(E_356,k1_tarski(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_8511])).

tff(c_28957,plain,(
    ! [A_545] :
      ( '#skF_2'(A_545) = '#skF_5'
      | ~ r1_tarski(A_545,'#skF_7')
      | k1_xboole_0 = A_545 ) ),
    inference(resolution,[status(thm)],[c_28934,c_8540])).

tff(c_28969,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_16,c_28957])).

tff(c_28974,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_28969])).

tff(c_28984,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_28974,c_10])).

tff(c_28992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_367,c_28984])).

tff(c_28993,plain,(
    k1_tarski('#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_124,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_24])).

tff(c_28996,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28993,c_124])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_29029,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_28996,c_12])).

tff(c_29032,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_29029])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_29828,plain,(
    ! [E_602,C_603,B_604,A_605] :
      ( E_602 = C_603
      | E_602 = B_604
      | E_602 = A_605
      | ~ r2_hidden(E_602,k1_enumset1(A_605,B_604,C_603)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_35708,plain,(
    ! [E_820,B_821,A_822] :
      ( E_820 = B_821
      | E_820 = A_822
      | E_820 = A_822
      | ~ r2_hidden(E_820,k2_tarski(A_822,B_821)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_29828])).

tff(c_51328,plain,(
    ! [E_1016,A_1017] :
      ( E_1016 = A_1017
      | E_1016 = A_1017
      | E_1016 = A_1017
      | ~ r2_hidden(E_1016,k1_tarski(A_1017)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_35708])).

tff(c_51413,plain,(
    ! [E_1019] :
      ( E_1019 = '#skF_5'
      | E_1019 = '#skF_5'
      | E_1019 = '#skF_5'
      | ~ r2_hidden(E_1019,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28993,c_51328])).

tff(c_51464,plain,(
    ! [B_1020] :
      ( '#skF_1'('#skF_7',B_1020) = '#skF_5'
      | r1_tarski('#skF_7',B_1020) ) ),
    inference(resolution,[status(thm)],[c_8,c_51413])).

tff(c_51504,plain,(
    '#skF_1'('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_51464,c_29032])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_51512,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_51504,c_6])).

tff(c_51519,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_29032,c_51512])).

tff(c_29307,plain,(
    ! [C_572,B_573,A_574] :
      ( r2_hidden(C_572,B_573)
      | ~ r2_hidden(C_572,A_574)
      | ~ r1_tarski(A_574,B_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_29349,plain,(
    ! [A_8,B_573] :
      ( r2_hidden('#skF_2'(A_8),B_573)
      | ~ r1_tarski(A_8,B_573)
      | k1_xboole_0 = A_8 ) ),
    inference(resolution,[status(thm)],[c_10,c_29307])).

tff(c_51893,plain,(
    ! [A_1025] :
      ( '#skF_2'(A_1025) = '#skF_5'
      | ~ r1_tarski(A_1025,'#skF_7')
      | k1_xboole_0 = A_1025 ) ),
    inference(resolution,[status(thm)],[c_29349,c_51413])).

tff(c_51910,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_28996,c_51893])).

tff(c_51928,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_51910])).

tff(c_51939,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_51928,c_10])).

tff(c_51944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_51519,c_51939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.71/10.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.71/10.46  
% 18.71/10.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.71/10.46  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 18.71/10.46  
% 18.71/10.46  %Foreground sorts:
% 18.71/10.46  
% 18.71/10.46  
% 18.71/10.46  %Background operators:
% 18.71/10.46  
% 18.71/10.46  
% 18.71/10.46  %Foreground operators:
% 18.71/10.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 18.71/10.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.71/10.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.71/10.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.71/10.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.71/10.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.71/10.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.71/10.46  tff('#skF_7', type, '#skF_7': $i).
% 18.71/10.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.71/10.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.71/10.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.71/10.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.71/10.46  tff('#skF_5', type, '#skF_5': $i).
% 18.71/10.46  tff('#skF_6', type, '#skF_6': $i).
% 18.71/10.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.71/10.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.71/10.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 18.71/10.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.71/10.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.71/10.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.71/10.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.71/10.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.71/10.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 18.71/10.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.71/10.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.71/10.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.71/10.46  
% 18.71/10.48  tff(f_110, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 18.71/10.48  tff(f_95, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 18.71/10.48  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 18.71/10.48  tff(f_56, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.71/10.48  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.71/10.48  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 18.71/10.48  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 18.71/10.48  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 18.71/10.48  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 18.71/10.48  tff(f_77, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 18.71/10.48  tff(c_78, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.71/10.48  tff(c_80, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.71/10.48  tff(c_76, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.71/10.48  tff(c_72, plain, (![A_60, B_61]: (r1_tarski(k1_tarski(A_60), B_61) | ~r2_hidden(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.71/10.48  tff(c_82, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 18.71/10.48  tff(c_130, plain, (![B_76, A_77]: (k2_xboole_0(B_76, A_77)=k2_xboole_0(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.71/10.48  tff(c_24, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.71/10.48  tff(c_169, plain, (![A_78, B_79]: (r1_tarski(A_78, k2_xboole_0(B_79, A_78)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_24])).
% 18.71/10.48  tff(c_178, plain, (r1_tarski('#skF_7', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_169])).
% 18.71/10.48  tff(c_291, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.71/10.48  tff(c_308, plain, (k1_tarski('#skF_5')='#skF_7' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_178, c_291])).
% 18.71/10.48  tff(c_359, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_308])).
% 18.71/10.48  tff(c_367, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_72, c_359])).
% 18.71/10.48  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.71/10.48  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 18.71/10.48  tff(c_446, plain, (![C_119, B_120, A_121]: (r2_hidden(C_119, B_120) | ~r2_hidden(C_119, A_121) | ~r1_tarski(A_121, B_120))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.71/10.48  tff(c_5597, plain, (![A_298, B_299]: (r2_hidden('#skF_2'(A_298), B_299) | ~r1_tarski(A_298, B_299) | k1_xboole_0=A_298)), inference(resolution, [status(thm)], [c_10, c_446])).
% 18.71/10.48  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.71/10.48  tff(c_28873, plain, (![A_541, B_542, B_543]: (r2_hidden('#skF_2'(A_541), B_542) | ~r1_tarski(B_543, B_542) | ~r1_tarski(A_541, B_543) | k1_xboole_0=A_541)), inference(resolution, [status(thm)], [c_5597, c_4])).
% 18.71/10.48  tff(c_28934, plain, (![A_544]: (r2_hidden('#skF_2'(A_544), k1_tarski('#skF_5')) | ~r1_tarski(A_544, '#skF_7') | k1_xboole_0=A_544)), inference(resolution, [status(thm)], [c_178, c_28873])).
% 18.71/10.48  tff(c_56, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_79])).
% 18.71/10.48  tff(c_58, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.71/10.48  tff(c_1536, plain, (![E_171, C_172, B_173, A_174]: (E_171=C_172 | E_171=B_173 | E_171=A_174 | ~r2_hidden(E_171, k1_enumset1(A_174, B_173, C_172)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.71/10.48  tff(c_8511, plain, (![E_356, B_357, A_358]: (E_356=B_357 | E_356=A_358 | E_356=A_358 | ~r2_hidden(E_356, k2_tarski(A_358, B_357)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1536])).
% 18.71/10.48  tff(c_8540, plain, (![E_356, A_32]: (E_356=A_32 | E_356=A_32 | E_356=A_32 | ~r2_hidden(E_356, k1_tarski(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_8511])).
% 18.71/10.48  tff(c_28957, plain, (![A_545]: ('#skF_2'(A_545)='#skF_5' | ~r1_tarski(A_545, '#skF_7') | k1_xboole_0=A_545)), inference(resolution, [status(thm)], [c_28934, c_8540])).
% 18.71/10.48  tff(c_28969, plain, ('#skF_2'('#skF_7')='#skF_5' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_16, c_28957])).
% 18.71/10.48  tff(c_28974, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_76, c_28969])).
% 18.71/10.48  tff(c_28984, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_28974, c_10])).
% 18.71/10.48  tff(c_28992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_367, c_28984])).
% 18.71/10.48  tff(c_28993, plain, (k1_tarski('#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_308])).
% 18.71/10.48  tff(c_124, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_24])).
% 18.71/10.48  tff(c_28996, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28993, c_124])).
% 18.71/10.48  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.71/10.48  tff(c_29029, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_28996, c_12])).
% 18.71/10.48  tff(c_29032, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_80, c_29029])).
% 18.71/10.48  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.71/10.48  tff(c_29828, plain, (![E_602, C_603, B_604, A_605]: (E_602=C_603 | E_602=B_604 | E_602=A_605 | ~r2_hidden(E_602, k1_enumset1(A_605, B_604, C_603)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.71/10.48  tff(c_35708, plain, (![E_820, B_821, A_822]: (E_820=B_821 | E_820=A_822 | E_820=A_822 | ~r2_hidden(E_820, k2_tarski(A_822, B_821)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_29828])).
% 18.71/10.48  tff(c_51328, plain, (![E_1016, A_1017]: (E_1016=A_1017 | E_1016=A_1017 | E_1016=A_1017 | ~r2_hidden(E_1016, k1_tarski(A_1017)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_35708])).
% 18.71/10.48  tff(c_51413, plain, (![E_1019]: (E_1019='#skF_5' | E_1019='#skF_5' | E_1019='#skF_5' | ~r2_hidden(E_1019, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_28993, c_51328])).
% 18.71/10.48  tff(c_51464, plain, (![B_1020]: ('#skF_1'('#skF_7', B_1020)='#skF_5' | r1_tarski('#skF_7', B_1020))), inference(resolution, [status(thm)], [c_8, c_51413])).
% 18.71/10.48  tff(c_51504, plain, ('#skF_1'('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_51464, c_29032])).
% 18.71/10.48  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.71/10.48  tff(c_51512, plain, (~r2_hidden('#skF_5', '#skF_6') | r1_tarski('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_51504, c_6])).
% 18.71/10.48  tff(c_51519, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_29032, c_51512])).
% 18.71/10.48  tff(c_29307, plain, (![C_572, B_573, A_574]: (r2_hidden(C_572, B_573) | ~r2_hidden(C_572, A_574) | ~r1_tarski(A_574, B_573))), inference(cnfTransformation, [status(thm)], [f_34])).
% 18.71/10.48  tff(c_29349, plain, (![A_8, B_573]: (r2_hidden('#skF_2'(A_8), B_573) | ~r1_tarski(A_8, B_573) | k1_xboole_0=A_8)), inference(resolution, [status(thm)], [c_10, c_29307])).
% 18.71/10.48  tff(c_51893, plain, (![A_1025]: ('#skF_2'(A_1025)='#skF_5' | ~r1_tarski(A_1025, '#skF_7') | k1_xboole_0=A_1025)), inference(resolution, [status(thm)], [c_29349, c_51413])).
% 18.71/10.48  tff(c_51910, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_28996, c_51893])).
% 18.71/10.48  tff(c_51928, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_78, c_51910])).
% 18.71/10.48  tff(c_51939, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_51928, c_10])).
% 18.71/10.48  tff(c_51944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_51519, c_51939])).
% 18.71/10.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.71/10.48  
% 18.71/10.48  Inference rules
% 18.71/10.48  ----------------------
% 18.71/10.48  #Ref     : 0
% 18.71/10.48  #Sup     : 12560
% 18.71/10.48  #Fact    : 24
% 18.71/10.48  #Define  : 0
% 18.71/10.48  #Split   : 8
% 18.71/10.48  #Chain   : 0
% 18.71/10.48  #Close   : 0
% 18.71/10.48  
% 18.71/10.48  Ordering : KBO
% 18.71/10.48  
% 18.71/10.48  Simplification rules
% 18.71/10.48  ----------------------
% 18.71/10.48  #Subsume      : 664
% 18.71/10.48  #Demod        : 17412
% 18.71/10.48  #Tautology    : 6748
% 18.71/10.48  #SimpNegUnit  : 33
% 18.71/10.48  #BackRed      : 28
% 18.71/10.48  
% 18.71/10.48  #Partial instantiations: 0
% 18.71/10.48  #Strategies tried      : 1
% 18.71/10.48  
% 18.71/10.48  Timing (in seconds)
% 18.71/10.48  ----------------------
% 18.71/10.48  Preprocessing        : 0.37
% 18.71/10.48  Parsing              : 0.19
% 18.71/10.48  CNF conversion       : 0.03
% 18.71/10.48  Main loop            : 9.30
% 18.71/10.48  Inferencing          : 1.43
% 18.71/10.48  Reduction            : 5.88
% 18.71/10.48  Demodulation         : 5.28
% 18.71/10.48  BG Simplification    : 0.17
% 18.71/10.48  Subsumption          : 1.45
% 18.71/10.48  Abstraction          : 0.28
% 18.71/10.48  MUC search           : 0.00
% 18.71/10.48  Cooper               : 0.00
% 18.71/10.48  Total                : 9.70
% 18.71/10.48  Index Insertion      : 0.00
% 18.71/10.48  Index Deletion       : 0.00
% 18.71/10.48  Index Matching       : 0.00
% 18.71/10.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
