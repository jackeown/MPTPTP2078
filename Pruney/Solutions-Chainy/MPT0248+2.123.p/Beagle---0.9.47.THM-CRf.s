%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:21 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 113 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 236 expanded)
%              Number of equality atoms :   39 ( 173 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_60,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_66,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_28,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_74,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_28])).

tff(c_839,plain,(
    ! [B_145,A_146] :
      ( k1_tarski(B_145) = A_146
      | k1_xboole_0 = A_146
      | ~ r1_tarski(A_146,k1_tarski(B_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_866,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_74,c_839])).

tff(c_878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_866])).

tff(c_879,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_880,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_883,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_12])).

tff(c_1186,plain,(
    ! [A_191,B_192] :
      ( r2_hidden('#skF_2'(A_191,B_192),A_191)
      | r1_tarski(A_191,B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1191,plain,(
    ! [A_193,B_194] :
      ( ~ v1_xboole_0(A_193)
      | r1_tarski(A_193,B_194) ) ),
    inference(resolution,[status(thm)],[c_1186,c_2])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1235,plain,(
    ! [A_197,B_198] :
      ( k2_xboole_0(A_197,B_198) = B_198
      | ~ v1_xboole_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_1191,c_16])).

tff(c_1238,plain,(
    ! [B_198] : k2_xboole_0('#skF_4',B_198) = B_198 ),
    inference(resolution,[status(thm)],[c_883,c_1235])).

tff(c_1240,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_64])).

tff(c_1242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_879,c_1240])).

tff(c_1244,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1290,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1244,c_62])).

tff(c_1273,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_64])).

tff(c_1442,plain,(
    ! [A_225,B_226] :
      ( r1_xboole_0(k1_tarski(A_225),B_226)
      | r2_hidden(A_225,B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1493,plain,(
    ! [B_232] :
      ( r1_xboole_0('#skF_4',B_232)
      | r2_hidden('#skF_3',B_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1244,c_1442])).

tff(c_1301,plain,(
    ! [A_209,B_210] :
      ( r1_tarski(k1_tarski(A_209),B_210)
      | ~ r2_hidden(A_209,B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1304,plain,(
    ! [B_210] :
      ( r1_tarski('#skF_4',B_210)
      | ~ r2_hidden('#skF_3',B_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1244,c_1301])).

tff(c_1541,plain,(
    ! [B_237] :
      ( r1_tarski('#skF_4',B_237)
      | r1_xboole_0('#skF_4',B_237) ) ),
    inference(resolution,[status(thm)],[c_1493,c_1304])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_xboole_0(B_11,A_10)
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1548,plain,(
    ! [B_237] :
      ( r1_xboole_0(B_237,'#skF_4')
      | r1_tarski('#skF_4',B_237) ) ),
    inference(resolution,[status(thm)],[c_1541,c_14])).

tff(c_1243,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1698,plain,(
    ! [A_246,C_247,B_248] :
      ( r1_xboole_0(A_246,C_247)
      | ~ r1_xboole_0(A_246,k2_xboole_0(B_248,C_247)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1738,plain,(
    ! [A_249] :
      ( r1_xboole_0(A_249,'#skF_5')
      | ~ r1_xboole_0(A_249,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1273,c_1698])).

tff(c_20,plain,(
    ! [A_14] :
      ( ~ r1_xboole_0(A_14,A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1744,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1738,c_20])).

tff(c_1748,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1243,c_1744])).

tff(c_1755,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1548,c_1748])).

tff(c_1759,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1755,c_16])).

tff(c_1764,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_1759])).

tff(c_1766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1290,c_1764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.58  
% 3.38/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.38/1.58  
% 3.38/1.58  %Foreground sorts:
% 3.38/1.58  
% 3.38/1.58  
% 3.38/1.58  %Background operators:
% 3.38/1.58  
% 3.38/1.58  
% 3.38/1.58  %Foreground operators:
% 3.38/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.38/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.38/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.38/1.58  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.58  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.38/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.38/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.58  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.38/1.58  
% 3.38/1.60  tff(f_127, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.38/1.60  tff(f_77, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.38/1.60  tff(f_106, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.38/1.60  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.38/1.60  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.38/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.38/1.60  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.38/1.60  tff(f_100, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.38/1.60  tff(f_95, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.38/1.60  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.38/1.60  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.38/1.60  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.38/1.60  tff(c_60, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.38/1.60  tff(c_70, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 3.38/1.60  tff(c_58, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.38/1.60  tff(c_66, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_58])).
% 3.38/1.60  tff(c_64, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.38/1.60  tff(c_28, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.38/1.60  tff(c_74, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_28])).
% 3.38/1.60  tff(c_839, plain, (![B_145, A_146]: (k1_tarski(B_145)=A_146 | k1_xboole_0=A_146 | ~r1_tarski(A_146, k1_tarski(B_145)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.38/1.60  tff(c_866, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_74, c_839])).
% 3.38/1.60  tff(c_878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_866])).
% 3.38/1.60  tff(c_879, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 3.38/1.60  tff(c_880, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 3.38/1.60  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.38/1.60  tff(c_883, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_880, c_12])).
% 3.38/1.60  tff(c_1186, plain, (![A_191, B_192]: (r2_hidden('#skF_2'(A_191, B_192), A_191) | r1_tarski(A_191, B_192))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.60  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.60  tff(c_1191, plain, (![A_193, B_194]: (~v1_xboole_0(A_193) | r1_tarski(A_193, B_194))), inference(resolution, [status(thm)], [c_1186, c_2])).
% 3.38/1.60  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.38/1.60  tff(c_1235, plain, (![A_197, B_198]: (k2_xboole_0(A_197, B_198)=B_198 | ~v1_xboole_0(A_197))), inference(resolution, [status(thm)], [c_1191, c_16])).
% 3.38/1.60  tff(c_1238, plain, (![B_198]: (k2_xboole_0('#skF_4', B_198)=B_198)), inference(resolution, [status(thm)], [c_883, c_1235])).
% 3.38/1.60  tff(c_1240, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_64])).
% 3.38/1.60  tff(c_1242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_879, c_1240])).
% 3.38/1.60  tff(c_1244, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 3.38/1.60  tff(c_62, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.38/1.60  tff(c_1290, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1244, c_1244, c_62])).
% 3.38/1.60  tff(c_1273, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1244, c_64])).
% 3.38/1.60  tff(c_1442, plain, (![A_225, B_226]: (r1_xboole_0(k1_tarski(A_225), B_226) | r2_hidden(A_225, B_226))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.38/1.60  tff(c_1493, plain, (![B_232]: (r1_xboole_0('#skF_4', B_232) | r2_hidden('#skF_3', B_232))), inference(superposition, [status(thm), theory('equality')], [c_1244, c_1442])).
% 3.38/1.60  tff(c_1301, plain, (![A_209, B_210]: (r1_tarski(k1_tarski(A_209), B_210) | ~r2_hidden(A_209, B_210))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.38/1.60  tff(c_1304, plain, (![B_210]: (r1_tarski('#skF_4', B_210) | ~r2_hidden('#skF_3', B_210))), inference(superposition, [status(thm), theory('equality')], [c_1244, c_1301])).
% 3.38/1.60  tff(c_1541, plain, (![B_237]: (r1_tarski('#skF_4', B_237) | r1_xboole_0('#skF_4', B_237))), inference(resolution, [status(thm)], [c_1493, c_1304])).
% 3.38/1.60  tff(c_14, plain, (![B_11, A_10]: (r1_xboole_0(B_11, A_10) | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.38/1.60  tff(c_1548, plain, (![B_237]: (r1_xboole_0(B_237, '#skF_4') | r1_tarski('#skF_4', B_237))), inference(resolution, [status(thm)], [c_1541, c_14])).
% 3.38/1.60  tff(c_1243, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_58])).
% 3.38/1.60  tff(c_1698, plain, (![A_246, C_247, B_248]: (r1_xboole_0(A_246, C_247) | ~r1_xboole_0(A_246, k2_xboole_0(B_248, C_247)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.38/1.60  tff(c_1738, plain, (![A_249]: (r1_xboole_0(A_249, '#skF_5') | ~r1_xboole_0(A_249, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1273, c_1698])).
% 3.38/1.60  tff(c_20, plain, (![A_14]: (~r1_xboole_0(A_14, A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.38/1.60  tff(c_1744, plain, (k1_xboole_0='#skF_5' | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1738, c_20])).
% 3.38/1.60  tff(c_1748, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1243, c_1744])).
% 3.38/1.60  tff(c_1755, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1548, c_1748])).
% 3.38/1.60  tff(c_1759, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_1755, c_16])).
% 3.38/1.60  tff(c_1764, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1273, c_1759])).
% 3.38/1.60  tff(c_1766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1290, c_1764])).
% 3.38/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.60  
% 3.38/1.60  Inference rules
% 3.38/1.60  ----------------------
% 3.38/1.60  #Ref     : 0
% 3.38/1.60  #Sup     : 383
% 3.38/1.60  #Fact    : 0
% 3.38/1.60  #Define  : 0
% 3.38/1.60  #Split   : 7
% 3.38/1.60  #Chain   : 0
% 3.38/1.60  #Close   : 0
% 3.38/1.60  
% 3.38/1.60  Ordering : KBO
% 3.38/1.60  
% 3.38/1.60  Simplification rules
% 3.38/1.60  ----------------------
% 3.38/1.60  #Subsume      : 93
% 3.38/1.60  #Demod        : 104
% 3.38/1.60  #Tautology    : 170
% 3.38/1.60  #SimpNegUnit  : 14
% 3.38/1.60  #BackRed      : 12
% 3.38/1.60  
% 3.38/1.60  #Partial instantiations: 0
% 3.38/1.60  #Strategies tried      : 1
% 3.38/1.60  
% 3.38/1.60  Timing (in seconds)
% 3.38/1.60  ----------------------
% 3.38/1.60  Preprocessing        : 0.35
% 3.38/1.60  Parsing              : 0.19
% 3.38/1.60  CNF conversion       : 0.02
% 3.38/1.60  Main loop            : 0.48
% 3.38/1.60  Inferencing          : 0.18
% 3.38/1.60  Reduction            : 0.14
% 3.38/1.60  Demodulation         : 0.10
% 3.38/1.60  BG Simplification    : 0.02
% 3.38/1.60  Subsumption          : 0.08
% 3.38/1.60  Abstraction          : 0.02
% 3.38/1.60  MUC search           : 0.00
% 3.38/1.60  Cooper               : 0.00
% 3.38/1.60  Total                : 0.86
% 3.38/1.60  Index Insertion      : 0.00
% 3.38/1.60  Index Deletion       : 0.00
% 3.38/1.60  Index Matching       : 0.00
% 3.38/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
