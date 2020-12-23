%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:22 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 107 expanded)
%              Number of leaves         :   34 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 218 expanded)
%              Number of equality atoms :   40 ( 155 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_80,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_78,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_110,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_84,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_24,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_114,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_24])).

tff(c_742,plain,(
    ! [B_157,A_158] :
      ( k1_tarski(B_157) = A_158
      | k1_xboole_0 = A_158
      | ~ r1_tarski(A_158,k1_tarski(B_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_753,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_114,c_742])).

tff(c_761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_110,c_753])).

tff(c_762,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_763,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_82,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_803,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_763,c_82])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_66,B_67] :
      ( r1_xboole_0(k1_tarski(A_66),B_67)
      | r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_770,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_84])).

tff(c_1410,plain,(
    ! [A_229,C_230,B_231] :
      ( r1_xboole_0(A_229,C_230)
      | ~ r1_xboole_0(A_229,k2_xboole_0(B_231,C_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1431,plain,(
    ! [A_232] :
      ( r1_xboole_0(A_232,'#skF_8')
      | ~ r1_xboole_0(A_232,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_1410])).

tff(c_1452,plain,(
    ! [A_236] :
      ( r1_xboole_0(k1_tarski(A_236),'#skF_8')
      | r2_hidden(A_236,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_1431])).

tff(c_58,plain,(
    ! [A_64,B_65] :
      ( ~ r2_hidden(A_64,B_65)
      | ~ r1_xboole_0(k1_tarski(A_64),B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1464,plain,(
    ! [A_237] :
      ( ~ r2_hidden(A_237,'#skF_8')
      | r2_hidden(A_237,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1452,c_58])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1483,plain,(
    ! [A_239] :
      ( r1_tarski(A_239,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_239,'#skF_7'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1464,c_4])).

tff(c_1488,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_1483])).

tff(c_1801,plain,(
    ! [B_259,A_260] :
      ( k1_tarski(B_259) = A_260
      | k1_xboole_0 = A_260
      | ~ r1_tarski(A_260,k1_tarski(B_259)) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1812,plain,(
    ! [A_260] :
      ( k1_tarski('#skF_6') = A_260
      | k1_xboole_0 = A_260
      | ~ r1_tarski(A_260,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_1801])).

tff(c_1818,plain,(
    ! [A_261] :
      ( A_261 = '#skF_7'
      | k1_xboole_0 = A_261
      | ~ r1_tarski(A_261,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_763,c_1812])).

tff(c_1821,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1488,c_1818])).

tff(c_1833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_803,c_1821])).

tff(c_1834,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_2143,plain,(
    ! [A_313,B_314] :
      ( r2_hidden('#skF_1'(A_313,B_314),A_313)
      | r1_tarski(A_313,B_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1835,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_12,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1837,plain,(
    ! [A_10] : r1_xboole_0(A_10,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1835,c_12])).

tff(c_1956,plain,(
    ! [A_280,B_281] :
      ( ~ r2_hidden(A_280,B_281)
      | ~ r1_xboole_0(k1_tarski(A_280),B_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1961,plain,(
    ! [A_280] : ~ r2_hidden(A_280,'#skF_7') ),
    inference(resolution,[status(thm)],[c_1837,c_1956])).

tff(c_2150,plain,(
    ! [B_315] : r1_tarski('#skF_7',B_315) ),
    inference(resolution,[status(thm)],[c_2143,c_1961])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2154,plain,(
    ! [B_315] : k2_xboole_0('#skF_7',B_315) = B_315 ),
    inference(resolution,[status(thm)],[c_2150,c_10])).

tff(c_2156,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_84])).

tff(c_2158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1834,c_2156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:51:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.69  
% 3.63/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 3.63/1.69  
% 3.63/1.69  %Foreground sorts:
% 3.63/1.69  
% 3.63/1.69  
% 3.63/1.69  %Background operators:
% 3.63/1.69  
% 3.63/1.69  
% 3.63/1.69  %Foreground operators:
% 3.63/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.63/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.63/1.69  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.63/1.69  tff('#skF_7', type, '#skF_7': $i).
% 3.63/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.63/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.63/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.63/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.63/1.69  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.63/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.63/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.63/1.69  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.63/1.69  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.63/1.69  tff('#skF_8', type, '#skF_8': $i).
% 3.63/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.63/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.63/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.63/1.69  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.63/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.63/1.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.63/1.69  
% 3.63/1.70  tff(f_140, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.63/1.70  tff(f_72, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.63/1.70  tff(f_121, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.63/1.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.63/1.70  tff(f_106, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.63/1.70  tff(f_70, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.63/1.70  tff(f_101, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.63/1.70  tff(f_42, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.63/1.70  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.63/1.70  tff(c_80, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.63/1.70  tff(c_92, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_80])).
% 3.63/1.70  tff(c_78, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.63/1.70  tff(c_110, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_78])).
% 3.63/1.70  tff(c_84, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.63/1.70  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.63/1.70  tff(c_114, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_24])).
% 3.63/1.70  tff(c_742, plain, (![B_157, A_158]: (k1_tarski(B_157)=A_158 | k1_xboole_0=A_158 | ~r1_tarski(A_158, k1_tarski(B_157)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.63/1.70  tff(c_753, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_114, c_742])).
% 3.63/1.70  tff(c_761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_110, c_753])).
% 3.63/1.70  tff(c_762, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_78])).
% 3.63/1.70  tff(c_763, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_78])).
% 3.63/1.70  tff(c_82, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.63/1.70  tff(c_803, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_763, c_763, c_82])).
% 3.63/1.70  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.63/1.70  tff(c_60, plain, (![A_66, B_67]: (r1_xboole_0(k1_tarski(A_66), B_67) | r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.63/1.70  tff(c_770, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_763, c_84])).
% 3.63/1.70  tff(c_1410, plain, (![A_229, C_230, B_231]: (r1_xboole_0(A_229, C_230) | ~r1_xboole_0(A_229, k2_xboole_0(B_231, C_230)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.63/1.70  tff(c_1431, plain, (![A_232]: (r1_xboole_0(A_232, '#skF_8') | ~r1_xboole_0(A_232, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_770, c_1410])).
% 3.63/1.70  tff(c_1452, plain, (![A_236]: (r1_xboole_0(k1_tarski(A_236), '#skF_8') | r2_hidden(A_236, '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_1431])).
% 3.63/1.70  tff(c_58, plain, (![A_64, B_65]: (~r2_hidden(A_64, B_65) | ~r1_xboole_0(k1_tarski(A_64), B_65))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.63/1.70  tff(c_1464, plain, (![A_237]: (~r2_hidden(A_237, '#skF_8') | r2_hidden(A_237, '#skF_7'))), inference(resolution, [status(thm)], [c_1452, c_58])).
% 3.63/1.70  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.63/1.70  tff(c_1483, plain, (![A_239]: (r1_tarski(A_239, '#skF_7') | ~r2_hidden('#skF_1'(A_239, '#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_1464, c_4])).
% 3.63/1.70  tff(c_1488, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_1483])).
% 3.63/1.70  tff(c_1801, plain, (![B_259, A_260]: (k1_tarski(B_259)=A_260 | k1_xboole_0=A_260 | ~r1_tarski(A_260, k1_tarski(B_259)))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.63/1.70  tff(c_1812, plain, (![A_260]: (k1_tarski('#skF_6')=A_260 | k1_xboole_0=A_260 | ~r1_tarski(A_260, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_763, c_1801])).
% 3.63/1.70  tff(c_1818, plain, (![A_261]: (A_261='#skF_7' | k1_xboole_0=A_261 | ~r1_tarski(A_261, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_763, c_1812])).
% 3.63/1.70  tff(c_1821, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1488, c_1818])).
% 3.63/1.70  tff(c_1833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_762, c_803, c_1821])).
% 3.63/1.70  tff(c_1834, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_80])).
% 3.63/1.70  tff(c_2143, plain, (![A_313, B_314]: (r2_hidden('#skF_1'(A_313, B_314), A_313) | r1_tarski(A_313, B_314))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.63/1.70  tff(c_1835, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 3.63/1.70  tff(c_12, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.63/1.70  tff(c_1837, plain, (![A_10]: (r1_xboole_0(A_10, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1835, c_12])).
% 3.63/1.70  tff(c_1956, plain, (![A_280, B_281]: (~r2_hidden(A_280, B_281) | ~r1_xboole_0(k1_tarski(A_280), B_281))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.63/1.70  tff(c_1961, plain, (![A_280]: (~r2_hidden(A_280, '#skF_7'))), inference(resolution, [status(thm)], [c_1837, c_1956])).
% 3.63/1.70  tff(c_2150, plain, (![B_315]: (r1_tarski('#skF_7', B_315))), inference(resolution, [status(thm)], [c_2143, c_1961])).
% 3.63/1.70  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.63/1.70  tff(c_2154, plain, (![B_315]: (k2_xboole_0('#skF_7', B_315)=B_315)), inference(resolution, [status(thm)], [c_2150, c_10])).
% 3.63/1.70  tff(c_2156, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_84])).
% 3.63/1.70  tff(c_2158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1834, c_2156])).
% 3.63/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.63/1.70  
% 3.63/1.70  Inference rules
% 3.63/1.70  ----------------------
% 3.63/1.70  #Ref     : 0
% 3.63/1.70  #Sup     : 467
% 3.63/1.70  #Fact    : 0
% 3.63/1.70  #Define  : 0
% 3.63/1.70  #Split   : 3
% 3.63/1.70  #Chain   : 0
% 3.63/1.70  #Close   : 0
% 3.63/1.70  
% 3.63/1.70  Ordering : KBO
% 3.63/1.70  
% 3.63/1.70  Simplification rules
% 3.63/1.70  ----------------------
% 3.63/1.70  #Subsume      : 59
% 3.63/1.70  #Demod        : 229
% 3.63/1.70  #Tautology    : 288
% 3.63/1.70  #SimpNegUnit  : 6
% 3.63/1.70  #BackRed      : 11
% 3.63/1.70  
% 3.63/1.70  #Partial instantiations: 0
% 3.63/1.70  #Strategies tried      : 1
% 3.63/1.70  
% 3.63/1.70  Timing (in seconds)
% 3.63/1.70  ----------------------
% 3.63/1.71  Preprocessing        : 0.37
% 3.63/1.71  Parsing              : 0.20
% 3.63/1.71  CNF conversion       : 0.03
% 3.63/1.71  Main loop            : 0.49
% 3.63/1.71  Inferencing          : 0.18
% 3.63/1.71  Reduction            : 0.16
% 3.63/1.71  Demodulation         : 0.12
% 3.63/1.71  BG Simplification    : 0.03
% 3.63/1.71  Subsumption          : 0.08
% 3.63/1.71  Abstraction          : 0.02
% 3.63/1.71  MUC search           : 0.00
% 3.63/1.71  Cooper               : 0.00
% 3.63/1.71  Total                : 0.90
% 3.63/1.71  Index Insertion      : 0.00
% 3.63/1.71  Index Deletion       : 0.00
% 3.63/1.71  Index Matching       : 0.00
% 3.63/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
