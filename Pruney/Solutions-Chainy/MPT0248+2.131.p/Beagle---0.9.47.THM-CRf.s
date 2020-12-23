%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:22 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 116 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 259 expanded)
%              Number of equality atoms :   44 ( 171 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_88,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_90,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_62,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_60,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_72,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_90,plain,(
    ! [A_62,B_63] : r1_tarski(A_62,k2_xboole_0(A_62,B_63)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_93,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_90])).

tff(c_513,plain,(
    ! [B_135,A_136] :
      ( k1_tarski(B_135) = A_136
      | k1_xboole_0 = A_136
      | ~ r1_tarski(A_136,k1_tarski(B_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_520,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_93,c_513])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_520])).

tff(c_530,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_531,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_18,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_533,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_531,c_18])).

tff(c_1548,plain,(
    ! [A_250,B_251,C_252] :
      ( ~ r1_xboole_0(A_250,B_251)
      | ~ r2_hidden(C_252,B_251)
      | ~ r2_hidden(C_252,A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1579,plain,(
    ! [C_253] : ~ r2_hidden(C_253,'#skF_4') ),
    inference(resolution,[status(thm)],[c_533,c_1548])).

tff(c_1614,plain,(
    ! [B_254] : r1_tarski('#skF_4',B_254) ),
    inference(resolution,[status(thm)],[c_6,c_1579])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1628,plain,(
    ! [B_254] : k2_xboole_0('#skF_4',B_254) = B_254 ),
    inference(resolution,[status(thm)],[c_1614,c_16])).

tff(c_1755,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1628,c_66])).

tff(c_1757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_530,c_1755])).

tff(c_1758,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1759,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1789,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_1759,c_64])).

tff(c_44,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    ! [B_52] : r1_tarski(k1_tarski(B_52),k1_tarski(B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2034,plain,(
    ! [A_288,C_289,B_290] :
      ( r2_hidden(A_288,C_289)
      | ~ r1_tarski(k2_tarski(A_288,B_290),C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2093,plain,(
    ! [A_296,C_297] :
      ( r2_hidden(A_296,C_297)
      | ~ r1_tarski(k1_tarski(A_296),C_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2034])).

tff(c_2111,plain,(
    ! [B_52] : r2_hidden(B_52,k1_tarski(B_52)) ),
    inference(resolution,[status(thm)],[c_48,c_2093])).

tff(c_1760,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_66])).

tff(c_2294,plain,(
    ! [A_329,C_330,B_331] :
      ( r1_xboole_0(A_329,C_330)
      | ~ r1_xboole_0(A_329,k2_xboole_0(B_331,C_330)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2326,plain,(
    ! [A_329] :
      ( r1_xboole_0(A_329,'#skF_5')
      | ~ r1_xboole_0(A_329,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1760,c_2294])).

tff(c_2753,plain,(
    ! [A_354,B_355,C_356] :
      ( ~ r1_xboole_0(A_354,B_355)
      | ~ r2_hidden(C_356,B_355)
      | ~ r2_hidden(C_356,A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3067,plain,(
    ! [C_372,A_373] :
      ( ~ r2_hidden(C_372,'#skF_5')
      | ~ r2_hidden(C_372,A_373)
      | ~ r1_xboole_0(A_373,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2326,c_2753])).

tff(c_3684,plain,(
    ! [B_433,A_434] :
      ( ~ r2_hidden('#skF_1'('#skF_5',B_433),A_434)
      | ~ r1_xboole_0(A_434,'#skF_4')
      | r1_tarski('#skF_5',B_433) ) ),
    inference(resolution,[status(thm)],[c_6,c_3067])).

tff(c_3735,plain,(
    ! [B_435] :
      ( ~ r1_xboole_0(k1_tarski('#skF_1'('#skF_5',B_435)),'#skF_4')
      | r1_tarski('#skF_5',B_435) ) ),
    inference(resolution,[status(thm)],[c_2111,c_3684])).

tff(c_3740,plain,(
    ! [B_436] :
      ( r1_tarski('#skF_5',B_436)
      | r2_hidden('#skF_1'('#skF_5',B_436),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_3735])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3752,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3740,c_4])).

tff(c_3031,plain,(
    ! [B_369,A_370] :
      ( k1_tarski(B_369) = A_370
      | k1_xboole_0 = A_370
      | ~ r1_tarski(A_370,k1_tarski(B_369)) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3042,plain,(
    ! [A_370] :
      ( k1_tarski('#skF_3') = A_370
      | k1_xboole_0 = A_370
      | ~ r1_tarski(A_370,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1759,c_3031])).

tff(c_3047,plain,(
    ! [A_370] :
      ( A_370 = '#skF_4'
      | k1_xboole_0 = A_370
      | ~ r1_tarski(A_370,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_3042])).

tff(c_3761,plain,
    ( '#skF_5' = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3752,c_3047])).

tff(c_3775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1758,c_1789,c_3761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.88  
% 4.71/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.88  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.71/1.88  
% 4.71/1.88  %Foreground sorts:
% 4.71/1.88  
% 4.71/1.88  
% 4.71/1.88  %Background operators:
% 4.71/1.88  
% 4.71/1.88  
% 4.71/1.88  %Foreground operators:
% 4.71/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.71/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.71/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.71/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.71/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.71/1.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.71/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.71/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.71/1.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.88  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.88  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.71/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.71/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.71/1.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.71/1.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.71/1.88  
% 4.71/1.89  tff(f_140, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.71/1.89  tff(f_88, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.71/1.89  tff(f_113, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.71/1.89  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.71/1.89  tff(f_70, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.71/1.89  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.71/1.89  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.71/1.89  tff(f_107, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.71/1.89  tff(f_90, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.71/1.89  tff(f_121, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.71/1.89  tff(f_86, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.71/1.89  tff(c_62, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.71/1.89  tff(c_74, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 4.71/1.89  tff(c_60, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.71/1.89  tff(c_72, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 4.71/1.89  tff(c_66, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.71/1.89  tff(c_90, plain, (![A_62, B_63]: (r1_tarski(A_62, k2_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.71/1.89  tff(c_93, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_90])).
% 4.71/1.89  tff(c_513, plain, (![B_135, A_136]: (k1_tarski(B_135)=A_136 | k1_xboole_0=A_136 | ~r1_tarski(A_136, k1_tarski(B_135)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.71/1.89  tff(c_520, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_93, c_513])).
% 4.71/1.89  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_520])).
% 4.71/1.89  tff(c_530, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 4.71/1.89  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.71/1.89  tff(c_531, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 4.71/1.89  tff(c_18, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.71/1.89  tff(c_533, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_531, c_531, c_18])).
% 4.71/1.89  tff(c_1548, plain, (![A_250, B_251, C_252]: (~r1_xboole_0(A_250, B_251) | ~r2_hidden(C_252, B_251) | ~r2_hidden(C_252, A_250))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.71/1.89  tff(c_1579, plain, (![C_253]: (~r2_hidden(C_253, '#skF_4'))), inference(resolution, [status(thm)], [c_533, c_1548])).
% 4.71/1.89  tff(c_1614, plain, (![B_254]: (r1_tarski('#skF_4', B_254))), inference(resolution, [status(thm)], [c_6, c_1579])).
% 4.71/1.89  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.71/1.89  tff(c_1628, plain, (![B_254]: (k2_xboole_0('#skF_4', B_254)=B_254)), inference(resolution, [status(thm)], [c_1614, c_16])).
% 4.71/1.89  tff(c_1755, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1628, c_66])).
% 4.71/1.89  tff(c_1757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_530, c_1755])).
% 4.71/1.89  tff(c_1758, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 4.71/1.89  tff(c_1759, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 4.71/1.89  tff(c_64, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.71/1.89  tff(c_1789, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_1759, c_64])).
% 4.71/1.89  tff(c_44, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.71/1.89  tff(c_48, plain, (![B_52]: (r1_tarski(k1_tarski(B_52), k1_tarski(B_52)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.71/1.89  tff(c_30, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.71/1.89  tff(c_2034, plain, (![A_288, C_289, B_290]: (r2_hidden(A_288, C_289) | ~r1_tarski(k2_tarski(A_288, B_290), C_289))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.71/1.89  tff(c_2093, plain, (![A_296, C_297]: (r2_hidden(A_296, C_297) | ~r1_tarski(k1_tarski(A_296), C_297))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2034])).
% 4.71/1.89  tff(c_2111, plain, (![B_52]: (r2_hidden(B_52, k1_tarski(B_52)))), inference(resolution, [status(thm)], [c_48, c_2093])).
% 4.71/1.89  tff(c_1760, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_66])).
% 4.71/1.89  tff(c_2294, plain, (![A_329, C_330, B_331]: (r1_xboole_0(A_329, C_330) | ~r1_xboole_0(A_329, k2_xboole_0(B_331, C_330)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.71/1.89  tff(c_2326, plain, (![A_329]: (r1_xboole_0(A_329, '#skF_5') | ~r1_xboole_0(A_329, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1760, c_2294])).
% 4.71/1.89  tff(c_2753, plain, (![A_354, B_355, C_356]: (~r1_xboole_0(A_354, B_355) | ~r2_hidden(C_356, B_355) | ~r2_hidden(C_356, A_354))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.71/1.89  tff(c_3067, plain, (![C_372, A_373]: (~r2_hidden(C_372, '#skF_5') | ~r2_hidden(C_372, A_373) | ~r1_xboole_0(A_373, '#skF_4'))), inference(resolution, [status(thm)], [c_2326, c_2753])).
% 4.71/1.89  tff(c_3684, plain, (![B_433, A_434]: (~r2_hidden('#skF_1'('#skF_5', B_433), A_434) | ~r1_xboole_0(A_434, '#skF_4') | r1_tarski('#skF_5', B_433))), inference(resolution, [status(thm)], [c_6, c_3067])).
% 4.71/1.89  tff(c_3735, plain, (![B_435]: (~r1_xboole_0(k1_tarski('#skF_1'('#skF_5', B_435)), '#skF_4') | r1_tarski('#skF_5', B_435))), inference(resolution, [status(thm)], [c_2111, c_3684])).
% 4.71/1.89  tff(c_3740, plain, (![B_436]: (r1_tarski('#skF_5', B_436) | r2_hidden('#skF_1'('#skF_5', B_436), '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_3735])).
% 4.71/1.89  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.71/1.89  tff(c_3752, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3740, c_4])).
% 4.71/1.89  tff(c_3031, plain, (![B_369, A_370]: (k1_tarski(B_369)=A_370 | k1_xboole_0=A_370 | ~r1_tarski(A_370, k1_tarski(B_369)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.71/1.89  tff(c_3042, plain, (![A_370]: (k1_tarski('#skF_3')=A_370 | k1_xboole_0=A_370 | ~r1_tarski(A_370, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1759, c_3031])).
% 4.71/1.89  tff(c_3047, plain, (![A_370]: (A_370='#skF_4' | k1_xboole_0=A_370 | ~r1_tarski(A_370, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1759, c_3042])).
% 4.71/1.89  tff(c_3761, plain, ('#skF_5'='#skF_4' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3752, c_3047])).
% 4.71/1.89  tff(c_3775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1758, c_1789, c_3761])).
% 4.71/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.89  
% 4.71/1.89  Inference rules
% 4.71/1.89  ----------------------
% 4.71/1.89  #Ref     : 0
% 4.71/1.89  #Sup     : 840
% 4.71/1.89  #Fact    : 0
% 4.71/1.89  #Define  : 0
% 4.71/1.89  #Split   : 6
% 4.71/1.89  #Chain   : 0
% 4.71/1.89  #Close   : 0
% 4.71/1.89  
% 4.71/1.89  Ordering : KBO
% 4.71/1.89  
% 4.71/1.89  Simplification rules
% 4.71/1.89  ----------------------
% 4.71/1.89  #Subsume      : 176
% 4.71/1.89  #Demod        : 340
% 4.71/1.89  #Tautology    : 457
% 4.71/1.89  #SimpNegUnit  : 15
% 4.71/1.89  #BackRed      : 18
% 4.71/1.89  
% 4.71/1.89  #Partial instantiations: 0
% 4.71/1.89  #Strategies tried      : 1
% 4.71/1.89  
% 4.71/1.89  Timing (in seconds)
% 4.71/1.89  ----------------------
% 4.71/1.90  Preprocessing        : 0.34
% 4.71/1.90  Parsing              : 0.18
% 4.71/1.90  CNF conversion       : 0.03
% 4.71/1.90  Main loop            : 0.80
% 4.71/1.90  Inferencing          : 0.31
% 4.71/1.90  Reduction            : 0.25
% 4.71/1.90  Demodulation         : 0.17
% 4.71/1.90  BG Simplification    : 0.03
% 4.71/1.90  Subsumption          : 0.14
% 4.71/1.90  Abstraction          : 0.03
% 4.71/1.90  MUC search           : 0.00
% 4.71/1.90  Cooper               : 0.00
% 4.71/1.90  Total                : 1.17
% 4.71/1.90  Index Insertion      : 0.00
% 4.71/1.90  Index Deletion       : 0.00
% 4.71/1.90  Index Matching       : 0.00
% 4.71/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
