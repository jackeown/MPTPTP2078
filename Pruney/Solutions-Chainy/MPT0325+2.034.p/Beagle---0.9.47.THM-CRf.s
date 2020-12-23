%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:25 EST 2020

% Result     : Theorem 5.17s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 271 expanded)
%              Number of leaves         :   31 ( 106 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 589 expanded)
%              Number of equality atoms :   25 ( 110 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_54,plain,
    ( ~ r1_tarski('#skF_10','#skF_12')
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_89,plain,(
    ~ r1_tarski('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [B_54] : k2_zfmisc_1(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_978,plain,(
    ! [A_177,B_178,C_179] :
      ( r2_hidden('#skF_4'(A_177,B_178,C_179),A_177)
      | r2_hidden('#skF_6'(A_177,B_178,C_179),C_179)
      | k2_zfmisc_1(A_177,B_178) = C_179 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2513,plain,(
    ! [A_287,B_288,B_289,C_290] :
      ( ~ r1_xboole_0(A_287,B_288)
      | r2_hidden('#skF_6'(k3_xboole_0(A_287,B_288),B_289,C_290),C_290)
      | k2_zfmisc_1(k3_xboole_0(A_287,B_288),B_289) = C_290 ) ),
    inference(resolution,[status(thm)],[c_978,c_10])).

tff(c_2569,plain,(
    ! [A_11,B_289,C_290] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | r2_hidden('#skF_6'(k1_xboole_0,B_289,C_290),C_290)
      | k2_zfmisc_1(k3_xboole_0(A_11,k1_xboole_0),B_289) = C_290 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2513])).

tff(c_2586,plain,(
    ! [B_291,C_292] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_291,C_292),C_292)
      | k1_xboole_0 = C_292 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12,c_16,c_2569])).

tff(c_58,plain,(
    r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_220,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( r2_hidden(k4_tarski(A_94,B_95),k2_zfmisc_1(C_96,D_97))
      | ~ r2_hidden(B_95,D_97)
      | ~ r2_hidden(A_94,C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2307,plain,(
    ! [B_278,B_281,A_277,C_280,D_279] :
      ( r2_hidden(k4_tarski(A_277,B_278),B_281)
      | ~ r1_tarski(k2_zfmisc_1(C_280,D_279),B_281)
      | ~ r2_hidden(B_278,D_279)
      | ~ r2_hidden(A_277,C_280) ) ),
    inference(resolution,[status(thm)],[c_220,c_2])).

tff(c_2371,plain,(
    ! [A_282,B_283] :
      ( r2_hidden(k4_tarski(A_282,B_283),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(B_283,'#skF_10')
      | ~ r2_hidden(A_282,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_58,c_2307])).

tff(c_44,plain,(
    ! [B_50,D_52,A_49,C_51] :
      ( r2_hidden(B_50,D_52)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2386,plain,(
    ! [B_283,A_282] :
      ( r2_hidden(B_283,'#skF_12')
      | ~ r2_hidden(B_283,'#skF_10')
      | ~ r2_hidden(A_282,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2371,c_44])).

tff(c_2390,plain,(
    ! [A_284] : ~ r2_hidden(A_284,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2386])).

tff(c_2444,plain,(
    ! [B_2] : r1_tarski('#skF_9',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_2390])).

tff(c_2447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2444,c_89])).

tff(c_2448,plain,(
    ! [B_283] :
      ( r2_hidden(B_283,'#skF_12')
      | ~ r2_hidden(B_283,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_2386])).

tff(c_2637,plain,(
    ! [B_291] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_291,'#skF_10'),'#skF_12')
      | k1_xboole_0 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_2586,c_2448])).

tff(c_2651,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_2637])).

tff(c_50,plain,(
    ! [A_53] : k2_zfmisc_1(A_53,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2686,plain,(
    ! [A_53] : k2_zfmisc_1(A_53,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2651,c_2651,c_50])).

tff(c_56,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2688,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2651,c_56])).

tff(c_2831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2686,c_2688])).

tff(c_2833,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitRight,[status(thm)],[c_2637])).

tff(c_2585,plain,(
    ! [B_289,C_290] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_289,C_290),C_290)
      | k1_xboole_0 = C_290 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12,c_16,c_2569])).

tff(c_46,plain,(
    ! [A_49,C_51,B_50,D_52] :
      ( r2_hidden(A_49,C_51)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2387,plain,(
    ! [A_282,B_283] :
      ( r2_hidden(A_282,'#skF_11')
      | ~ r2_hidden(B_283,'#skF_10')
      | ~ r2_hidden(A_282,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2371,c_46])).

tff(c_3040,plain,(
    ! [B_305] : ~ r2_hidden(B_305,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2387])).

tff(c_3048,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2585,c_3040])).

tff(c_3101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2833,c_3048])).

tff(c_3103,plain,(
    ! [A_306] :
      ( r2_hidden(A_306,'#skF_11')
      | ~ r2_hidden(A_306,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_2387])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3212,plain,(
    ! [A_312] :
      ( r1_tarski(A_312,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_312,'#skF_11'),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3103,c_4])).

tff(c_3220,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_3212])).

tff(c_3225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_89,c_3220])).

tff(c_3226,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4116,plain,(
    ! [A_431,B_432,C_433] :
      ( r2_hidden('#skF_4'(A_431,B_432,C_433),A_431)
      | r2_hidden('#skF_6'(A_431,B_432,C_433),C_433)
      | k2_zfmisc_1(A_431,B_432) = C_433 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3262,plain,(
    ! [A_322,B_323,C_324] :
      ( ~ r1_xboole_0(A_322,B_323)
      | ~ r2_hidden(C_324,k3_xboole_0(A_322,B_323)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3269,plain,(
    ! [A_11,C_324] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_324,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3262])).

tff(c_3272,plain,(
    ! [C_324] : ~ r2_hidden(C_324,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3269])).

tff(c_4198,plain,(
    ! [A_431,B_432] :
      ( r2_hidden('#skF_4'(A_431,B_432,k1_xboole_0),A_431)
      | k2_zfmisc_1(A_431,B_432) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4116,c_3272])).

tff(c_3358,plain,(
    ! [A_348,B_349,C_350,D_351] :
      ( r2_hidden(k4_tarski(A_348,B_349),k2_zfmisc_1(C_350,D_351))
      | ~ r2_hidden(B_349,D_351)
      | ~ r2_hidden(A_348,C_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5445,plain,(
    ! [D_533,C_532,B_535,B_534,A_531] :
      ( r2_hidden(k4_tarski(A_531,B_534),B_535)
      | ~ r1_tarski(k2_zfmisc_1(C_532,D_533),B_535)
      | ~ r2_hidden(B_534,D_533)
      | ~ r2_hidden(A_531,C_532) ) ),
    inference(resolution,[status(thm)],[c_3358,c_2])).

tff(c_5660,plain,(
    ! [A_550,B_551] :
      ( r2_hidden(k4_tarski(A_550,B_551),k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(B_551,'#skF_10')
      | ~ r2_hidden(A_550,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_58,c_5445])).

tff(c_5676,plain,(
    ! [B_551,A_550] :
      ( r2_hidden(B_551,'#skF_12')
      | ~ r2_hidden(B_551,'#skF_10')
      | ~ r2_hidden(A_550,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5660,c_44])).

tff(c_6008,plain,(
    ! [A_566] : ~ r2_hidden(A_566,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5676])).

tff(c_6059,plain,(
    ! [B_432] : k2_zfmisc_1('#skF_9',B_432) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4198,c_6008])).

tff(c_6094,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6059,c_56])).

tff(c_6096,plain,(
    ! [B_568] :
      ( r2_hidden(B_568,'#skF_12')
      | ~ r2_hidden(B_568,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_5676])).

tff(c_6156,plain,(
    ! [B_569] :
      ( r2_hidden('#skF_1'('#skF_10',B_569),'#skF_12')
      | r1_tarski('#skF_10',B_569) ) ),
    inference(resolution,[status(thm)],[c_6,c_6096])).

tff(c_6162,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_6156,c_4])).

tff(c_6167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3226,c_3226,c_6162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:45:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.17/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.02  
% 5.17/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.02  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 5.17/2.02  
% 5.17/2.02  %Foreground sorts:
% 5.17/2.02  
% 5.17/2.02  
% 5.17/2.02  %Background operators:
% 5.17/2.02  
% 5.17/2.02  
% 5.17/2.02  %Foreground operators:
% 5.17/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.17/2.02  tff('#skF_11', type, '#skF_11': $i).
% 5.17/2.02  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.17/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.17/2.02  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.17/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.17/2.02  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.17/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.17/2.02  tff('#skF_10', type, '#skF_10': $i).
% 5.17/2.02  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 5.17/2.02  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.17/2.02  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.17/2.02  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 5.17/2.02  tff('#skF_9', type, '#skF_9': $i).
% 5.17/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.17/2.02  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.17/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/2.02  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.17/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.17/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.17/2.02  tff('#skF_12', type, '#skF_12': $i).
% 5.17/2.02  
% 5.17/2.04  tff(f_85, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 5.17/2.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.17/2.04  tff(f_76, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.17/2.04  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.17/2.04  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.17/2.04  tff(f_64, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 5.17/2.04  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.17/2.04  tff(f_70, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.17/2.04  tff(c_54, plain, (~r1_tarski('#skF_10', '#skF_12') | ~r1_tarski('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.17/2.04  tff(c_89, plain, (~r1_tarski('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_54])).
% 5.17/2.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/2.04  tff(c_52, plain, (![B_54]: (k2_zfmisc_1(k1_xboole_0, B_54)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.17/2.04  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.17/2.04  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.17/2.04  tff(c_978, plain, (![A_177, B_178, C_179]: (r2_hidden('#skF_4'(A_177, B_178, C_179), A_177) | r2_hidden('#skF_6'(A_177, B_178, C_179), C_179) | k2_zfmisc_1(A_177, B_178)=C_179)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.17/2.04  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.17/2.04  tff(c_2513, plain, (![A_287, B_288, B_289, C_290]: (~r1_xboole_0(A_287, B_288) | r2_hidden('#skF_6'(k3_xboole_0(A_287, B_288), B_289, C_290), C_290) | k2_zfmisc_1(k3_xboole_0(A_287, B_288), B_289)=C_290)), inference(resolution, [status(thm)], [c_978, c_10])).
% 5.17/2.04  tff(c_2569, plain, (![A_11, B_289, C_290]: (~r1_xboole_0(A_11, k1_xboole_0) | r2_hidden('#skF_6'(k1_xboole_0, B_289, C_290), C_290) | k2_zfmisc_1(k3_xboole_0(A_11, k1_xboole_0), B_289)=C_290)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2513])).
% 5.17/2.04  tff(c_2586, plain, (![B_291, C_292]: (r2_hidden('#skF_6'(k1_xboole_0, B_291, C_292), C_292) | k1_xboole_0=C_292)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_12, c_16, c_2569])).
% 5.17/2.04  tff(c_58, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.17/2.04  tff(c_220, plain, (![A_94, B_95, C_96, D_97]: (r2_hidden(k4_tarski(A_94, B_95), k2_zfmisc_1(C_96, D_97)) | ~r2_hidden(B_95, D_97) | ~r2_hidden(A_94, C_96))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.17/2.04  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/2.04  tff(c_2307, plain, (![B_278, B_281, A_277, C_280, D_279]: (r2_hidden(k4_tarski(A_277, B_278), B_281) | ~r1_tarski(k2_zfmisc_1(C_280, D_279), B_281) | ~r2_hidden(B_278, D_279) | ~r2_hidden(A_277, C_280))), inference(resolution, [status(thm)], [c_220, c_2])).
% 5.17/2.04  tff(c_2371, plain, (![A_282, B_283]: (r2_hidden(k4_tarski(A_282, B_283), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(B_283, '#skF_10') | ~r2_hidden(A_282, '#skF_9'))), inference(resolution, [status(thm)], [c_58, c_2307])).
% 5.17/2.04  tff(c_44, plain, (![B_50, D_52, A_49, C_51]: (r2_hidden(B_50, D_52) | ~r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.17/2.04  tff(c_2386, plain, (![B_283, A_282]: (r2_hidden(B_283, '#skF_12') | ~r2_hidden(B_283, '#skF_10') | ~r2_hidden(A_282, '#skF_9'))), inference(resolution, [status(thm)], [c_2371, c_44])).
% 5.17/2.04  tff(c_2390, plain, (![A_284]: (~r2_hidden(A_284, '#skF_9'))), inference(splitLeft, [status(thm)], [c_2386])).
% 5.17/2.04  tff(c_2444, plain, (![B_2]: (r1_tarski('#skF_9', B_2))), inference(resolution, [status(thm)], [c_6, c_2390])).
% 5.17/2.04  tff(c_2447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2444, c_89])).
% 5.17/2.04  tff(c_2448, plain, (![B_283]: (r2_hidden(B_283, '#skF_12') | ~r2_hidden(B_283, '#skF_10'))), inference(splitRight, [status(thm)], [c_2386])).
% 5.17/2.04  tff(c_2637, plain, (![B_291]: (r2_hidden('#skF_6'(k1_xboole_0, B_291, '#skF_10'), '#skF_12') | k1_xboole_0='#skF_10')), inference(resolution, [status(thm)], [c_2586, c_2448])).
% 5.17/2.04  tff(c_2651, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_2637])).
% 5.17/2.04  tff(c_50, plain, (![A_53]: (k2_zfmisc_1(A_53, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.17/2.04  tff(c_2686, plain, (![A_53]: (k2_zfmisc_1(A_53, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2651, c_2651, c_50])).
% 5.17/2.04  tff(c_56, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.17/2.04  tff(c_2688, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_2651, c_56])).
% 5.17/2.04  tff(c_2831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2686, c_2688])).
% 5.17/2.04  tff(c_2833, plain, (k1_xboole_0!='#skF_10'), inference(splitRight, [status(thm)], [c_2637])).
% 5.17/2.04  tff(c_2585, plain, (![B_289, C_290]: (r2_hidden('#skF_6'(k1_xboole_0, B_289, C_290), C_290) | k1_xboole_0=C_290)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_12, c_16, c_2569])).
% 5.17/2.04  tff(c_46, plain, (![A_49, C_51, B_50, D_52]: (r2_hidden(A_49, C_51) | ~r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.17/2.04  tff(c_2387, plain, (![A_282, B_283]: (r2_hidden(A_282, '#skF_11') | ~r2_hidden(B_283, '#skF_10') | ~r2_hidden(A_282, '#skF_9'))), inference(resolution, [status(thm)], [c_2371, c_46])).
% 5.17/2.04  tff(c_3040, plain, (![B_305]: (~r2_hidden(B_305, '#skF_10'))), inference(splitLeft, [status(thm)], [c_2387])).
% 5.17/2.04  tff(c_3048, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_2585, c_3040])).
% 5.17/2.04  tff(c_3101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2833, c_3048])).
% 5.17/2.04  tff(c_3103, plain, (![A_306]: (r2_hidden(A_306, '#skF_11') | ~r2_hidden(A_306, '#skF_9'))), inference(splitRight, [status(thm)], [c_2387])).
% 5.17/2.04  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.17/2.04  tff(c_3212, plain, (![A_312]: (r1_tarski(A_312, '#skF_11') | ~r2_hidden('#skF_1'(A_312, '#skF_11'), '#skF_9'))), inference(resolution, [status(thm)], [c_3103, c_4])).
% 5.17/2.04  tff(c_3220, plain, (r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_6, c_3212])).
% 5.17/2.04  tff(c_3225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_89, c_3220])).
% 5.17/2.04  tff(c_3226, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitRight, [status(thm)], [c_54])).
% 5.17/2.04  tff(c_4116, plain, (![A_431, B_432, C_433]: (r2_hidden('#skF_4'(A_431, B_432, C_433), A_431) | r2_hidden('#skF_6'(A_431, B_432, C_433), C_433) | k2_zfmisc_1(A_431, B_432)=C_433)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.17/2.04  tff(c_3262, plain, (![A_322, B_323, C_324]: (~r1_xboole_0(A_322, B_323) | ~r2_hidden(C_324, k3_xboole_0(A_322, B_323)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.17/2.04  tff(c_3269, plain, (![A_11, C_324]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_324, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3262])).
% 5.17/2.04  tff(c_3272, plain, (![C_324]: (~r2_hidden(C_324, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3269])).
% 5.17/2.04  tff(c_4198, plain, (![A_431, B_432]: (r2_hidden('#skF_4'(A_431, B_432, k1_xboole_0), A_431) | k2_zfmisc_1(A_431, B_432)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4116, c_3272])).
% 5.17/2.04  tff(c_3358, plain, (![A_348, B_349, C_350, D_351]: (r2_hidden(k4_tarski(A_348, B_349), k2_zfmisc_1(C_350, D_351)) | ~r2_hidden(B_349, D_351) | ~r2_hidden(A_348, C_350))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.17/2.04  tff(c_5445, plain, (![D_533, C_532, B_535, B_534, A_531]: (r2_hidden(k4_tarski(A_531, B_534), B_535) | ~r1_tarski(k2_zfmisc_1(C_532, D_533), B_535) | ~r2_hidden(B_534, D_533) | ~r2_hidden(A_531, C_532))), inference(resolution, [status(thm)], [c_3358, c_2])).
% 5.17/2.04  tff(c_5660, plain, (![A_550, B_551]: (r2_hidden(k4_tarski(A_550, B_551), k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(B_551, '#skF_10') | ~r2_hidden(A_550, '#skF_9'))), inference(resolution, [status(thm)], [c_58, c_5445])).
% 5.17/2.04  tff(c_5676, plain, (![B_551, A_550]: (r2_hidden(B_551, '#skF_12') | ~r2_hidden(B_551, '#skF_10') | ~r2_hidden(A_550, '#skF_9'))), inference(resolution, [status(thm)], [c_5660, c_44])).
% 5.17/2.04  tff(c_6008, plain, (![A_566]: (~r2_hidden(A_566, '#skF_9'))), inference(splitLeft, [status(thm)], [c_5676])).
% 5.17/2.04  tff(c_6059, plain, (![B_432]: (k2_zfmisc_1('#skF_9', B_432)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4198, c_6008])).
% 5.17/2.04  tff(c_6094, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6059, c_56])).
% 5.17/2.04  tff(c_6096, plain, (![B_568]: (r2_hidden(B_568, '#skF_12') | ~r2_hidden(B_568, '#skF_10'))), inference(splitRight, [status(thm)], [c_5676])).
% 5.17/2.04  tff(c_6156, plain, (![B_569]: (r2_hidden('#skF_1'('#skF_10', B_569), '#skF_12') | r1_tarski('#skF_10', B_569))), inference(resolution, [status(thm)], [c_6, c_6096])).
% 5.17/2.04  tff(c_6162, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_6156, c_4])).
% 5.17/2.04  tff(c_6167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3226, c_3226, c_6162])).
% 5.17/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.17/2.04  
% 5.17/2.04  Inference rules
% 5.17/2.04  ----------------------
% 5.17/2.04  #Ref     : 0
% 5.17/2.04  #Sup     : 1424
% 5.17/2.04  #Fact    : 0
% 5.17/2.04  #Define  : 0
% 5.17/2.04  #Split   : 8
% 5.17/2.04  #Chain   : 0
% 5.17/2.04  #Close   : 0
% 5.17/2.04  
% 5.17/2.04  Ordering : KBO
% 5.17/2.04  
% 5.17/2.04  Simplification rules
% 5.17/2.04  ----------------------
% 5.17/2.04  #Subsume      : 508
% 5.17/2.04  #Demod        : 601
% 5.17/2.04  #Tautology    : 401
% 5.17/2.04  #SimpNegUnit  : 32
% 5.17/2.04  #BackRed      : 44
% 5.17/2.04  
% 5.17/2.04  #Partial instantiations: 0
% 5.17/2.04  #Strategies tried      : 1
% 5.17/2.04  
% 5.17/2.04  Timing (in seconds)
% 5.17/2.04  ----------------------
% 5.17/2.04  Preprocessing        : 0.31
% 5.17/2.04  Parsing              : 0.17
% 5.17/2.04  CNF conversion       : 0.02
% 5.17/2.04  Main loop            : 0.92
% 5.17/2.04  Inferencing          : 0.37
% 5.17/2.04  Reduction            : 0.26
% 5.17/2.04  Demodulation         : 0.18
% 5.17/2.04  BG Simplification    : 0.03
% 5.17/2.04  Subsumption          : 0.18
% 5.17/2.04  Abstraction          : 0.04
% 5.17/2.04  MUC search           : 0.00
% 5.17/2.04  Cooper               : 0.00
% 5.17/2.04  Total                : 1.26
% 5.17/2.04  Index Insertion      : 0.00
% 5.17/2.04  Index Deletion       : 0.00
% 5.17/2.04  Index Matching       : 0.00
% 5.17/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
