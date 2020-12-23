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
% DateTime   : Thu Dec  3 09:50:17 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 320 expanded)
%              Number of leaves         :   28 ( 114 expanded)
%              Depth                    :   16
%              Number of atoms          :  186 ( 711 expanded)
%              Number of equality atoms :   73 ( 440 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_48,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(k1_tarski(A_28),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,
    ( k1_xboole_0 != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_57,plain,(
    k1_tarski('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_52,plain,(
    k2_xboole_0('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_194,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_198,plain,
    ( k1_tarski('#skF_5') = '#skF_6'
    | ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_71,c_194])).

tff(c_206,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_198])).

tff(c_237,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_206])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_87,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_71,c_87])).

tff(c_170,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_tarski(A_52),B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_178,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(k1_tarski(A_52),B_53) = B_53
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_170,c_18])).

tff(c_143,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,B_47)
      | ~ r1_tarski(k1_tarski(A_46),B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_152,plain,(
    ! [A_46,B_16] : r2_hidden(A_46,k2_xboole_0(k1_tarski(A_46),B_16)) ),
    inference(resolution,[status(thm)],[c_20,c_143])).

tff(c_2050,plain,(
    ! [C_1229,B_1230,A_1231] :
      ( r2_hidden(C_1229,B_1230)
      | ~ r2_hidden(C_1229,A_1231)
      | ~ r1_tarski(A_1231,B_1230) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3283,plain,(
    ! [A_2415,B_2416,B_2417] :
      ( r2_hidden(A_2415,B_2416)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_2415),B_2417),B_2416) ) ),
    inference(resolution,[status(thm)],[c_152,c_2050])).

tff(c_3325,plain,(
    ! [A_2438,B_2439,B_2440] : r2_hidden(A_2438,k2_xboole_0(k2_xboole_0(k1_tarski(A_2438),B_2439),B_2440)) ),
    inference(resolution,[status(thm)],[c_20,c_3283])).

tff(c_3403,plain,(
    ! [A_2461,B_2462,B_2463] :
      ( r2_hidden(A_2461,k2_xboole_0(B_2462,B_2463))
      | ~ r2_hidden(A_2461,B_2462) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_3325])).

tff(c_3434,plain,(
    ! [A_2484] :
      ( r2_hidden(A_2484,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_2484,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_3403])).

tff(c_22,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3512,plain,(
    ! [A_2527] :
      ( A_2527 = '#skF_5'
      | ~ r2_hidden(A_2527,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_3434,c_22])).

tff(c_3532,plain,
    ( '#skF_2'('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8,c_3512])).

tff(c_3539,plain,(
    '#skF_2'('#skF_6') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_3532])).

tff(c_3546,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3539,c_8])).

tff(c_3551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_237,c_3546])).

tff(c_3552,plain,(
    k1_tarski('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3578,plain,(
    ! [A_2571,B_2572] :
      ( k2_xboole_0(A_2571,B_2572) = B_2572
      | ~ r1_tarski(A_2571,B_2572) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3590,plain,(
    ! [B_9] : k2_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_14,c_3578])).

tff(c_3553,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3565,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3553,c_8])).

tff(c_3697,plain,(
    ! [A_2590,C_2591,B_2592] :
      ( r1_tarski(A_2590,k2_xboole_0(C_2591,B_2592))
      | ~ r1_tarski(A_2590,B_2592) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3716,plain,(
    ! [A_2593] :
      ( r1_tarski(A_2593,k1_tarski('#skF_5'))
      | ~ r1_tarski(A_2593,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_3697])).

tff(c_40,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | ~ r1_tarski(k1_tarski(A_28),B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3726,plain,(
    ! [A_2594] :
      ( r2_hidden(A_2594,k1_tarski('#skF_5'))
      | ~ r1_tarski(k1_tarski(A_2594),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3716,c_40])).

tff(c_3736,plain,(
    ! [A_2595] :
      ( A_2595 = '#skF_5'
      | ~ r1_tarski(k1_tarski(A_2595),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3726,c_22])).

tff(c_3742,plain,(
    ! [A_2596] :
      ( A_2596 = '#skF_5'
      | ~ r2_hidden(A_2596,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_3736])).

tff(c_3752,plain,
    ( '#skF_2'('#skF_7') = '#skF_5'
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3565,c_3742])).

tff(c_3753,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3752])).

tff(c_3759,plain,(
    k2_xboole_0('#skF_6','#skF_6') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3753,c_52])).

tff(c_3760,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3590,c_3759])).

tff(c_3762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_3760])).

tff(c_3764,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3752])).

tff(c_3763,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3752])).

tff(c_3792,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3763,c_3565])).

tff(c_3795,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_3764,c_3792])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3561,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_3588,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_3561,c_3578])).

tff(c_3621,plain,(
    ! [A_2576,B_2577] :
      ( r1_tarski(k1_tarski(A_2576),B_2577)
      | ~ r2_hidden(A_2576,B_2577) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3625,plain,(
    ! [A_2576,B_2577] :
      ( k2_xboole_0(k1_tarski(A_2576),B_2577) = B_2577
      | ~ r2_hidden(A_2576,B_2577) ) ),
    inference(resolution,[status(thm)],[c_3621,c_18])).

tff(c_3648,plain,(
    ! [A_2581,B_2582] :
      ( r2_hidden(A_2581,B_2582)
      | ~ r1_tarski(k1_tarski(A_2581),B_2582) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3661,plain,(
    ! [A_2581,B_16] : r2_hidden(A_2581,k2_xboole_0(k1_tarski(A_2581),B_16)) ),
    inference(resolution,[status(thm)],[c_20,c_3648])).

tff(c_4019,plain,(
    ! [C_2609,B_2610,A_2611] :
      ( r2_hidden(C_2609,B_2610)
      | ~ r2_hidden(C_2609,A_2611)
      | ~ r1_tarski(A_2611,B_2610) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5295,plain,(
    ! [A_3834,B_3835,B_3836] :
      ( r2_hidden(A_3834,B_3835)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(A_3834),B_3836),B_3835) ) ),
    inference(resolution,[status(thm)],[c_3661,c_4019])).

tff(c_5337,plain,(
    ! [A_3857,B_3858,B_3859] : r2_hidden(A_3857,k2_xboole_0(k2_xboole_0(k1_tarski(A_3857),B_3858),B_3859)) ),
    inference(resolution,[status(thm)],[c_20,c_5295])).

tff(c_5444,plain,(
    ! [A_3901,B_3902,B_3903] :
      ( r2_hidden(A_3901,k2_xboole_0(B_3902,B_3903))
      | ~ r2_hidden(A_3901,B_3902) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3625,c_5337])).

tff(c_5475,plain,(
    ! [A_3924] :
      ( r2_hidden(A_3924,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_3924,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3588,c_5444])).

tff(c_5525,plain,(
    ! [A_3945] :
      ( A_3945 = '#skF_5'
      | ~ r2_hidden(A_3945,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_5475,c_22])).

tff(c_5552,plain,(
    ! [B_3966] :
      ( '#skF_1'('#skF_6',B_3966) = '#skF_5'
      | r1_tarski('#skF_6',B_3966) ) ),
    inference(resolution,[status(thm)],[c_6,c_5525])).

tff(c_5642,plain,(
    ! [B_4030] :
      ( k2_xboole_0('#skF_6',B_4030) = B_4030
      | '#skF_1'('#skF_6',B_4030) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_5552,c_18])).

tff(c_5678,plain,
    ( k1_tarski('#skF_5') = '#skF_7'
    | '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5642,c_52])).

tff(c_5710,plain,(
    '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3552,c_5678])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5720,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5710,c_4])).

tff(c_5727,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3795,c_5720])).

tff(c_5743,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5727,c_18])).

tff(c_5745,plain,(
    k1_tarski('#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5743,c_52])).

tff(c_5747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3552,c_5745])).

tff(c_5748,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_5749,plain,(
    k1_tarski('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( k1_tarski('#skF_5') != '#skF_7'
    | k1_tarski('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_5815,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5749,c_5749,c_50])).

tff(c_5768,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5749,c_52])).

tff(c_6052,plain,(
    ! [A_4123,C_4124,B_4125] :
      ( r1_tarski(A_4123,k2_xboole_0(C_4124,B_4125))
      | ~ r1_tarski(A_4123,B_4125) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6080,plain,(
    ! [A_4129] :
      ( r1_tarski(A_4129,'#skF_6')
      | ~ r1_tarski(A_4129,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5768,c_6052])).

tff(c_6096,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_6080])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6098,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_6096,c_10])).

tff(c_6104,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_5815,c_6098])).

tff(c_6002,plain,(
    ! [A_4119,B_4120] :
      ( r2_hidden('#skF_1'(A_4119,B_4120),A_4119)
      | r1_tarski(A_4119,B_4120) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5778,plain,(
    ! [C_4093,A_4094] :
      ( C_4093 = A_4094
      | ~ r2_hidden(C_4093,k1_tarski(A_4094)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5785,plain,(
    ! [C_4093] :
      ( C_4093 = '#skF_5'
      | ~ r2_hidden(C_4093,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5749,c_5778])).

tff(c_6017,plain,(
    ! [B_4120] :
      ( '#skF_1'('#skF_6',B_4120) = '#skF_5'
      | r1_tarski('#skF_6',B_4120) ) ),
    inference(resolution,[status(thm)],[c_6002,c_5785])).

tff(c_6109,plain,(
    '#skF_1'('#skF_6','#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6017,c_6104])).

tff(c_6116,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r1_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6109,c_4])).

tff(c_6121,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_6104,c_6116])).

tff(c_6138,plain,(
    ! [A_4130] :
      ( r1_tarski(k1_tarski(A_4130),'#skF_6')
      | ~ r2_hidden(A_4130,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_6080])).

tff(c_6154,plain,(
    ! [A_4131] :
      ( r2_hidden(A_4131,'#skF_6')
      | ~ r2_hidden(A_4131,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6138,c_40])).

tff(c_6166,plain,
    ( r2_hidden('#skF_2'('#skF_7'),'#skF_6')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_8,c_6154])).

tff(c_6172,plain,(
    r2_hidden('#skF_2'('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_5748,c_6166])).

tff(c_6176,plain,(
    '#skF_2'('#skF_7') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6172,c_5785])).

tff(c_6207,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_6176,c_8])).

tff(c_6211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5748,c_6121,c_6207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/2.03  
% 4.84/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/2.03  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4
% 4.84/2.03  
% 4.84/2.03  %Foreground sorts:
% 4.84/2.03  
% 4.84/2.03  
% 4.84/2.03  %Background operators:
% 4.84/2.03  
% 4.84/2.03  
% 4.84/2.03  %Foreground operators:
% 4.84/2.03  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.84/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.84/2.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.84/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/2.03  tff('#skF_7', type, '#skF_7': $i).
% 4.84/2.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.84/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.84/2.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.84/2.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.84/2.03  tff('#skF_5', type, '#skF_5': $i).
% 4.84/2.03  tff('#skF_6', type, '#skF_6': $i).
% 4.84/2.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.84/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/2.03  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.84/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.84/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.84/2.03  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.84/2.03  
% 4.84/2.05  tff(f_94, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 4.84/2.05  tff(f_73, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.84/2.05  tff(f_56, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.84/2.05  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.84/2.05  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.84/2.05  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.84/2.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.84/2.05  tff(f_63, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.84/2.05  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.84/2.05  tff(c_48, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.84/2.05  tff(c_67, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_48])).
% 4.84/2.05  tff(c_42, plain, (![A_28, B_29]: (r1_tarski(k1_tarski(A_28), B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.84/2.05  tff(c_46, plain, (k1_xboole_0!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.84/2.05  tff(c_57, plain, (k1_tarski('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_46])).
% 4.84/2.05  tff(c_52, plain, (k2_xboole_0('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.84/2.05  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.84/2.05  tff(c_71, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_20])).
% 4.84/2.05  tff(c_194, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.84/2.05  tff(c_198, plain, (k1_tarski('#skF_5')='#skF_6' | ~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_71, c_194])).
% 4.84/2.05  tff(c_206, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_57, c_198])).
% 4.84/2.05  tff(c_237, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_206])).
% 4.84/2.05  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.84/2.05  tff(c_87, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.84/2.05  tff(c_97, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_71, c_87])).
% 4.84/2.05  tff(c_170, plain, (![A_52, B_53]: (r1_tarski(k1_tarski(A_52), B_53) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.84/2.05  tff(c_18, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.84/2.05  tff(c_178, plain, (![A_52, B_53]: (k2_xboole_0(k1_tarski(A_52), B_53)=B_53 | ~r2_hidden(A_52, B_53))), inference(resolution, [status(thm)], [c_170, c_18])).
% 4.84/2.05  tff(c_143, plain, (![A_46, B_47]: (r2_hidden(A_46, B_47) | ~r1_tarski(k1_tarski(A_46), B_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.84/2.05  tff(c_152, plain, (![A_46, B_16]: (r2_hidden(A_46, k2_xboole_0(k1_tarski(A_46), B_16)))), inference(resolution, [status(thm)], [c_20, c_143])).
% 4.84/2.05  tff(c_2050, plain, (![C_1229, B_1230, A_1231]: (r2_hidden(C_1229, B_1230) | ~r2_hidden(C_1229, A_1231) | ~r1_tarski(A_1231, B_1230))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/2.05  tff(c_3283, plain, (![A_2415, B_2416, B_2417]: (r2_hidden(A_2415, B_2416) | ~r1_tarski(k2_xboole_0(k1_tarski(A_2415), B_2417), B_2416))), inference(resolution, [status(thm)], [c_152, c_2050])).
% 4.84/2.05  tff(c_3325, plain, (![A_2438, B_2439, B_2440]: (r2_hidden(A_2438, k2_xboole_0(k2_xboole_0(k1_tarski(A_2438), B_2439), B_2440)))), inference(resolution, [status(thm)], [c_20, c_3283])).
% 4.84/2.05  tff(c_3403, plain, (![A_2461, B_2462, B_2463]: (r2_hidden(A_2461, k2_xboole_0(B_2462, B_2463)) | ~r2_hidden(A_2461, B_2462))), inference(superposition, [status(thm), theory('equality')], [c_178, c_3325])).
% 4.84/2.05  tff(c_3434, plain, (![A_2484]: (r2_hidden(A_2484, k1_tarski('#skF_5')) | ~r2_hidden(A_2484, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_3403])).
% 4.84/2.05  tff(c_22, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.84/2.05  tff(c_3512, plain, (![A_2527]: (A_2527='#skF_5' | ~r2_hidden(A_2527, '#skF_6'))), inference(resolution, [status(thm)], [c_3434, c_22])).
% 4.84/2.05  tff(c_3532, plain, ('#skF_2'('#skF_6')='#skF_5' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_8, c_3512])).
% 4.84/2.05  tff(c_3539, plain, ('#skF_2'('#skF_6')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_67, c_3532])).
% 4.84/2.05  tff(c_3546, plain, (r2_hidden('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3539, c_8])).
% 4.84/2.05  tff(c_3551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_237, c_3546])).
% 4.84/2.05  tff(c_3552, plain, (k1_tarski('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_48])).
% 4.84/2.05  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.84/2.05  tff(c_3578, plain, (![A_2571, B_2572]: (k2_xboole_0(A_2571, B_2572)=B_2572 | ~r1_tarski(A_2571, B_2572))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.84/2.05  tff(c_3590, plain, (![B_9]: (k2_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_14, c_3578])).
% 4.84/2.05  tff(c_3553, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 4.84/2.05  tff(c_3565, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3553, c_8])).
% 4.84/2.05  tff(c_3697, plain, (![A_2590, C_2591, B_2592]: (r1_tarski(A_2590, k2_xboole_0(C_2591, B_2592)) | ~r1_tarski(A_2590, B_2592))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.84/2.05  tff(c_3716, plain, (![A_2593]: (r1_tarski(A_2593, k1_tarski('#skF_5')) | ~r1_tarski(A_2593, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_3697])).
% 4.84/2.05  tff(c_40, plain, (![A_28, B_29]: (r2_hidden(A_28, B_29) | ~r1_tarski(k1_tarski(A_28), B_29))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.84/2.05  tff(c_3726, plain, (![A_2594]: (r2_hidden(A_2594, k1_tarski('#skF_5')) | ~r1_tarski(k1_tarski(A_2594), '#skF_7'))), inference(resolution, [status(thm)], [c_3716, c_40])).
% 4.84/2.05  tff(c_3736, plain, (![A_2595]: (A_2595='#skF_5' | ~r1_tarski(k1_tarski(A_2595), '#skF_7'))), inference(resolution, [status(thm)], [c_3726, c_22])).
% 4.84/2.05  tff(c_3742, plain, (![A_2596]: (A_2596='#skF_5' | ~r2_hidden(A_2596, '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_3736])).
% 4.84/2.05  tff(c_3752, plain, ('#skF_2'('#skF_7')='#skF_5' | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_3565, c_3742])).
% 4.84/2.05  tff(c_3753, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_3752])).
% 4.84/2.05  tff(c_3759, plain, (k2_xboole_0('#skF_6', '#skF_6')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3753, c_52])).
% 4.84/2.05  tff(c_3760, plain, (k1_tarski('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3590, c_3759])).
% 4.84/2.05  tff(c_3762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_3760])).
% 4.84/2.05  tff(c_3764, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_3752])).
% 4.84/2.05  tff(c_3763, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_3752])).
% 4.84/2.05  tff(c_3792, plain, (r2_hidden('#skF_5', '#skF_7') | '#skF_7'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3763, c_3565])).
% 4.84/2.05  tff(c_3795, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_3764, c_3792])).
% 4.84/2.05  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/2.05  tff(c_3561, plain, (r1_tarski('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_20])).
% 4.84/2.05  tff(c_3588, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_3561, c_3578])).
% 4.84/2.05  tff(c_3621, plain, (![A_2576, B_2577]: (r1_tarski(k1_tarski(A_2576), B_2577) | ~r2_hidden(A_2576, B_2577))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.84/2.05  tff(c_3625, plain, (![A_2576, B_2577]: (k2_xboole_0(k1_tarski(A_2576), B_2577)=B_2577 | ~r2_hidden(A_2576, B_2577))), inference(resolution, [status(thm)], [c_3621, c_18])).
% 4.84/2.05  tff(c_3648, plain, (![A_2581, B_2582]: (r2_hidden(A_2581, B_2582) | ~r1_tarski(k1_tarski(A_2581), B_2582))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.84/2.05  tff(c_3661, plain, (![A_2581, B_16]: (r2_hidden(A_2581, k2_xboole_0(k1_tarski(A_2581), B_16)))), inference(resolution, [status(thm)], [c_20, c_3648])).
% 4.84/2.05  tff(c_4019, plain, (![C_2609, B_2610, A_2611]: (r2_hidden(C_2609, B_2610) | ~r2_hidden(C_2609, A_2611) | ~r1_tarski(A_2611, B_2610))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/2.05  tff(c_5295, plain, (![A_3834, B_3835, B_3836]: (r2_hidden(A_3834, B_3835) | ~r1_tarski(k2_xboole_0(k1_tarski(A_3834), B_3836), B_3835))), inference(resolution, [status(thm)], [c_3661, c_4019])).
% 4.84/2.05  tff(c_5337, plain, (![A_3857, B_3858, B_3859]: (r2_hidden(A_3857, k2_xboole_0(k2_xboole_0(k1_tarski(A_3857), B_3858), B_3859)))), inference(resolution, [status(thm)], [c_20, c_5295])).
% 4.84/2.05  tff(c_5444, plain, (![A_3901, B_3902, B_3903]: (r2_hidden(A_3901, k2_xboole_0(B_3902, B_3903)) | ~r2_hidden(A_3901, B_3902))), inference(superposition, [status(thm), theory('equality')], [c_3625, c_5337])).
% 4.84/2.05  tff(c_5475, plain, (![A_3924]: (r2_hidden(A_3924, k1_tarski('#skF_5')) | ~r2_hidden(A_3924, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3588, c_5444])).
% 4.84/2.05  tff(c_5525, plain, (![A_3945]: (A_3945='#skF_5' | ~r2_hidden(A_3945, '#skF_6'))), inference(resolution, [status(thm)], [c_5475, c_22])).
% 4.84/2.05  tff(c_5552, plain, (![B_3966]: ('#skF_1'('#skF_6', B_3966)='#skF_5' | r1_tarski('#skF_6', B_3966))), inference(resolution, [status(thm)], [c_6, c_5525])).
% 4.84/2.05  tff(c_5642, plain, (![B_4030]: (k2_xboole_0('#skF_6', B_4030)=B_4030 | '#skF_1'('#skF_6', B_4030)='#skF_5')), inference(resolution, [status(thm)], [c_5552, c_18])).
% 4.84/2.05  tff(c_5678, plain, (k1_tarski('#skF_5')='#skF_7' | '#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5642, c_52])).
% 4.84/2.05  tff(c_5710, plain, ('#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3552, c_5678])).
% 4.84/2.05  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/2.05  tff(c_5720, plain, (~r2_hidden('#skF_5', '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5710, c_4])).
% 4.84/2.05  tff(c_5727, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3795, c_5720])).
% 4.84/2.05  tff(c_5743, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_5727, c_18])).
% 4.84/2.05  tff(c_5745, plain, (k1_tarski('#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5743, c_52])).
% 4.84/2.05  tff(c_5747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3552, c_5745])).
% 4.84/2.05  tff(c_5748, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_46])).
% 4.84/2.05  tff(c_5749, plain, (k1_tarski('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 4.84/2.05  tff(c_50, plain, (k1_tarski('#skF_5')!='#skF_7' | k1_tarski('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.84/2.05  tff(c_5815, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5749, c_5749, c_50])).
% 4.84/2.05  tff(c_5768, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5749, c_52])).
% 4.84/2.05  tff(c_6052, plain, (![A_4123, C_4124, B_4125]: (r1_tarski(A_4123, k2_xboole_0(C_4124, B_4125)) | ~r1_tarski(A_4123, B_4125))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.84/2.05  tff(c_6080, plain, (![A_4129]: (r1_tarski(A_4129, '#skF_6') | ~r1_tarski(A_4129, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_5768, c_6052])).
% 4.84/2.05  tff(c_6096, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_14, c_6080])).
% 4.84/2.05  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.84/2.05  tff(c_6098, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_6096, c_10])).
% 4.84/2.05  tff(c_6104, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_5815, c_6098])).
% 4.84/2.05  tff(c_6002, plain, (![A_4119, B_4120]: (r2_hidden('#skF_1'(A_4119, B_4120), A_4119) | r1_tarski(A_4119, B_4120))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.84/2.05  tff(c_5778, plain, (![C_4093, A_4094]: (C_4093=A_4094 | ~r2_hidden(C_4093, k1_tarski(A_4094)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.84/2.05  tff(c_5785, plain, (![C_4093]: (C_4093='#skF_5' | ~r2_hidden(C_4093, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5749, c_5778])).
% 4.84/2.05  tff(c_6017, plain, (![B_4120]: ('#skF_1'('#skF_6', B_4120)='#skF_5' | r1_tarski('#skF_6', B_4120))), inference(resolution, [status(thm)], [c_6002, c_5785])).
% 4.84/2.05  tff(c_6109, plain, ('#skF_1'('#skF_6', '#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_6017, c_6104])).
% 4.84/2.05  tff(c_6116, plain, (~r2_hidden('#skF_5', '#skF_7') | r1_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6109, c_4])).
% 4.84/2.05  tff(c_6121, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_6104, c_6116])).
% 4.84/2.05  tff(c_6138, plain, (![A_4130]: (r1_tarski(k1_tarski(A_4130), '#skF_6') | ~r2_hidden(A_4130, '#skF_7'))), inference(resolution, [status(thm)], [c_42, c_6080])).
% 4.84/2.05  tff(c_6154, plain, (![A_4131]: (r2_hidden(A_4131, '#skF_6') | ~r2_hidden(A_4131, '#skF_7'))), inference(resolution, [status(thm)], [c_6138, c_40])).
% 4.84/2.05  tff(c_6166, plain, (r2_hidden('#skF_2'('#skF_7'), '#skF_6') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_8, c_6154])).
% 4.84/2.05  tff(c_6172, plain, (r2_hidden('#skF_2'('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_5748, c_6166])).
% 4.84/2.05  tff(c_6176, plain, ('#skF_2'('#skF_7')='#skF_5'), inference(resolution, [status(thm)], [c_6172, c_5785])).
% 4.84/2.05  tff(c_6207, plain, (r2_hidden('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_6176, c_8])).
% 4.84/2.05  tff(c_6211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5748, c_6121, c_6207])).
% 4.84/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/2.05  
% 4.84/2.05  Inference rules
% 4.84/2.05  ----------------------
% 4.84/2.05  #Ref     : 0
% 4.84/2.05  #Sup     : 1000
% 4.84/2.05  #Fact    : 0
% 4.84/2.05  #Define  : 0
% 4.84/2.05  #Split   : 8
% 4.84/2.05  #Chain   : 0
% 4.84/2.05  #Close   : 0
% 4.84/2.05  
% 4.84/2.05  Ordering : KBO
% 4.84/2.05  
% 4.84/2.05  Simplification rules
% 4.84/2.05  ----------------------
% 4.84/2.05  #Subsume      : 106
% 4.84/2.05  #Demod        : 310
% 4.84/2.05  #Tautology    : 396
% 4.84/2.05  #SimpNegUnit  : 56
% 4.84/2.05  #BackRed      : 11
% 4.84/2.05  
% 4.84/2.05  #Partial instantiations: 2674
% 4.84/2.05  #Strategies tried      : 1
% 4.84/2.05  
% 4.84/2.05  Timing (in seconds)
% 4.84/2.05  ----------------------
% 5.21/2.05  Preprocessing        : 0.34
% 5.21/2.05  Parsing              : 0.17
% 5.21/2.05  CNF conversion       : 0.03
% 5.21/2.05  Main loop            : 0.89
% 5.21/2.05  Inferencing          : 0.40
% 5.21/2.05  Reduction            : 0.24
% 5.21/2.05  Demodulation         : 0.17
% 5.21/2.05  BG Simplification    : 0.04
% 5.21/2.05  Subsumption          : 0.14
% 5.21/2.05  Abstraction          : 0.04
% 5.21/2.05  MUC search           : 0.00
% 5.21/2.05  Cooper               : 0.00
% 5.21/2.05  Total                : 1.27
% 5.21/2.05  Index Insertion      : 0.00
% 5.21/2.05  Index Deletion       : 0.00
% 5.21/2.05  Index Matching       : 0.00
% 5.21/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
