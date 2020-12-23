%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:57 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 166 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 281 expanded)
%              Number of equality atoms :   17 (  99 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_15 > #skF_10 > #skF_14 > #skF_2 > #skF_13 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
      <=> ( A = C
          & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(c_34,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_94,plain,
    ( '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_13','#skF_15')
    | '#skF_14' != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_131,plain,(
    '#skF_14' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_100,plain,
    ( '#skF_10' = '#skF_8'
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_14'),'#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_251,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_14'),'#skF_15')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_344,plain,(
    ! [A_118,C_119,B_120,D_121] :
      ( r2_hidden(A_118,C_119)
      | ~ r2_hidden(k4_tarski(A_118,B_120),k2_zfmisc_1(C_119,D_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_348,plain,(
    r2_hidden('#skF_12',k1_tarski('#skF_14')) ),
    inference(resolution,[status(thm)],[c_251,c_344])).

tff(c_32,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_353,plain,(
    '#skF_14' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_348,c_32])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_353])).

tff(c_360,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_14'),'#skF_15')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_98,plain,
    ( r2_hidden('#skF_9','#skF_11')
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_14'),'#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_387,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_14'),'#skF_15')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_387])).

tff(c_389,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_4435,plain,(
    ! [A_475,B_476,C_477,D_478] :
      ( r2_hidden(k4_tarski(A_475,B_476),k2_zfmisc_1(C_477,D_478))
      | ~ r2_hidden(B_476,D_478)
      | ~ r2_hidden(A_475,C_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_359,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_96,plain,
    ( ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1(k1_tarski('#skF_10'),'#skF_11'))
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_14'),'#skF_15')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_558,plain,
    ( ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_11'))
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_14'),'#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_96])).

tff(c_559,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_558])).

tff(c_4443,plain,
    ( ~ r2_hidden('#skF_9','#skF_11')
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_4435,c_559])).

tff(c_4457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_389,c_4443])).

tff(c_4459,plain,(
    '#skF_14' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_4844,plain,
    ( r2_hidden('#skF_9','#skF_11')
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),'#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_98])).

tff(c_4845,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),'#skF_15')) ),
    inference(splitLeft,[status(thm)],[c_4844])).

tff(c_4458,plain,
    ( ~ r2_hidden('#skF_13','#skF_15')
    | '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_4464,plain,(
    ~ r2_hidden('#skF_13','#skF_15') ),
    inference(splitLeft,[status(thm)],[c_4458])).

tff(c_4518,plain,
    ( '#skF_10' = '#skF_8'
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),'#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_100])).

tff(c_4519,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),'#skF_15')) ),
    inference(splitLeft,[status(thm)],[c_4518])).

tff(c_4821,plain,(
    ! [B_548,D_549,A_550,C_551] :
      ( r2_hidden(B_548,D_549)
      | ~ r2_hidden(k4_tarski(A_550,B_548),k2_zfmisc_1(C_551,D_549)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4824,plain,(
    r2_hidden('#skF_13','#skF_15') ),
    inference(resolution,[status(thm)],[c_4519,c_4821])).

tff(c_4828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4464,c_4824])).

tff(c_4830,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),'#skF_15')) ),
    inference(splitRight,[status(thm)],[c_4518])).

tff(c_4872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4845,c_4830])).

tff(c_4873,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_4844])).

tff(c_8671,plain,(
    ! [A_902,B_903,C_904,D_905] :
      ( r2_hidden(k4_tarski(A_902,B_903),k2_zfmisc_1(C_904,D_905))
      | ~ r2_hidden(B_903,D_905)
      | ~ r2_hidden(A_902,C_904) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4829,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4518])).

tff(c_4978,plain,
    ( ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_11'))
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),k2_zfmisc_1(k1_tarski('#skF_12'),'#skF_15')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_4829,c_96])).

tff(c_4979,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_4830,c_4978])).

tff(c_8679,plain,
    ( ~ r2_hidden('#skF_9','#skF_11')
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_8671,c_4979])).

tff(c_8693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4873,c_8679])).

tff(c_8695,plain,(
    r2_hidden('#skF_13','#skF_15') ),
    inference(splitRight,[status(thm)],[c_4458])).

tff(c_92,plain,
    ( r2_hidden('#skF_9','#skF_11')
    | ~ r2_hidden('#skF_13','#skF_15')
    | '#skF_14' != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8702,plain,(
    r2_hidden('#skF_9','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_8695,c_92])).

tff(c_10843,plain,(
    ! [A_1130,B_1131,C_1132,D_1133] :
      ( r2_hidden(k4_tarski(A_1130,B_1131),k2_zfmisc_1(C_1132,D_1133))
      | ~ r2_hidden(B_1131,D_1133)
      | ~ r2_hidden(A_1130,C_1132) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8694,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4458])).

tff(c_90,plain,
    ( ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1(k1_tarski('#skF_10'),'#skF_11'))
    | ~ r2_hidden('#skF_13','#skF_15')
    | '#skF_14' != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8961,plain,(
    ~ r2_hidden(k4_tarski('#skF_8','#skF_9'),k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4459,c_8695,c_8694,c_90])).

tff(c_10851,plain,
    ( ~ r2_hidden('#skF_9','#skF_11')
    | ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_10843,c_8961])).

tff(c_10862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8702,c_10851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.41/2.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.76  
% 7.41/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.76  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_11 > #skF_15 > #skF_10 > #skF_14 > #skF_2 > #skF_13 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 7.41/2.76  
% 7.41/2.76  %Foreground sorts:
% 7.41/2.76  
% 7.41/2.76  
% 7.41/2.76  %Background operators:
% 7.41/2.76  
% 7.41/2.76  
% 7.41/2.76  %Foreground operators:
% 7.41/2.76  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.41/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.41/2.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.41/2.76  tff('#skF_11', type, '#skF_11': $i).
% 7.41/2.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.41/2.76  tff('#skF_15', type, '#skF_15': $i).
% 7.41/2.76  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.41/2.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.41/2.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.41/2.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.41/2.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.41/2.76  tff('#skF_10', type, '#skF_10': $i).
% 7.41/2.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.41/2.76  tff('#skF_14', type, '#skF_14': $i).
% 7.41/2.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.41/2.76  tff('#skF_13', type, '#skF_13': $i).
% 7.41/2.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.41/2.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.41/2.76  tff('#skF_9', type, '#skF_9': $i).
% 7.41/2.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.41/2.76  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.41/2.76  tff('#skF_8', type, '#skF_8': $i).
% 7.41/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.41/2.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.41/2.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.41/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.41/2.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.41/2.76  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.41/2.76  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.41/2.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.41/2.76  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.41/2.76  tff('#skF_12', type, '#skF_12': $i).
% 7.41/2.76  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.41/2.76  
% 7.41/2.78  tff(f_54, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 7.41/2.78  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 7.41/2.78  tff(f_81, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 7.41/2.78  tff(c_34, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.41/2.78  tff(c_94, plain, ('#skF_10'='#skF_8' | ~r2_hidden('#skF_13', '#skF_15') | '#skF_14'!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.41/2.78  tff(c_131, plain, ('#skF_14'!='#skF_12'), inference(splitLeft, [status(thm)], [c_94])).
% 7.41/2.78  tff(c_100, plain, ('#skF_10'='#skF_8' | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_14'), '#skF_15'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.41/2.78  tff(c_251, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_14'), '#skF_15'))), inference(splitLeft, [status(thm)], [c_100])).
% 7.41/2.78  tff(c_344, plain, (![A_118, C_119, B_120, D_121]: (r2_hidden(A_118, C_119) | ~r2_hidden(k4_tarski(A_118, B_120), k2_zfmisc_1(C_119, D_121)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.41/2.78  tff(c_348, plain, (r2_hidden('#skF_12', k1_tarski('#skF_14'))), inference(resolution, [status(thm)], [c_251, c_344])).
% 7.41/2.78  tff(c_32, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.41/2.78  tff(c_353, plain, ('#skF_14'='#skF_12'), inference(resolution, [status(thm)], [c_348, c_32])).
% 7.41/2.78  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_353])).
% 7.41/2.78  tff(c_360, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_14'), '#skF_15'))), inference(splitRight, [status(thm)], [c_100])).
% 7.41/2.78  tff(c_98, plain, (r2_hidden('#skF_9', '#skF_11') | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_14'), '#skF_15'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.41/2.78  tff(c_387, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_14'), '#skF_15'))), inference(splitLeft, [status(thm)], [c_98])).
% 7.41/2.78  tff(c_388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_360, c_387])).
% 7.41/2.78  tff(c_389, plain, (r2_hidden('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_98])).
% 7.41/2.78  tff(c_4435, plain, (![A_475, B_476, C_477, D_478]: (r2_hidden(k4_tarski(A_475, B_476), k2_zfmisc_1(C_477, D_478)) | ~r2_hidden(B_476, D_478) | ~r2_hidden(A_475, C_477))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.41/2.78  tff(c_359, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_100])).
% 7.41/2.78  tff(c_96, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1(k1_tarski('#skF_10'), '#skF_11')) | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_14'), '#skF_15'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.41/2.78  tff(c_558, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_11')) | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_14'), '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_96])).
% 7.41/2.78  tff(c_559, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_360, c_558])).
% 7.41/2.78  tff(c_4443, plain, (~r2_hidden('#skF_9', '#skF_11') | ~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_4435, c_559])).
% 7.41/2.78  tff(c_4457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_389, c_4443])).
% 7.41/2.78  tff(c_4459, plain, ('#skF_14'='#skF_12'), inference(splitRight, [status(thm)], [c_94])).
% 7.41/2.78  tff(c_4844, plain, (r2_hidden('#skF_9', '#skF_11') | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_98])).
% 7.41/2.78  tff(c_4845, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), '#skF_15'))), inference(splitLeft, [status(thm)], [c_4844])).
% 7.41/2.78  tff(c_4458, plain, (~r2_hidden('#skF_13', '#skF_15') | '#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_94])).
% 7.41/2.78  tff(c_4464, plain, (~r2_hidden('#skF_13', '#skF_15')), inference(splitLeft, [status(thm)], [c_4458])).
% 7.41/2.78  tff(c_4518, plain, ('#skF_10'='#skF_8' | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_100])).
% 7.41/2.78  tff(c_4519, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), '#skF_15'))), inference(splitLeft, [status(thm)], [c_4518])).
% 7.41/2.78  tff(c_4821, plain, (![B_548, D_549, A_550, C_551]: (r2_hidden(B_548, D_549) | ~r2_hidden(k4_tarski(A_550, B_548), k2_zfmisc_1(C_551, D_549)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.41/2.78  tff(c_4824, plain, (r2_hidden('#skF_13', '#skF_15')), inference(resolution, [status(thm)], [c_4519, c_4821])).
% 7.41/2.78  tff(c_4828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4464, c_4824])).
% 7.41/2.78  tff(c_4830, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), '#skF_15'))), inference(splitRight, [status(thm)], [c_4518])).
% 7.41/2.78  tff(c_4872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4845, c_4830])).
% 7.41/2.78  tff(c_4873, plain, (r2_hidden('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_4844])).
% 7.41/2.78  tff(c_8671, plain, (![A_902, B_903, C_904, D_905]: (r2_hidden(k4_tarski(A_902, B_903), k2_zfmisc_1(C_904, D_905)) | ~r2_hidden(B_903, D_905) | ~r2_hidden(A_902, C_904))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.41/2.78  tff(c_4829, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_4518])).
% 7.41/2.78  tff(c_4978, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_11')) | r2_hidden(k4_tarski('#skF_12', '#skF_13'), k2_zfmisc_1(k1_tarski('#skF_12'), '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_4829, c_96])).
% 7.41/2.78  tff(c_4979, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_4830, c_4978])).
% 7.41/2.78  tff(c_8679, plain, (~r2_hidden('#skF_9', '#skF_11') | ~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_8671, c_4979])).
% 7.41/2.78  tff(c_8693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_4873, c_8679])).
% 7.41/2.78  tff(c_8695, plain, (r2_hidden('#skF_13', '#skF_15')), inference(splitRight, [status(thm)], [c_4458])).
% 7.41/2.78  tff(c_92, plain, (r2_hidden('#skF_9', '#skF_11') | ~r2_hidden('#skF_13', '#skF_15') | '#skF_14'!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.41/2.78  tff(c_8702, plain, (r2_hidden('#skF_9', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_8695, c_92])).
% 7.41/2.78  tff(c_10843, plain, (![A_1130, B_1131, C_1132, D_1133]: (r2_hidden(k4_tarski(A_1130, B_1131), k2_zfmisc_1(C_1132, D_1133)) | ~r2_hidden(B_1131, D_1133) | ~r2_hidden(A_1130, C_1132))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.41/2.78  tff(c_8694, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_4458])).
% 7.41/2.78  tff(c_90, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1(k1_tarski('#skF_10'), '#skF_11')) | ~r2_hidden('#skF_13', '#skF_15') | '#skF_14'!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.41/2.78  tff(c_8961, plain, (~r2_hidden(k4_tarski('#skF_8', '#skF_9'), k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_4459, c_8695, c_8694, c_90])).
% 7.41/2.78  tff(c_10851, plain, (~r2_hidden('#skF_9', '#skF_11') | ~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_10843, c_8961])).
% 7.41/2.78  tff(c_10862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_8702, c_10851])).
% 7.41/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/2.78  
% 7.41/2.78  Inference rules
% 7.41/2.78  ----------------------
% 7.41/2.78  #Ref     : 0
% 7.41/2.78  #Sup     : 2328
% 7.41/2.78  #Fact    : 0
% 7.41/2.78  #Define  : 0
% 7.41/2.78  #Split   : 15
% 7.41/2.78  #Chain   : 0
% 7.41/2.78  #Close   : 0
% 7.41/2.78  
% 7.41/2.78  Ordering : KBO
% 7.41/2.78  
% 7.41/2.78  Simplification rules
% 7.41/2.78  ----------------------
% 7.41/2.78  #Subsume      : 142
% 7.41/2.78  #Demod        : 375
% 7.41/2.78  #Tautology    : 382
% 7.41/2.78  #SimpNegUnit  : 5
% 7.41/2.78  #BackRed      : 0
% 7.41/2.78  
% 7.41/2.78  #Partial instantiations: 0
% 7.41/2.78  #Strategies tried      : 1
% 7.41/2.78  
% 7.41/2.78  Timing (in seconds)
% 7.41/2.78  ----------------------
% 7.41/2.78  Preprocessing        : 0.34
% 7.41/2.78  Parsing              : 0.17
% 7.41/2.78  CNF conversion       : 0.03
% 7.41/2.78  Main loop            : 1.68
% 7.41/2.78  Inferencing          : 0.52
% 7.41/2.78  Reduction            : 0.57
% 7.41/2.78  Demodulation         : 0.43
% 7.41/2.78  BG Simplification    : 0.07
% 7.41/2.78  Subsumption          : 0.39
% 7.41/2.78  Abstraction          : 0.06
% 7.41/2.78  MUC search           : 0.00
% 7.41/2.78  Cooper               : 0.00
% 7.41/2.78  Total                : 2.05
% 7.41/2.78  Index Insertion      : 0.00
% 7.41/2.78  Index Deletion       : 0.00
% 7.41/2.78  Index Matching       : 0.00
% 7.41/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
