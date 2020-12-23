%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:03 EST 2020

% Result     : Theorem 11.20s
% Output     : CNFRefutation 11.22s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 189 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 345 expanded)
%              Number of equality atoms :   32 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_56,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_93,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_70,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_64,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_62,plain,(
    r1_xboole_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_31342,plain,(
    ! [A_14288,B_14289,C_14290] :
      ( ~ r1_xboole_0(A_14288,B_14289)
      | ~ r2_hidden(C_14290,B_14289)
      | ~ r2_hidden(C_14290,A_14288) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31358,plain,(
    ! [C_14291] :
      ( ~ r2_hidden(C_14291,'#skF_6')
      | ~ r2_hidden(C_14291,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_31342])).

tff(c_31377,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_31358])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k3_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),B_11)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_749,plain,(
    ! [A_114,B_115,C_116] :
      ( ~ r1_xboole_0(A_114,B_115)
      | ~ r2_hidden(C_116,B_115)
      | ~ r2_hidden(C_116,A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_762,plain,(
    ! [C_117] :
      ( ~ r2_hidden(C_117,'#skF_6')
      | ~ r2_hidden(C_117,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_749])).

tff(c_814,plain,(
    ! [A_121] :
      ( ~ r2_hidden('#skF_2'(A_121,'#skF_7'),'#skF_6')
      | r1_xboole_0(A_121,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16,c_762])).

tff(c_819,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_18,c_814])).

tff(c_793,plain,(
    ! [A_118,C_119,B_120] :
      ( ~ r1_xboole_0(A_118,C_119)
      | ~ r1_xboole_0(A_118,B_120)
      | r1_xboole_0(A_118,k2_xboole_0(B_120,C_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22337,plain,(
    ! [A_10892,B_10893,C_10894] :
      ( k3_xboole_0(A_10892,k2_xboole_0(B_10893,C_10894)) = k1_xboole_0
      | ~ r1_xboole_0(A_10892,C_10894)
      | ~ r1_xboole_0(A_10892,B_10893) ) ),
    inference(resolution,[status(thm)],[c_793,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(A_53,B_54)
      | k3_xboole_0(A_53,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_5','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_177,plain,(
    k3_xboole_0(k2_xboole_0('#skF_5','#skF_7'),'#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_171,c_60])).

tff(c_180,plain,(
    k3_xboole_0('#skF_6',k2_xboole_0('#skF_5','#skF_7')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_22416,plain,
    ( ~ r1_xboole_0('#skF_6','#skF_7')
    | ~ r1_xboole_0('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_22337,c_180])).

tff(c_22465,plain,(
    ~ r1_xboole_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_22416])).

tff(c_22485,plain,(
    k3_xboole_0('#skF_6','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_22465])).

tff(c_66,plain,(
    r1_tarski(k3_xboole_0('#skF_5','#skF_6'),k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_68,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_5'),k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_247,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_254,plain,
    ( k3_xboole_0('#skF_6','#skF_5') = k1_tarski('#skF_8')
    | ~ r1_tarski(k1_tarski('#skF_8'),k3_xboole_0('#skF_6','#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_247])).

tff(c_260,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),k3_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_523,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    ! [C_31,A_27] :
      ( C_31 = A_27
      | ~ r2_hidden(C_31,k1_tarski(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1433,plain,(
    ! [A_2103,B_2104] :
      ( '#skF_1'(k1_tarski(A_2103),B_2104) = A_2103
      | r1_tarski(k1_tarski(A_2103),B_2104) ) ),
    inference(resolution,[status(thm)],[c_523,c_40])).

tff(c_1523,plain,(
    '#skF_1'(k1_tarski('#skF_8'),k3_xboole_0('#skF_6','#skF_5')) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1433,c_260])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1532,plain,
    ( ~ r2_hidden('#skF_8',k3_xboole_0('#skF_6','#skF_5'))
    | r1_tarski(k1_tarski('#skF_8'),k3_xboole_0('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1523,c_6])).

tff(c_1582,plain,(
    ~ r2_hidden('#skF_8',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_1532])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_553,plain,(
    ! [C_90,B_91,A_92] :
      ( r2_hidden(C_90,B_91)
      | ~ r2_hidden(C_90,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3523,plain,(
    ! [A_3383,B_3384,B_3385] :
      ( r2_hidden('#skF_1'(A_3383,B_3384),B_3385)
      | ~ r1_tarski(A_3383,B_3385)
      | r1_tarski(A_3383,B_3384) ) ),
    inference(resolution,[status(thm)],[c_8,c_553])).

tff(c_30764,plain,(
    ! [A_14155,A_14156,B_14157] :
      ( A_14155 = '#skF_1'(A_14156,B_14157)
      | ~ r1_tarski(A_14156,k1_tarski(A_14155))
      | r1_tarski(A_14156,B_14157) ) ),
    inference(resolution,[status(thm)],[c_3523,c_40])).

tff(c_30796,plain,(
    ! [B_14184] :
      ( '#skF_1'(k3_xboole_0('#skF_6','#skF_5'),B_14184) = '#skF_8'
      | r1_tarski(k3_xboole_0('#skF_6','#skF_5'),B_14184) ) ),
    inference(resolution,[status(thm)],[c_68,c_30764])).

tff(c_32,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_129,plain,(
    ! [A_23] : k3_xboole_0(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_121])).

tff(c_273,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_291,plain,(
    ! [A_70,B_71] : r1_tarski(k3_xboole_0(A_70,B_71),A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_28])).

tff(c_314,plain,(
    ! [A_72] : r1_tarski(k1_xboole_0,A_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_291])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(B_16,A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_317,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ r1_tarski(A_72,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_314,c_20])).

tff(c_30885,plain,
    ( k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0
    | '#skF_1'(k3_xboole_0('#skF_6','#skF_5'),k1_xboole_0) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30796,c_317])).

tff(c_30921,plain,(
    '#skF_1'(k3_xboole_0('#skF_6','#skF_5'),k1_xboole_0) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_22485,c_30885])).

tff(c_30932,plain,
    ( r2_hidden('#skF_8',k3_xboole_0('#skF_6','#skF_5'))
    | r1_tarski(k3_xboole_0('#skF_6','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30921,c_8])).

tff(c_30940,plain,(
    r1_tarski(k3_xboole_0('#skF_6','#skF_5'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_1582,c_30932])).

tff(c_30965,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30940,c_317])).

tff(c_30983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22485,c_30965])).

tff(c_30984,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_31195,plain,(
    ! [A_14282,B_14283] : k4_xboole_0(A_14282,k4_xboole_0(A_14282,B_14283)) = k3_xboole_0(A_14282,B_14283) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_31381,plain,(
    ! [A_14292,B_14293] : r1_tarski(k3_xboole_0(A_14292,B_14293),A_14292) ),
    inference(superposition,[status(thm),theory(equality)],[c_31195,c_28])).

tff(c_31386,plain,(
    r1_tarski(k1_tarski('#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_30984,c_31381])).

tff(c_42,plain,(
    ! [C_31] : r2_hidden(C_31,k1_tarski(C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_31295,plain,(
    ! [C_14284,B_14285,A_14286] :
      ( r2_hidden(C_14284,B_14285)
      | ~ r2_hidden(C_14284,A_14286)
      | ~ r1_tarski(A_14286,B_14285) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_31895,plain,(
    ! [C_15760,B_15761] :
      ( r2_hidden(C_15760,B_15761)
      | ~ r1_tarski(k1_tarski(C_15760),B_15761) ) ),
    inference(resolution,[status(thm)],[c_42,c_31295])).

tff(c_31905,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_31386,c_31895])).

tff(c_31914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31377,c_31905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.20/4.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.22/4.04  
% 11.22/4.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.22/4.04  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 11.22/4.04  
% 11.22/4.04  %Foreground sorts:
% 11.22/4.04  
% 11.22/4.04  
% 11.22/4.04  %Background operators:
% 11.22/4.04  
% 11.22/4.04  
% 11.22/4.04  %Foreground operators:
% 11.22/4.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.22/4.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.22/4.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.22/4.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.22/4.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.22/4.04  tff('#skF_7', type, '#skF_7': $i).
% 11.22/4.04  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.22/4.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.22/4.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.22/4.04  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.22/4.04  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.22/4.04  tff('#skF_5', type, '#skF_5': $i).
% 11.22/4.04  tff('#skF_6', type, '#skF_6': $i).
% 11.22/4.04  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.22/4.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.22/4.04  tff('#skF_8', type, '#skF_8': $i).
% 11.22/4.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.22/4.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.22/4.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.22/4.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.22/4.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.22/4.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.22/4.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.22/4.04  
% 11.22/4.06  tff(f_113, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 11.22/4.06  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.22/4.06  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.22/4.06  tff(f_86, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 11.22/4.06  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.22/4.06  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.22/4.06  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.22/4.06  tff(f_93, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 11.22/4.06  tff(f_70, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.22/4.06  tff(f_68, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.22/4.06  tff(f_66, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 11.22/4.06  tff(c_64, plain, (r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.22/4.06  tff(c_62, plain, (r1_xboole_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.22/4.06  tff(c_31342, plain, (![A_14288, B_14289, C_14290]: (~r1_xboole_0(A_14288, B_14289) | ~r2_hidden(C_14290, B_14289) | ~r2_hidden(C_14290, A_14288))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.22/4.06  tff(c_31358, plain, (![C_14291]: (~r2_hidden(C_14291, '#skF_6') | ~r2_hidden(C_14291, '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_31342])).
% 11.22/4.06  tff(c_31377, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_31358])).
% 11.22/4.06  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k3_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.22/4.06  tff(c_18, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.22/4.06  tff(c_16, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), B_11) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.22/4.06  tff(c_749, plain, (![A_114, B_115, C_116]: (~r1_xboole_0(A_114, B_115) | ~r2_hidden(C_116, B_115) | ~r2_hidden(C_116, A_114))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.22/4.06  tff(c_762, plain, (![C_117]: (~r2_hidden(C_117, '#skF_6') | ~r2_hidden(C_117, '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_749])).
% 11.22/4.06  tff(c_814, plain, (![A_121]: (~r2_hidden('#skF_2'(A_121, '#skF_7'), '#skF_6') | r1_xboole_0(A_121, '#skF_7'))), inference(resolution, [status(thm)], [c_16, c_762])).
% 11.22/4.06  tff(c_819, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_18, c_814])).
% 11.22/4.06  tff(c_793, plain, (![A_118, C_119, B_120]: (~r1_xboole_0(A_118, C_119) | ~r1_xboole_0(A_118, B_120) | r1_xboole_0(A_118, k2_xboole_0(B_120, C_119)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.22/4.06  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.22/4.06  tff(c_22337, plain, (![A_10892, B_10893, C_10894]: (k3_xboole_0(A_10892, k2_xboole_0(B_10893, C_10894))=k1_xboole_0 | ~r1_xboole_0(A_10892, C_10894) | ~r1_xboole_0(A_10892, B_10893))), inference(resolution, [status(thm)], [c_793, c_10])).
% 11.22/4.06  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.22/4.06  tff(c_171, plain, (![A_53, B_54]: (r1_xboole_0(A_53, B_54) | k3_xboole_0(A_53, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.22/4.06  tff(c_60, plain, (~r1_xboole_0(k2_xboole_0('#skF_5', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.22/4.06  tff(c_177, plain, (k3_xboole_0(k2_xboole_0('#skF_5', '#skF_7'), '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_171, c_60])).
% 11.22/4.06  tff(c_180, plain, (k3_xboole_0('#skF_6', k2_xboole_0('#skF_5', '#skF_7'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_177])).
% 11.22/4.06  tff(c_22416, plain, (~r1_xboole_0('#skF_6', '#skF_7') | ~r1_xboole_0('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_22337, c_180])).
% 11.22/4.06  tff(c_22465, plain, (~r1_xboole_0('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_819, c_22416])).
% 11.22/4.06  tff(c_22485, plain, (k3_xboole_0('#skF_6', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_22465])).
% 11.22/4.06  tff(c_66, plain, (r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.22/4.06  tff(c_68, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_5'), k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_66])).
% 11.22/4.06  tff(c_247, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.22/4.06  tff(c_254, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_tarski('#skF_8') | ~r1_tarski(k1_tarski('#skF_8'), k3_xboole_0('#skF_6', '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_247])).
% 11.22/4.06  tff(c_260, plain, (~r1_tarski(k1_tarski('#skF_8'), k3_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_254])).
% 11.22/4.06  tff(c_523, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85, B_86), A_85) | r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.22/4.06  tff(c_40, plain, (![C_31, A_27]: (C_31=A_27 | ~r2_hidden(C_31, k1_tarski(A_27)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.22/4.06  tff(c_1433, plain, (![A_2103, B_2104]: ('#skF_1'(k1_tarski(A_2103), B_2104)=A_2103 | r1_tarski(k1_tarski(A_2103), B_2104))), inference(resolution, [status(thm)], [c_523, c_40])).
% 11.22/4.06  tff(c_1523, plain, ('#skF_1'(k1_tarski('#skF_8'), k3_xboole_0('#skF_6', '#skF_5'))='#skF_8'), inference(resolution, [status(thm)], [c_1433, c_260])).
% 11.22/4.06  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.22/4.06  tff(c_1532, plain, (~r2_hidden('#skF_8', k3_xboole_0('#skF_6', '#skF_5')) | r1_tarski(k1_tarski('#skF_8'), k3_xboole_0('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1523, c_6])).
% 11.22/4.06  tff(c_1582, plain, (~r2_hidden('#skF_8', k3_xboole_0('#skF_6', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_260, c_1532])).
% 11.22/4.06  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.22/4.06  tff(c_553, plain, (![C_90, B_91, A_92]: (r2_hidden(C_90, B_91) | ~r2_hidden(C_90, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.22/4.06  tff(c_3523, plain, (![A_3383, B_3384, B_3385]: (r2_hidden('#skF_1'(A_3383, B_3384), B_3385) | ~r1_tarski(A_3383, B_3385) | r1_tarski(A_3383, B_3384))), inference(resolution, [status(thm)], [c_8, c_553])).
% 11.22/4.06  tff(c_30764, plain, (![A_14155, A_14156, B_14157]: (A_14155='#skF_1'(A_14156, B_14157) | ~r1_tarski(A_14156, k1_tarski(A_14155)) | r1_tarski(A_14156, B_14157))), inference(resolution, [status(thm)], [c_3523, c_40])).
% 11.22/4.06  tff(c_30796, plain, (![B_14184]: ('#skF_1'(k3_xboole_0('#skF_6', '#skF_5'), B_14184)='#skF_8' | r1_tarski(k3_xboole_0('#skF_6', '#skF_5'), B_14184))), inference(resolution, [status(thm)], [c_68, c_30764])).
% 11.22/4.06  tff(c_32, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.22/4.06  tff(c_121, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.22/4.06  tff(c_129, plain, (![A_23]: (k3_xboole_0(A_23, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_121])).
% 11.22/4.06  tff(c_273, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.22/4.06  tff(c_28, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.22/4.06  tff(c_291, plain, (![A_70, B_71]: (r1_tarski(k3_xboole_0(A_70, B_71), A_70))), inference(superposition, [status(thm), theory('equality')], [c_273, c_28])).
% 11.22/4.06  tff(c_314, plain, (![A_72]: (r1_tarski(k1_xboole_0, A_72))), inference(superposition, [status(thm), theory('equality')], [c_129, c_291])).
% 11.22/4.06  tff(c_20, plain, (![B_16, A_15]: (B_16=A_15 | ~r1_tarski(B_16, A_15) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.22/4.06  tff(c_317, plain, (![A_72]: (k1_xboole_0=A_72 | ~r1_tarski(A_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_314, c_20])).
% 11.22/4.06  tff(c_30885, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0 | '#skF_1'(k3_xboole_0('#skF_6', '#skF_5'), k1_xboole_0)='#skF_8'), inference(resolution, [status(thm)], [c_30796, c_317])).
% 11.22/4.06  tff(c_30921, plain, ('#skF_1'(k3_xboole_0('#skF_6', '#skF_5'), k1_xboole_0)='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_22485, c_30885])).
% 11.22/4.06  tff(c_30932, plain, (r2_hidden('#skF_8', k3_xboole_0('#skF_6', '#skF_5')) | r1_tarski(k3_xboole_0('#skF_6', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30921, c_8])).
% 11.22/4.06  tff(c_30940, plain, (r1_tarski(k3_xboole_0('#skF_6', '#skF_5'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_1582, c_30932])).
% 11.22/4.06  tff(c_30965, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30940, c_317])).
% 11.22/4.06  tff(c_30983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22485, c_30965])).
% 11.22/4.06  tff(c_30984, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_254])).
% 11.22/4.06  tff(c_31195, plain, (![A_14282, B_14283]: (k4_xboole_0(A_14282, k4_xboole_0(A_14282, B_14283))=k3_xboole_0(A_14282, B_14283))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.22/4.06  tff(c_31381, plain, (![A_14292, B_14293]: (r1_tarski(k3_xboole_0(A_14292, B_14293), A_14292))), inference(superposition, [status(thm), theory('equality')], [c_31195, c_28])).
% 11.22/4.06  tff(c_31386, plain, (r1_tarski(k1_tarski('#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_30984, c_31381])).
% 11.22/4.06  tff(c_42, plain, (![C_31]: (r2_hidden(C_31, k1_tarski(C_31)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 11.22/4.06  tff(c_31295, plain, (![C_14284, B_14285, A_14286]: (r2_hidden(C_14284, B_14285) | ~r2_hidden(C_14284, A_14286) | ~r1_tarski(A_14286, B_14285))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.22/4.06  tff(c_31895, plain, (![C_15760, B_15761]: (r2_hidden(C_15760, B_15761) | ~r1_tarski(k1_tarski(C_15760), B_15761))), inference(resolution, [status(thm)], [c_42, c_31295])).
% 11.22/4.06  tff(c_31905, plain, (r2_hidden('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_31386, c_31895])).
% 11.22/4.06  tff(c_31914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31377, c_31905])).
% 11.22/4.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.22/4.06  
% 11.22/4.06  Inference rules
% 11.22/4.06  ----------------------
% 11.22/4.06  #Ref     : 0
% 11.22/4.06  #Sup     : 5140
% 11.22/4.06  #Fact    : 10
% 11.22/4.06  #Define  : 0
% 11.22/4.06  #Split   : 9
% 11.22/4.06  #Chain   : 0
% 11.22/4.06  #Close   : 0
% 11.22/4.06  
% 11.22/4.06  Ordering : KBO
% 11.22/4.06  
% 11.22/4.06  Simplification rules
% 11.22/4.06  ----------------------
% 11.22/4.06  #Subsume      : 1694
% 11.22/4.06  #Demod        : 2075
% 11.22/4.06  #Tautology    : 1351
% 11.22/4.06  #SimpNegUnit  : 58
% 11.22/4.06  #BackRed      : 2
% 11.22/4.06  
% 11.22/4.06  #Partial instantiations: 9996
% 11.22/4.06  #Strategies tried      : 1
% 11.22/4.06  
% 11.22/4.06  Timing (in seconds)
% 11.22/4.06  ----------------------
% 11.22/4.06  Preprocessing        : 0.47
% 11.22/4.06  Parsing              : 0.29
% 11.22/4.06  CNF conversion       : 0.02
% 11.22/4.06  Main loop            : 2.77
% 11.22/4.06  Inferencing          : 0.87
% 11.22/4.06  Reduction            : 1.00
% 11.22/4.06  Demodulation         : 0.74
% 11.22/4.06  BG Simplification    : 0.09
% 11.22/4.06  Subsumption          : 0.62
% 11.22/4.06  Abstraction          : 0.12
% 11.22/4.06  MUC search           : 0.00
% 11.22/4.06  Cooper               : 0.00
% 11.22/4.06  Total                : 3.28
% 11.22/4.06  Index Insertion      : 0.00
% 11.22/4.06  Index Deletion       : 0.00
% 11.22/4.06  Index Matching       : 0.00
% 11.22/4.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
