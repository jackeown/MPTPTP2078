%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:36 EST 2020

% Result     : Theorem 9.09s
% Output     : CNFRefutation 9.37s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 264 expanded)
%              Number of leaves         :   36 ( 103 expanded)
%              Depth                    :   19
%              Number of atoms          :  139 ( 439 expanded)
%              Number of equality atoms :   64 ( 180 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_64,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_81,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_72,plain,
    ( k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6'
    | r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_191,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_30,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_192,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k4_xboole_0(B_70,A_69)) = k2_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_201,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k2_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_192])).

tff(c_204,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_201])).

tff(c_146,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [E_28,A_22,B_23] : r2_hidden(E_28,k1_enumset1(A_22,B_23,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_155,plain,(
    ! [B_59,A_58] : r2_hidden(B_59,k2_tarski(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_40])).

tff(c_95,plain,(
    ! [A_43,B_44] : r1_xboole_0(k4_xboole_0(A_43,B_44),B_44) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    ! [A_17] : r1_xboole_0(k1_xboole_0,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_95])).

tff(c_278,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,B_85)
      | ~ r2_hidden(C_86,A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_288,plain,(
    ! [C_87,A_88] :
      ( ~ r2_hidden(C_87,A_88)
      | ~ r2_hidden(C_87,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_98,c_278])).

tff(c_307,plain,(
    ! [B_59] : ~ r2_hidden(B_59,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_155,c_288])).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | r2_hidden('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_111,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_511,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden('#skF_1'(A_131,B_132,C_133),A_131)
      | r2_hidden('#skF_2'(A_131,B_132,C_133),C_133)
      | k3_xboole_0(A_131,B_132) = C_133 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_613,plain,(
    ! [B_134,C_135] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_134,C_135),C_135)
      | k3_xboole_0(k1_xboole_0,B_134) = C_135 ) ),
    inference(resolution,[status(thm)],[c_511,c_307])).

tff(c_663,plain,(
    ! [B_134] : k3_xboole_0(k1_xboole_0,B_134) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_613,c_307])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_13463,plain,(
    ! [A_29092,B_29093,A_29094,B_29095] :
      ( r2_hidden('#skF_2'(A_29092,B_29093,k3_xboole_0(A_29094,B_29095)),A_29094)
      | r2_hidden('#skF_1'(A_29092,B_29093,k3_xboole_0(A_29094,B_29095)),A_29092)
      | k3_xboole_0(A_29094,B_29095) = k3_xboole_0(A_29092,B_29093) ) ),
    inference(resolution,[status(thm)],[c_511,c_8])).

tff(c_13684,plain,(
    ! [A_29092,B_29093,B_134] :
      ( r2_hidden('#skF_2'(A_29092,B_29093,k3_xboole_0(k1_xboole_0,B_134)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_29092,B_29093,k1_xboole_0),A_29092)
      | k3_xboole_0(k1_xboole_0,B_134) = k3_xboole_0(A_29092,B_29093) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_13463])).

tff(c_13762,plain,(
    ! [A_29092,B_29093] :
      ( r2_hidden('#skF_2'(A_29092,B_29093,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_29092,B_29093,k1_xboole_0),A_29092)
      | k3_xboole_0(A_29092,B_29093) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_663,c_13684])).

tff(c_13764,plain,(
    ! [A_29291,B_29292] :
      ( r2_hidden('#skF_1'(A_29291,B_29292,k1_xboole_0),A_29291)
      | k3_xboole_0(A_29291,B_29292) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_13762])).

tff(c_62,plain,(
    ! [A_29] : k2_tarski(A_29,A_29) = k1_tarski(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_64,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_417,plain,(
    ! [E_109,C_110,B_111,A_112] :
      ( E_109 = C_110
      | E_109 = B_111
      | E_109 = A_112
      | ~ r2_hidden(E_109,k1_enumset1(A_112,B_111,C_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1181,plain,(
    ! [E_158,B_159,A_160] :
      ( E_158 = B_159
      | E_158 = A_160
      | E_158 = A_160
      | ~ r2_hidden(E_158,k2_tarski(A_160,B_159)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_417])).

tff(c_1230,plain,(
    ! [E_158,A_29] :
      ( E_158 = A_29
      | E_158 = A_29
      | E_158 = A_29
      | ~ r2_hidden(E_158,k1_tarski(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1181])).

tff(c_14074,plain,(
    ! [A_29687,B_29688] :
      ( '#skF_1'(k1_tarski(A_29687),B_29688,k1_xboole_0) = A_29687
      | k3_xboole_0(k1_tarski(A_29687),B_29688) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_13764,c_1230])).

tff(c_176,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_185,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_176])).

tff(c_14247,plain,(
    ! [B_29688,A_29687] :
      ( k4_xboole_0(B_29688,k1_tarski(A_29687)) = k5_xboole_0(B_29688,k1_xboole_0)
      | '#skF_1'(k1_tarski(A_29687),B_29688,k1_xboole_0) = A_29687 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14074,c_185])).

tff(c_14638,plain,(
    ! [B_30277,A_30278] :
      ( k4_xboole_0(B_30277,k1_tarski(A_30278)) = B_30277
      | '#skF_1'(k1_tarski(A_30278),B_30277,k1_xboole_0) = A_30278 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_14247])).

tff(c_14707,plain,(
    '#skF_1'(k1_tarski('#skF_7'),'#skF_6',k1_xboole_0) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_14638,c_191])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14719,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | r2_hidden('#skF_2'(k1_tarski('#skF_7'),'#skF_6',k1_xboole_0),k1_xboole_0)
    | k3_xboole_0(k1_tarski('#skF_7'),'#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14707,c_18])).

tff(c_14735,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | r2_hidden('#skF_2'(k1_tarski('#skF_7'),'#skF_6',k1_xboole_0),k1_xboole_0)
    | k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14719])).

tff(c_14736,plain,(
    k3_xboole_0('#skF_6',k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_111,c_14735])).

tff(c_28,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14862,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14736,c_28])).

tff(c_14919,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_14862])).

tff(c_14921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_14919])).

tff(c_14922,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_42,plain,(
    ! [E_28,A_22,C_24] : r2_hidden(E_28,k1_enumset1(A_22,E_28,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_164,plain,(
    ! [A_60,B_61] : r2_hidden(A_60,k2_tarski(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_42])).

tff(c_167,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_164])).

tff(c_14923,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6'
    | k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14924,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_7')) != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_14933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14923,c_14924])).

tff(c_14934,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_34,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14947,plain,(
    r1_xboole_0('#skF_8',k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14934,c_34])).

tff(c_15051,plain,(
    ! [A_30879,B_30880,C_30881] :
      ( ~ r1_xboole_0(A_30879,B_30880)
      | ~ r2_hidden(C_30881,B_30880)
      | ~ r2_hidden(C_30881,A_30879) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_15136,plain,(
    ! [C_30890] :
      ( ~ r2_hidden(C_30890,k1_tarski('#skF_9'))
      | ~ r2_hidden(C_30890,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14947,c_15051])).

tff(c_15148,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_167,c_15136])).

tff(c_15154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14922,c_15148])).

tff(c_15155,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_15200,plain,(
    ! [A_30896,B_30897] : k1_enumset1(A_30896,A_30896,B_30897) = k2_tarski(A_30896,B_30897) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_15218,plain,(
    ! [A_30898,B_30899] : r2_hidden(A_30898,k2_tarski(A_30898,B_30899)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15200,c_42])).

tff(c_15221,plain,(
    ! [A_29] : r2_hidden(A_29,k1_tarski(A_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_15218])).

tff(c_15156,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_15192,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15156,c_78])).

tff(c_15196,plain,(
    r1_xboole_0('#skF_8',k1_tarski('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15192,c_34])).

tff(c_15349,plain,(
    ! [A_30925,B_30926,C_30927] :
      ( ~ r1_xboole_0(A_30925,B_30926)
      | ~ r2_hidden(C_30927,B_30926)
      | ~ r2_hidden(C_30927,A_30925) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_15418,plain,(
    ! [C_30936] :
      ( ~ r2_hidden(C_30936,k1_tarski('#skF_9'))
      | ~ r2_hidden(C_30936,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_15196,c_15349])).

tff(c_15430,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_15221,c_15418])).

tff(c_15436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15155,c_15430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:07:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.09/3.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.09/3.28  
% 9.09/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.09/3.28  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_5
% 9.09/3.28  
% 9.09/3.28  %Foreground sorts:
% 9.09/3.28  
% 9.09/3.28  
% 9.09/3.28  %Background operators:
% 9.09/3.28  
% 9.09/3.28  
% 9.09/3.28  %Foreground operators:
% 9.09/3.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.09/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.09/3.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.09/3.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.09/3.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.09/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.09/3.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.09/3.28  tff('#skF_7', type, '#skF_7': $i).
% 9.09/3.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.09/3.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.09/3.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.09/3.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.09/3.28  tff('#skF_6', type, '#skF_6': $i).
% 9.09/3.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.09/3.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.09/3.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.09/3.28  tff('#skF_9', type, '#skF_9': $i).
% 9.09/3.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 9.09/3.28  tff('#skF_8', type, '#skF_8': $i).
% 9.09/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.09/3.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 9.09/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.09/3.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.09/3.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.09/3.28  
% 9.37/3.30  tff(f_98, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 9.37/3.30  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 9.37/3.30  tff(f_60, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 9.37/3.30  tff(f_64, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.37/3.30  tff(f_83, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 9.37/3.30  tff(f_79, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 9.37/3.30  tff(f_62, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.37/3.30  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.37/3.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.37/3.30  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 9.37/3.30  tff(f_81, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.37/3.30  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.37/3.30  tff(c_72, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6' | r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.37/3.30  tff(c_191, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_72])).
% 9.37/3.30  tff(c_30, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.37/3.30  tff(c_32, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.37/3.30  tff(c_192, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k4_xboole_0(B_70, A_69))=k2_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.37/3.30  tff(c_201, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k2_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_192])).
% 9.37/3.30  tff(c_204, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_201])).
% 9.37/3.30  tff(c_146, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.37/3.30  tff(c_40, plain, (![E_28, A_22, B_23]: (r2_hidden(E_28, k1_enumset1(A_22, B_23, E_28)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.37/3.30  tff(c_155, plain, (![B_59, A_58]: (r2_hidden(B_59, k2_tarski(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_40])).
% 9.37/3.30  tff(c_95, plain, (![A_43, B_44]: (r1_xboole_0(k4_xboole_0(A_43, B_44), B_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.37/3.30  tff(c_98, plain, (![A_17]: (r1_xboole_0(k1_xboole_0, A_17))), inference(superposition, [status(thm), theory('equality')], [c_32, c_95])).
% 9.37/3.30  tff(c_278, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, B_85) | ~r2_hidden(C_86, A_84))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.37/3.30  tff(c_288, plain, (![C_87, A_88]: (~r2_hidden(C_87, A_88) | ~r2_hidden(C_87, k1_xboole_0))), inference(resolution, [status(thm)], [c_98, c_278])).
% 9.37/3.30  tff(c_307, plain, (![B_59]: (~r2_hidden(B_59, k1_xboole_0))), inference(resolution, [status(thm)], [c_155, c_288])).
% 9.37/3.30  tff(c_74, plain, (~r2_hidden('#skF_7', '#skF_6') | r2_hidden('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.37/3.30  tff(c_111, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_74])).
% 9.37/3.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.37/3.30  tff(c_511, plain, (![A_131, B_132, C_133]: (r2_hidden('#skF_1'(A_131, B_132, C_133), A_131) | r2_hidden('#skF_2'(A_131, B_132, C_133), C_133) | k3_xboole_0(A_131, B_132)=C_133)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.37/3.30  tff(c_613, plain, (![B_134, C_135]: (r2_hidden('#skF_2'(k1_xboole_0, B_134, C_135), C_135) | k3_xboole_0(k1_xboole_0, B_134)=C_135)), inference(resolution, [status(thm)], [c_511, c_307])).
% 9.37/3.30  tff(c_663, plain, (![B_134]: (k3_xboole_0(k1_xboole_0, B_134)=k1_xboole_0)), inference(resolution, [status(thm)], [c_613, c_307])).
% 9.37/3.30  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.37/3.30  tff(c_13463, plain, (![A_29092, B_29093, A_29094, B_29095]: (r2_hidden('#skF_2'(A_29092, B_29093, k3_xboole_0(A_29094, B_29095)), A_29094) | r2_hidden('#skF_1'(A_29092, B_29093, k3_xboole_0(A_29094, B_29095)), A_29092) | k3_xboole_0(A_29094, B_29095)=k3_xboole_0(A_29092, B_29093))), inference(resolution, [status(thm)], [c_511, c_8])).
% 9.37/3.30  tff(c_13684, plain, (![A_29092, B_29093, B_134]: (r2_hidden('#skF_2'(A_29092, B_29093, k3_xboole_0(k1_xboole_0, B_134)), k1_xboole_0) | r2_hidden('#skF_1'(A_29092, B_29093, k1_xboole_0), A_29092) | k3_xboole_0(k1_xboole_0, B_134)=k3_xboole_0(A_29092, B_29093))), inference(superposition, [status(thm), theory('equality')], [c_663, c_13463])).
% 9.37/3.30  tff(c_13762, plain, (![A_29092, B_29093]: (r2_hidden('#skF_2'(A_29092, B_29093, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_29092, B_29093, k1_xboole_0), A_29092) | k3_xboole_0(A_29092, B_29093)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_663, c_663, c_13684])).
% 9.37/3.30  tff(c_13764, plain, (![A_29291, B_29292]: (r2_hidden('#skF_1'(A_29291, B_29292, k1_xboole_0), A_29291) | k3_xboole_0(A_29291, B_29292)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_307, c_13762])).
% 9.37/3.30  tff(c_62, plain, (![A_29]: (k2_tarski(A_29, A_29)=k1_tarski(A_29))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.37/3.30  tff(c_64, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.37/3.30  tff(c_417, plain, (![E_109, C_110, B_111, A_112]: (E_109=C_110 | E_109=B_111 | E_109=A_112 | ~r2_hidden(E_109, k1_enumset1(A_112, B_111, C_110)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.37/3.30  tff(c_1181, plain, (![E_158, B_159, A_160]: (E_158=B_159 | E_158=A_160 | E_158=A_160 | ~r2_hidden(E_158, k2_tarski(A_160, B_159)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_417])).
% 9.37/3.30  tff(c_1230, plain, (![E_158, A_29]: (E_158=A_29 | E_158=A_29 | E_158=A_29 | ~r2_hidden(E_158, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1181])).
% 9.37/3.30  tff(c_14074, plain, (![A_29687, B_29688]: ('#skF_1'(k1_tarski(A_29687), B_29688, k1_xboole_0)=A_29687 | k3_xboole_0(k1_tarski(A_29687), B_29688)=k1_xboole_0)), inference(resolution, [status(thm)], [c_13764, c_1230])).
% 9.37/3.30  tff(c_176, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.37/3.30  tff(c_185, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_176])).
% 9.37/3.30  tff(c_14247, plain, (![B_29688, A_29687]: (k4_xboole_0(B_29688, k1_tarski(A_29687))=k5_xboole_0(B_29688, k1_xboole_0) | '#skF_1'(k1_tarski(A_29687), B_29688, k1_xboole_0)=A_29687)), inference(superposition, [status(thm), theory('equality')], [c_14074, c_185])).
% 9.37/3.30  tff(c_14638, plain, (![B_30277, A_30278]: (k4_xboole_0(B_30277, k1_tarski(A_30278))=B_30277 | '#skF_1'(k1_tarski(A_30278), B_30277, k1_xboole_0)=A_30278)), inference(demodulation, [status(thm), theory('equality')], [c_204, c_14247])).
% 9.37/3.30  tff(c_14707, plain, ('#skF_1'(k1_tarski('#skF_7'), '#skF_6', k1_xboole_0)='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_14638, c_191])).
% 9.37/3.30  tff(c_18, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.37/3.30  tff(c_14719, plain, (r2_hidden('#skF_7', '#skF_6') | r2_hidden('#skF_2'(k1_tarski('#skF_7'), '#skF_6', k1_xboole_0), k1_xboole_0) | k3_xboole_0(k1_tarski('#skF_7'), '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14707, c_18])).
% 9.37/3.30  tff(c_14735, plain, (r2_hidden('#skF_7', '#skF_6') | r2_hidden('#skF_2'(k1_tarski('#skF_7'), '#skF_6', k1_xboole_0), k1_xboole_0) | k3_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14719])).
% 9.37/3.30  tff(c_14736, plain, (k3_xboole_0('#skF_6', k1_tarski('#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_307, c_111, c_14735])).
% 9.37/3.30  tff(c_28, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.37/3.30  tff(c_14862, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14736, c_28])).
% 9.37/3.30  tff(c_14919, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_14862])).
% 9.37/3.30  tff(c_14921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_14919])).
% 9.37/3.30  tff(c_14922, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_72])).
% 9.37/3.30  tff(c_42, plain, (![E_28, A_22, C_24]: (r2_hidden(E_28, k1_enumset1(A_22, E_28, C_24)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.37/3.30  tff(c_164, plain, (![A_60, B_61]: (r2_hidden(A_60, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_42])).
% 9.37/3.30  tff(c_167, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_164])).
% 9.37/3.30  tff(c_14923, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))='#skF_6'), inference(splitRight, [status(thm)], [c_72])).
% 9.37/3.30  tff(c_76, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6' | k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.37/3.30  tff(c_14924, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_7'))!='#skF_6'), inference(splitLeft, [status(thm)], [c_76])).
% 9.37/3.30  tff(c_14933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14923, c_14924])).
% 9.37/3.30  tff(c_14934, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(splitRight, [status(thm)], [c_76])).
% 9.37/3.30  tff(c_34, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.37/3.30  tff(c_14947, plain, (r1_xboole_0('#skF_8', k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_14934, c_34])).
% 9.37/3.30  tff(c_15051, plain, (![A_30879, B_30880, C_30881]: (~r1_xboole_0(A_30879, B_30880) | ~r2_hidden(C_30881, B_30880) | ~r2_hidden(C_30881, A_30879))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.37/3.30  tff(c_15136, plain, (![C_30890]: (~r2_hidden(C_30890, k1_tarski('#skF_9')) | ~r2_hidden(C_30890, '#skF_8'))), inference(resolution, [status(thm)], [c_14947, c_15051])).
% 9.37/3.30  tff(c_15148, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_167, c_15136])).
% 9.37/3.30  tff(c_15154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14922, c_15148])).
% 9.37/3.30  tff(c_15155, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_74])).
% 9.37/3.30  tff(c_15200, plain, (![A_30896, B_30897]: (k1_enumset1(A_30896, A_30896, B_30897)=k2_tarski(A_30896, B_30897))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.37/3.30  tff(c_15218, plain, (![A_30898, B_30899]: (r2_hidden(A_30898, k2_tarski(A_30898, B_30899)))), inference(superposition, [status(thm), theory('equality')], [c_15200, c_42])).
% 9.37/3.30  tff(c_15221, plain, (![A_29]: (r2_hidden(A_29, k1_tarski(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_15218])).
% 9.37/3.30  tff(c_15156, plain, (r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 9.37/3.30  tff(c_78, plain, (~r2_hidden('#skF_7', '#skF_6') | k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.37/3.30  tff(c_15192, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_15156, c_78])).
% 9.37/3.30  tff(c_15196, plain, (r1_xboole_0('#skF_8', k1_tarski('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_15192, c_34])).
% 9.37/3.30  tff(c_15349, plain, (![A_30925, B_30926, C_30927]: (~r1_xboole_0(A_30925, B_30926) | ~r2_hidden(C_30927, B_30926) | ~r2_hidden(C_30927, A_30925))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.37/3.30  tff(c_15418, plain, (![C_30936]: (~r2_hidden(C_30936, k1_tarski('#skF_9')) | ~r2_hidden(C_30936, '#skF_8'))), inference(resolution, [status(thm)], [c_15196, c_15349])).
% 9.37/3.30  tff(c_15430, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_15221, c_15418])).
% 9.37/3.30  tff(c_15436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15155, c_15430])).
% 9.37/3.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.37/3.30  
% 9.37/3.30  Inference rules
% 9.37/3.30  ----------------------
% 9.37/3.30  #Ref     : 0
% 9.37/3.30  #Sup     : 2600
% 9.37/3.30  #Fact    : 22
% 9.37/3.30  #Define  : 0
% 9.37/3.30  #Split   : 3
% 9.37/3.30  #Chain   : 0
% 9.37/3.30  #Close   : 0
% 9.37/3.30  
% 9.37/3.30  Ordering : KBO
% 9.37/3.30  
% 9.37/3.30  Simplification rules
% 9.37/3.30  ----------------------
% 9.37/3.30  #Subsume      : 457
% 9.37/3.30  #Demod        : 706
% 9.37/3.30  #Tautology    : 536
% 9.37/3.30  #SimpNegUnit  : 105
% 9.37/3.30  #BackRed      : 1
% 9.37/3.30  
% 9.37/3.30  #Partial instantiations: 14782
% 9.37/3.30  #Strategies tried      : 1
% 9.37/3.30  
% 9.37/3.30  Timing (in seconds)
% 9.37/3.30  ----------------------
% 9.37/3.30  Preprocessing        : 0.32
% 9.37/3.30  Parsing              : 0.15
% 9.37/3.30  CNF conversion       : 0.03
% 9.37/3.30  Main loop            : 2.07
% 9.37/3.30  Inferencing          : 0.89
% 9.37/3.30  Reduction            : 0.54
% 9.37/3.30  Demodulation         : 0.41
% 9.37/3.30  BG Simplification    : 0.08
% 9.37/3.30  Subsumption          : 0.43
% 9.37/3.30  Abstraction          : 0.10
% 9.37/3.30  MUC search           : 0.00
% 9.37/3.30  Cooper               : 0.00
% 9.37/3.30  Total                : 2.43
% 9.37/3.30  Index Insertion      : 0.00
% 9.37/3.30  Index Deletion       : 0.00
% 9.37/3.30  Index Matching       : 0.00
% 9.37/3.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
