%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:39 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 147 expanded)
%              Number of leaves         :   33 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 240 expanded)
%              Number of equality atoms :   50 (  99 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_78,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_90,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_117,plain,(
    ~ r2_hidden('#skF_9','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_52,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7498,plain,(
    ! [A_4491,B_4492,C_4493] :
      ( ~ r2_hidden('#skF_2'(A_4491,B_4492,C_4493),C_4493)
      | r2_hidden('#skF_3'(A_4491,B_4492,C_4493),C_4493)
      | k3_xboole_0(A_4491,B_4492) = C_4493 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7636,plain,(
    ! [A_4501,B_4502] :
      ( r2_hidden('#skF_3'(A_4501,B_4502,B_4502),B_4502)
      | k3_xboole_0(A_4501,B_4502) = B_4502 ) ),
    inference(resolution,[status(thm)],[c_22,c_7498])).

tff(c_296,plain,(
    ! [A_88,B_89] :
      ( ~ r2_hidden(A_88,B_89)
      | k4_xboole_0(k1_tarski(A_88),B_89) != k1_tarski(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_305,plain,(
    ! [A_88] : ~ r2_hidden(A_88,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_296])).

tff(c_7707,plain,(
    ! [A_4503] : k3_xboole_0(A_4503,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7636,c_305])).

tff(c_50,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7718,plain,(
    ! [A_4503] : k5_xboole_0(A_4503,k1_xboole_0) = k4_xboole_0(A_4503,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7707,c_50])).

tff(c_7726,plain,(
    ! [A_4503] : k5_xboole_0(A_4503,k1_xboole_0) = A_4503 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7718])).

tff(c_7048,plain,(
    ! [A_4482,B_4483,C_4484] :
      ( r2_hidden('#skF_4'(A_4482,B_4483,C_4484),A_4482)
      | r2_hidden('#skF_5'(A_4482,B_4483,C_4484),C_4484)
      | k4_xboole_0(A_4482,B_4483) = C_4484 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [A_12,B_13,C_14] :
      ( ~ r2_hidden('#skF_4'(A_12,B_13,C_14),C_14)
      | r2_hidden('#skF_5'(A_12,B_13,C_14),C_14)
      | k4_xboole_0(A_12,B_13) = C_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7526,plain,(
    ! [A_4494,B_4495] :
      ( r2_hidden('#skF_5'(A_4494,B_4495,A_4494),A_4494)
      | k4_xboole_0(A_4494,B_4495) = A_4494 ) ),
    inference(resolution,[status(thm)],[c_7048,c_38])).

tff(c_7592,plain,(
    ! [B_4495] : k4_xboole_0(k1_xboole_0,B_4495) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7526,c_305])).

tff(c_7175,plain,(
    ! [B_4483,C_4484] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_4483,C_4484),C_4484)
      | k4_xboole_0(k1_xboole_0,B_4483) = C_4484 ) ),
    inference(resolution,[status(thm)],[c_7048,c_305])).

tff(c_8222,plain,(
    ! [B_4528,C_4529] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_4528,C_4529),C_4529)
      | k1_xboole_0 = C_4529 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7592,c_7175])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10394,plain,(
    ! [B_4655,A_4656,B_4657] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_4655,k3_xboole_0(A_4656,B_4657)),B_4657)
      | k3_xboole_0(A_4656,B_4657) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8222,c_10])).

tff(c_40,plain,(
    ! [A_12,B_13,C_14] :
      ( ~ r2_hidden('#skF_4'(A_12,B_13,C_14),B_13)
      | r2_hidden('#skF_5'(A_12,B_13,C_14),C_14)
      | k4_xboole_0(A_12,B_13) = C_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7739,plain,(
    ! [A_4505,C_4506] :
      ( r2_hidden('#skF_5'(A_4505,A_4505,C_4506),C_4506)
      | k4_xboole_0(A_4505,A_4505) = C_4506 ) ),
    inference(resolution,[status(thm)],[c_7048,c_40])).

tff(c_7805,plain,(
    ! [A_4505] : k4_xboole_0(A_4505,A_4505) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7739,c_305])).

tff(c_7162,plain,(
    ! [A_4482,C_4484] :
      ( r2_hidden('#skF_5'(A_4482,A_4482,C_4484),C_4484)
      | k4_xboole_0(A_4482,A_4482) = C_4484 ) ),
    inference(resolution,[status(thm)],[c_7048,c_40])).

tff(c_7863,plain,(
    ! [A_4509,C_4510] :
      ( r2_hidden('#skF_5'(A_4509,A_4509,C_4510),C_4510)
      | k1_xboole_0 = C_4510 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7805,c_7162])).

tff(c_258,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(k1_tarski(A_85),B_86) = k1_tarski(A_85)
      | r2_hidden(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [D_17,B_13,A_12] :
      ( ~ r2_hidden(D_17,B_13)
      | ~ r2_hidden(D_17,k4_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_264,plain,(
    ! [D_17,B_86,A_85] :
      ( ~ r2_hidden(D_17,B_86)
      | ~ r2_hidden(D_17,k1_tarski(A_85))
      | r2_hidden(A_85,B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_28])).

tff(c_7941,plain,(
    ! [A_4509,C_4510,A_85] :
      ( ~ r2_hidden('#skF_5'(A_4509,A_4509,C_4510),k1_tarski(A_85))
      | r2_hidden(A_85,C_4510)
      | k1_xboole_0 = C_4510 ) ),
    inference(resolution,[status(thm)],[c_7863,c_264])).

tff(c_10523,plain,(
    ! [A_4660,A_4661] :
      ( r2_hidden(A_4660,k3_xboole_0(A_4661,k1_tarski(A_4660)))
      | k3_xboole_0(A_4661,k1_tarski(A_4660)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10394,c_7941])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10545,plain,(
    ! [A_4662,A_4663] :
      ( r2_hidden(A_4662,A_4663)
      | k3_xboole_0(A_4663,k1_tarski(A_4662)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10523,c_12])).

tff(c_10587,plain,(
    ! [A_4663,A_4662] :
      ( k4_xboole_0(A_4663,k1_tarski(A_4662)) = k5_xboole_0(A_4663,k1_xboole_0)
      | r2_hidden(A_4662,A_4663) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10545,c_50])).

tff(c_10611,plain,(
    ! [A_4664,A_4665] :
      ( k4_xboole_0(A_4664,k1_tarski(A_4665)) = A_4664
      | r2_hidden(A_4665,A_4664) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7726,c_10587])).

tff(c_88,plain,
    ( k4_xboole_0('#skF_8',k1_tarski('#skF_9')) != '#skF_8'
    | r2_hidden('#skF_11','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_137,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_10658,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_10611,c_137])).

tff(c_10687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_10658])).

tff(c_10688,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_78,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_119,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_58,plain,(
    ! [E_29,A_23,C_25] : r2_hidden(E_29,k1_enumset1(A_23,E_29,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10694,plain,(
    ! [A_4666,B_4667] : r2_hidden(A_4666,k2_tarski(A_4666,B_4667)) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_58])).

tff(c_10697,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10694])).

tff(c_10689,plain,(
    k4_xboole_0('#skF_8',k1_tarski('#skF_9')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_92,plain,
    ( k4_xboole_0('#skF_8',k1_tarski('#skF_9')) != '#skF_8'
    | k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10766,plain,(
    k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10689,c_92])).

tff(c_10777,plain,(
    ! [D_4690] :
      ( ~ r2_hidden(D_4690,k1_tarski('#skF_11'))
      | ~ r2_hidden(D_4690,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10766,c_28])).

tff(c_10785,plain,(
    ~ r2_hidden('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_10697,c_10777])).

tff(c_10790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10688,c_10785])).

tff(c_10791,plain,(
    r2_hidden('#skF_11','#skF_10') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_10794,plain,(
    ! [A_4694,B_4695] : k1_enumset1(A_4694,A_4694,B_4695) = k2_tarski(A_4694,B_4695) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ! [E_29,A_23,B_24] : r2_hidden(E_29,k1_enumset1(A_23,B_24,E_29)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10813,plain,(
    ! [B_4696,A_4697] : r2_hidden(B_4696,k2_tarski(A_4697,B_4696)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10794,c_56])).

tff(c_10816,plain,(
    ! [A_30] : r2_hidden(A_30,k1_tarski(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10813])).

tff(c_10792,plain,(
    r2_hidden('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_94,plain,
    ( ~ r2_hidden('#skF_9','#skF_8')
    | k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10824,plain,(
    k4_xboole_0('#skF_10',k1_tarski('#skF_11')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10792,c_94])).

tff(c_10844,plain,(
    ! [D_4708,B_4709,A_4710] :
      ( ~ r2_hidden(D_4708,B_4709)
      | ~ r2_hidden(D_4708,k4_xboole_0(A_4710,B_4709)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10873,plain,(
    ! [D_4716] :
      ( ~ r2_hidden(D_4716,k1_tarski('#skF_11'))
      | ~ r2_hidden(D_4716,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10824,c_10844])).

tff(c_10881,plain,(
    ~ r2_hidden('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_10816,c_10873])).

tff(c_10886,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10791,c_10881])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:09:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.36  
% 6.62/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.36  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 6.62/2.36  
% 6.62/2.36  %Foreground sorts:
% 6.62/2.36  
% 6.62/2.36  
% 6.62/2.36  %Background operators:
% 6.62/2.36  
% 6.62/2.36  
% 6.62/2.36  %Foreground operators:
% 6.62/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.62/2.36  tff('#skF_11', type, '#skF_11': $i).
% 6.62/2.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.62/2.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.62/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.62/2.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.62/2.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.62/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.62/2.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.62/2.36  tff('#skF_10', type, '#skF_10': $i).
% 6.62/2.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.62/2.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.62/2.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.62/2.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.62/2.36  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 6.62/2.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.62/2.36  tff('#skF_9', type, '#skF_9': $i).
% 6.62/2.36  tff('#skF_8', type, '#skF_8': $i).
% 6.62/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.62/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.62/2.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.62/2.36  
% 6.62/2.38  tff(f_93, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.62/2.38  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.62/2.38  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.62/2.38  tff(f_87, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 6.62/2.38  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.62/2.38  tff(f_51, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.62/2.38  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.62/2.38  tff(f_80, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.62/2.38  tff(f_76, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.62/2.38  tff(c_90, plain, (~r2_hidden('#skF_9', '#skF_8') | r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.62/2.38  tff(c_117, plain, (~r2_hidden('#skF_9', '#skF_8')), inference(splitLeft, [status(thm)], [c_90])).
% 6.62/2.38  tff(c_52, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.62/2.38  tff(c_22, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.62/2.38  tff(c_7498, plain, (![A_4491, B_4492, C_4493]: (~r2_hidden('#skF_2'(A_4491, B_4492, C_4493), C_4493) | r2_hidden('#skF_3'(A_4491, B_4492, C_4493), C_4493) | k3_xboole_0(A_4491, B_4492)=C_4493)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.62/2.38  tff(c_7636, plain, (![A_4501, B_4502]: (r2_hidden('#skF_3'(A_4501, B_4502, B_4502), B_4502) | k3_xboole_0(A_4501, B_4502)=B_4502)), inference(resolution, [status(thm)], [c_22, c_7498])).
% 6.62/2.38  tff(c_296, plain, (![A_88, B_89]: (~r2_hidden(A_88, B_89) | k4_xboole_0(k1_tarski(A_88), B_89)!=k1_tarski(A_88))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.62/2.38  tff(c_305, plain, (![A_88]: (~r2_hidden(A_88, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_296])).
% 6.62/2.38  tff(c_7707, plain, (![A_4503]: (k3_xboole_0(A_4503, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7636, c_305])).
% 6.62/2.38  tff(c_50, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.62/2.38  tff(c_7718, plain, (![A_4503]: (k5_xboole_0(A_4503, k1_xboole_0)=k4_xboole_0(A_4503, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7707, c_50])).
% 6.62/2.38  tff(c_7726, plain, (![A_4503]: (k5_xboole_0(A_4503, k1_xboole_0)=A_4503)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_7718])).
% 6.62/2.38  tff(c_7048, plain, (![A_4482, B_4483, C_4484]: (r2_hidden('#skF_4'(A_4482, B_4483, C_4484), A_4482) | r2_hidden('#skF_5'(A_4482, B_4483, C_4484), C_4484) | k4_xboole_0(A_4482, B_4483)=C_4484)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.62/2.38  tff(c_38, plain, (![A_12, B_13, C_14]: (~r2_hidden('#skF_4'(A_12, B_13, C_14), C_14) | r2_hidden('#skF_5'(A_12, B_13, C_14), C_14) | k4_xboole_0(A_12, B_13)=C_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.62/2.38  tff(c_7526, plain, (![A_4494, B_4495]: (r2_hidden('#skF_5'(A_4494, B_4495, A_4494), A_4494) | k4_xboole_0(A_4494, B_4495)=A_4494)), inference(resolution, [status(thm)], [c_7048, c_38])).
% 6.62/2.38  tff(c_7592, plain, (![B_4495]: (k4_xboole_0(k1_xboole_0, B_4495)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7526, c_305])).
% 6.62/2.38  tff(c_7175, plain, (![B_4483, C_4484]: (r2_hidden('#skF_5'(k1_xboole_0, B_4483, C_4484), C_4484) | k4_xboole_0(k1_xboole_0, B_4483)=C_4484)), inference(resolution, [status(thm)], [c_7048, c_305])).
% 6.62/2.38  tff(c_8222, plain, (![B_4528, C_4529]: (r2_hidden('#skF_5'(k1_xboole_0, B_4528, C_4529), C_4529) | k1_xboole_0=C_4529)), inference(demodulation, [status(thm), theory('equality')], [c_7592, c_7175])).
% 6.62/2.38  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.62/2.38  tff(c_10394, plain, (![B_4655, A_4656, B_4657]: (r2_hidden('#skF_5'(k1_xboole_0, B_4655, k3_xboole_0(A_4656, B_4657)), B_4657) | k3_xboole_0(A_4656, B_4657)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8222, c_10])).
% 6.62/2.38  tff(c_40, plain, (![A_12, B_13, C_14]: (~r2_hidden('#skF_4'(A_12, B_13, C_14), B_13) | r2_hidden('#skF_5'(A_12, B_13, C_14), C_14) | k4_xboole_0(A_12, B_13)=C_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.62/2.38  tff(c_7739, plain, (![A_4505, C_4506]: (r2_hidden('#skF_5'(A_4505, A_4505, C_4506), C_4506) | k4_xboole_0(A_4505, A_4505)=C_4506)), inference(resolution, [status(thm)], [c_7048, c_40])).
% 6.62/2.38  tff(c_7805, plain, (![A_4505]: (k4_xboole_0(A_4505, A_4505)=k1_xboole_0)), inference(resolution, [status(thm)], [c_7739, c_305])).
% 6.62/2.38  tff(c_7162, plain, (![A_4482, C_4484]: (r2_hidden('#skF_5'(A_4482, A_4482, C_4484), C_4484) | k4_xboole_0(A_4482, A_4482)=C_4484)), inference(resolution, [status(thm)], [c_7048, c_40])).
% 6.62/2.38  tff(c_7863, plain, (![A_4509, C_4510]: (r2_hidden('#skF_5'(A_4509, A_4509, C_4510), C_4510) | k1_xboole_0=C_4510)), inference(demodulation, [status(thm), theory('equality')], [c_7805, c_7162])).
% 6.62/2.38  tff(c_258, plain, (![A_85, B_86]: (k4_xboole_0(k1_tarski(A_85), B_86)=k1_tarski(A_85) | r2_hidden(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.62/2.38  tff(c_28, plain, (![D_17, B_13, A_12]: (~r2_hidden(D_17, B_13) | ~r2_hidden(D_17, k4_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.62/2.38  tff(c_264, plain, (![D_17, B_86, A_85]: (~r2_hidden(D_17, B_86) | ~r2_hidden(D_17, k1_tarski(A_85)) | r2_hidden(A_85, B_86))), inference(superposition, [status(thm), theory('equality')], [c_258, c_28])).
% 6.62/2.38  tff(c_7941, plain, (![A_4509, C_4510, A_85]: (~r2_hidden('#skF_5'(A_4509, A_4509, C_4510), k1_tarski(A_85)) | r2_hidden(A_85, C_4510) | k1_xboole_0=C_4510)), inference(resolution, [status(thm)], [c_7863, c_264])).
% 6.62/2.38  tff(c_10523, plain, (![A_4660, A_4661]: (r2_hidden(A_4660, k3_xboole_0(A_4661, k1_tarski(A_4660))) | k3_xboole_0(A_4661, k1_tarski(A_4660))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10394, c_7941])).
% 6.62/2.38  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.62/2.38  tff(c_10545, plain, (![A_4662, A_4663]: (r2_hidden(A_4662, A_4663) | k3_xboole_0(A_4663, k1_tarski(A_4662))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10523, c_12])).
% 6.62/2.38  tff(c_10587, plain, (![A_4663, A_4662]: (k4_xboole_0(A_4663, k1_tarski(A_4662))=k5_xboole_0(A_4663, k1_xboole_0) | r2_hidden(A_4662, A_4663))), inference(superposition, [status(thm), theory('equality')], [c_10545, c_50])).
% 6.62/2.38  tff(c_10611, plain, (![A_4664, A_4665]: (k4_xboole_0(A_4664, k1_tarski(A_4665))=A_4664 | r2_hidden(A_4665, A_4664))), inference(demodulation, [status(thm), theory('equality')], [c_7726, c_10587])).
% 6.62/2.38  tff(c_88, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))!='#skF_8' | r2_hidden('#skF_11', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.62/2.38  tff(c_137, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))!='#skF_8'), inference(splitLeft, [status(thm)], [c_88])).
% 6.62/2.38  tff(c_10658, plain, (r2_hidden('#skF_9', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_10611, c_137])).
% 6.62/2.38  tff(c_10687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_10658])).
% 6.62/2.38  tff(c_10688, plain, (r2_hidden('#skF_11', '#skF_10')), inference(splitRight, [status(thm)], [c_88])).
% 6.62/2.38  tff(c_78, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.62/2.38  tff(c_119, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.62/2.38  tff(c_58, plain, (![E_29, A_23, C_25]: (r2_hidden(E_29, k1_enumset1(A_23, E_29, C_25)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.62/2.38  tff(c_10694, plain, (![A_4666, B_4667]: (r2_hidden(A_4666, k2_tarski(A_4666, B_4667)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_58])).
% 6.62/2.38  tff(c_10697, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_10694])).
% 6.62/2.38  tff(c_10689, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))='#skF_8'), inference(splitRight, [status(thm)], [c_88])).
% 6.62/2.38  tff(c_92, plain, (k4_xboole_0('#skF_8', k1_tarski('#skF_9'))!='#skF_8' | k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.62/2.38  tff(c_10766, plain, (k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_10689, c_92])).
% 6.62/2.38  tff(c_10777, plain, (![D_4690]: (~r2_hidden(D_4690, k1_tarski('#skF_11')) | ~r2_hidden(D_4690, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_10766, c_28])).
% 6.62/2.38  tff(c_10785, plain, (~r2_hidden('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_10697, c_10777])).
% 6.62/2.38  tff(c_10790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10688, c_10785])).
% 6.62/2.38  tff(c_10791, plain, (r2_hidden('#skF_11', '#skF_10')), inference(splitRight, [status(thm)], [c_90])).
% 6.62/2.38  tff(c_10794, plain, (![A_4694, B_4695]: (k1_enumset1(A_4694, A_4694, B_4695)=k2_tarski(A_4694, B_4695))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.62/2.38  tff(c_56, plain, (![E_29, A_23, B_24]: (r2_hidden(E_29, k1_enumset1(A_23, B_24, E_29)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.62/2.38  tff(c_10813, plain, (![B_4696, A_4697]: (r2_hidden(B_4696, k2_tarski(A_4697, B_4696)))), inference(superposition, [status(thm), theory('equality')], [c_10794, c_56])).
% 6.62/2.38  tff(c_10816, plain, (![A_30]: (r2_hidden(A_30, k1_tarski(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_10813])).
% 6.62/2.38  tff(c_10792, plain, (r2_hidden('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_90])).
% 6.62/2.38  tff(c_94, plain, (~r2_hidden('#skF_9', '#skF_8') | k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.62/2.38  tff(c_10824, plain, (k4_xboole_0('#skF_10', k1_tarski('#skF_11'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_10792, c_94])).
% 6.62/2.38  tff(c_10844, plain, (![D_4708, B_4709, A_4710]: (~r2_hidden(D_4708, B_4709) | ~r2_hidden(D_4708, k4_xboole_0(A_4710, B_4709)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.62/2.38  tff(c_10873, plain, (![D_4716]: (~r2_hidden(D_4716, k1_tarski('#skF_11')) | ~r2_hidden(D_4716, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_10824, c_10844])).
% 6.62/2.38  tff(c_10881, plain, (~r2_hidden('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_10816, c_10873])).
% 6.62/2.38  tff(c_10886, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10791, c_10881])).
% 6.62/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.38  
% 6.62/2.38  Inference rules
% 6.62/2.38  ----------------------
% 6.62/2.38  #Ref     : 0
% 6.62/2.38  #Sup     : 2049
% 6.62/2.38  #Fact    : 2
% 6.62/2.38  #Define  : 0
% 6.62/2.38  #Split   : 2
% 6.62/2.38  #Chain   : 0
% 6.62/2.38  #Close   : 0
% 6.62/2.38  
% 6.62/2.38  Ordering : KBO
% 6.62/2.38  
% 6.62/2.38  Simplification rules
% 6.62/2.38  ----------------------
% 6.62/2.38  #Subsume      : 467
% 6.62/2.38  #Demod        : 499
% 6.62/2.38  #Tautology    : 381
% 6.62/2.38  #SimpNegUnit  : 127
% 6.62/2.38  #BackRed      : 1
% 6.62/2.38  
% 6.62/2.38  #Partial instantiations: 2128
% 6.62/2.38  #Strategies tried      : 1
% 6.62/2.38  
% 6.62/2.38  Timing (in seconds)
% 6.62/2.38  ----------------------
% 6.62/2.38  Preprocessing        : 0.34
% 6.62/2.38  Parsing              : 0.17
% 6.62/2.38  CNF conversion       : 0.03
% 6.62/2.38  Main loop            : 1.23
% 6.62/2.38  Inferencing          : 0.44
% 6.62/2.38  Reduction            : 0.36
% 6.62/2.38  Demodulation         : 0.25
% 6.62/2.38  BG Simplification    : 0.06
% 6.62/2.38  Subsumption          : 0.27
% 6.62/2.38  Abstraction          : 0.08
% 6.62/2.38  MUC search           : 0.00
% 6.62/2.38  Cooper               : 0.00
% 6.62/2.38  Total                : 1.61
% 6.62/2.38  Index Insertion      : 0.00
% 6.62/2.38  Index Deletion       : 0.00
% 6.62/2.38  Index Matching       : 0.00
% 6.62/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
