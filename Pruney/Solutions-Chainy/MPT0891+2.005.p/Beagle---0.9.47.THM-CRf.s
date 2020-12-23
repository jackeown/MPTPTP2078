%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:40 EST 2020

% Result     : Theorem 9.73s
% Output     : CNFRefutation 9.73s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 168 expanded)
%              Number of leaves         :   40 (  77 expanded)
%              Depth                    :    8
%              Number of atoms          :  143 ( 348 expanded)
%              Number of equality atoms :  112 ( 266 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_97,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_70,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_40,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    ! [A_17] : k2_zfmisc_1(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_141,plain,(
    ! [A_69,B_70] : ~ r2_hidden(A_69,k2_zfmisc_1(A_69,B_70)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_144,plain,(
    ! [A_17] : ~ r2_hidden(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_141])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14167,plain,(
    ! [B_86819,C_86820,A_86821] :
      ( r2_hidden(B_86819,C_86820)
      | k4_xboole_0(k2_tarski(A_86821,B_86819),C_86820) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14174,plain,(
    ! [B_86819,A_86821] :
      ( r2_hidden(B_86819,k1_xboole_0)
      | k2_tarski(A_86821,B_86819) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14167])).

tff(c_14176,plain,(
    ! [A_86822,B_86823] : k2_tarski(A_86822,B_86823) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_14174])).

tff(c_14178,plain,(
    ! [A_14] : k1_tarski(A_14) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_14176])).

tff(c_6936,plain,(
    ! [A_42334] :
      ( r2_hidden('#skF_5'(A_42334),A_42334)
      | k1_xboole_0 = A_42334 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_28,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6945,plain,(
    ! [A_9] :
      ( '#skF_5'(k1_tarski(A_9)) = A_9
      | k1_tarski(A_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6936,c_28])).

tff(c_14179,plain,(
    ! [A_9] : '#skF_5'(k1_tarski(A_9)) = A_9 ),
    inference(negUnitSimplification,[status(thm)],[c_14178,c_6945])).

tff(c_30,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14310,plain,(
    ! [D_86856,A_86857,C_86858,E_86859] :
      ( ~ r2_hidden(D_86856,A_86857)
      | k3_mcart_1(C_86858,D_86856,E_86859) != '#skF_5'(A_86857)
      | k1_xboole_0 = A_86857 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14324,plain,(
    ! [C_86858,C_13,E_86859] :
      ( k3_mcart_1(C_86858,C_13,E_86859) != '#skF_5'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_14310])).

tff(c_14336,plain,(
    ! [C_86858,C_13,E_86859] :
      ( k3_mcart_1(C_86858,C_13,E_86859) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14179,c_14324])).

tff(c_14337,plain,(
    ! [C_86858,C_13,E_86859] : k3_mcart_1(C_86858,C_13,E_86859) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_14178,c_14336])).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_7008,plain,(
    ! [A_42347,B_42348,C_42349] : k4_tarski(k4_tarski(A_42347,B_42348),C_42349) = k3_mcart_1(A_42347,B_42348,C_42349) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    ! [A_54,B_55] : k2_mcart_1(k4_tarski(A_54,B_55)) = B_55 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    ! [B_33,C_34] : k2_mcart_1(k4_tarski(B_33,C_34)) != k4_tarski(B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_88,plain,(
    ! [B_33,C_34] : k4_tarski(B_33,C_34) != C_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_62])).

tff(c_7026,plain,(
    ! [A_42347,B_42348,C_42349] : k3_mcart_1(A_42347,B_42348,C_42349) != C_42349 ),
    inference(superposition,[status(thm),theory(equality)],[c_7008,c_88])).

tff(c_238,plain,(
    ! [B_94,C_95,A_96] :
      ( r2_hidden(B_94,C_95)
      | k4_xboole_0(k2_tarski(A_96,B_94),C_95) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_245,plain,(
    ! [B_94,A_96] :
      ( r2_hidden(B_94,k1_xboole_0)
      | k2_tarski(A_96,B_94) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_238])).

tff(c_247,plain,(
    ! [A_97,B_98] : k2_tarski(A_97,B_98) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_245])).

tff(c_249,plain,(
    ! [A_14] : k1_tarski(A_14) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_247])).

tff(c_167,plain,(
    ! [A_81] :
      ( r2_hidden('#skF_5'(A_81),A_81)
      | k1_xboole_0 = A_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_176,plain,(
    ! [A_9] :
      ( '#skF_5'(k1_tarski(A_9)) = A_9
      | k1_tarski(A_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_167,c_28])).

tff(c_250,plain,(
    ! [A_9] : '#skF_5'(k1_tarski(A_9)) = A_9 ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_176])).

tff(c_862,plain,(
    ! [C_2416,A_2417,D_2418,E_2419] :
      ( ~ r2_hidden(C_2416,A_2417)
      | k3_mcart_1(C_2416,D_2418,E_2419) != '#skF_5'(A_2417)
      | k1_xboole_0 = A_2417 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_876,plain,(
    ! [C_13,D_2418,E_2419] :
      ( k3_mcart_1(C_13,D_2418,E_2419) != '#skF_5'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_862])).

tff(c_888,plain,(
    ! [C_13,D_2418,E_2419] :
      ( k3_mcart_1(C_13,D_2418,E_2419) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_876])).

tff(c_889,plain,(
    ! [C_13,D_2418,E_2419] : k3_mcart_1(C_13,D_2418,E_2419) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_888])).

tff(c_78,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_166,plain,(
    k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_6759,plain,(
    ! [A_42060,B_42061,C_42062,D_42063] :
      ( k3_mcart_1(k5_mcart_1(A_42060,B_42061,C_42062,D_42063),k6_mcart_1(A_42060,B_42061,C_42062,D_42063),k7_mcart_1(A_42060,B_42061,C_42062,D_42063)) = D_42063
      | ~ m1_subset_1(D_42063,k3_zfmisc_1(A_42060,B_42061,C_42062))
      | k1_xboole_0 = C_42062
      | k1_xboole_0 = B_42061
      | k1_xboole_0 = A_42060 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6921,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_6759])).

tff(c_6931,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_6921])).

tff(c_6933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_82,c_889,c_6931])).

tff(c_6934,plain,
    ( k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_6949,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_6934])).

tff(c_13847,plain,(
    ! [A_86523,B_86524,C_86525,D_86526] :
      ( k3_mcart_1(k5_mcart_1(A_86523,B_86524,C_86525,D_86526),k6_mcart_1(A_86523,B_86524,C_86525,D_86526),k7_mcart_1(A_86523,B_86524,C_86525,D_86526)) = D_86526
      | ~ m1_subset_1(D_86526,k3_zfmisc_1(A_86523,B_86524,C_86525))
      | k1_xboole_0 = C_86525
      | k1_xboole_0 = B_86524
      | k1_xboole_0 = A_86523 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_14007,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6949,c_13847])).

tff(c_14017,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_14007])).

tff(c_14019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_82,c_7026,c_14017])).

tff(c_14020,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_6934])).

tff(c_20172,plain,(
    ! [A_125702,B_125703,C_125704,D_125705] :
      ( k3_mcart_1(k5_mcart_1(A_125702,B_125703,C_125704,D_125705),k6_mcart_1(A_125702,B_125703,C_125704,D_125705),k7_mcart_1(A_125702,B_125703,C_125704,D_125705)) = D_125705
      | ~ m1_subset_1(D_125705,k3_zfmisc_1(A_125702,B_125703,C_125704))
      | k1_xboole_0 = C_125704
      | k1_xboole_0 = B_125703
      | k1_xboole_0 = A_125702 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20321,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_14020,c_20172])).

tff(c_20330,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_20321])).

tff(c_20332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_82,c_14337,c_20330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n018.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 19:28:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.73/3.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/3.53  
% 9.73/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/3.53  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4
% 9.73/3.53  
% 9.73/3.53  %Foreground sorts:
% 9.73/3.53  
% 9.73/3.53  
% 9.73/3.53  %Background operators:
% 9.73/3.53  
% 9.73/3.53  
% 9.73/3.53  %Foreground operators:
% 9.73/3.53  tff('#skF_5', type, '#skF_5': $i > $i).
% 9.73/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.73/3.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.73/3.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.73/3.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.73/3.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.73/3.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.73/3.53  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 9.73/3.53  tff('#skF_7', type, '#skF_7': $i).
% 9.73/3.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.73/3.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.73/3.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 9.73/3.53  tff('#skF_6', type, '#skF_6': $i).
% 9.73/3.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.73/3.53  tff('#skF_9', type, '#skF_9': $i).
% 9.73/3.53  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 9.73/3.53  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 9.73/3.53  tff('#skF_8', type, '#skF_8': $i).
% 9.73/3.53  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 9.73/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.73/3.53  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 9.73/3.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.73/3.53  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 9.73/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.73/3.53  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 9.73/3.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 9.73/3.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.73/3.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.73/3.53  
% 9.73/3.55  tff(f_141, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 9.73/3.55  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 9.73/3.55  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.73/3.55  tff(f_62, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 9.73/3.55  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.73/3.55  tff(f_68, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 9.73/3.55  tff(f_97, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 9.73/3.55  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 9.73/3.55  tff(f_70, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 9.73/3.55  tff(f_117, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 9.73/3.55  tff(f_81, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 9.73/3.55  tff(f_113, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 9.73/3.55  tff(c_86, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.73/3.55  tff(c_84, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.73/3.55  tff(c_82, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.73/3.55  tff(c_40, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.73/3.55  tff(c_46, plain, (![A_17]: (k2_zfmisc_1(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.73/3.55  tff(c_141, plain, (![A_69, B_70]: (~r2_hidden(A_69, k2_zfmisc_1(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.73/3.55  tff(c_144, plain, (![A_17]: (~r2_hidden(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_141])).
% 9.73/3.55  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.73/3.55  tff(c_14167, plain, (![B_86819, C_86820, A_86821]: (r2_hidden(B_86819, C_86820) | k4_xboole_0(k2_tarski(A_86821, B_86819), C_86820)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.73/3.55  tff(c_14174, plain, (![B_86819, A_86821]: (r2_hidden(B_86819, k1_xboole_0) | k2_tarski(A_86821, B_86819)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_14167])).
% 9.73/3.55  tff(c_14176, plain, (![A_86822, B_86823]: (k2_tarski(A_86822, B_86823)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_144, c_14174])).
% 9.73/3.55  tff(c_14178, plain, (![A_14]: (k1_tarski(A_14)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_14176])).
% 9.73/3.55  tff(c_6936, plain, (![A_42334]: (r2_hidden('#skF_5'(A_42334), A_42334) | k1_xboole_0=A_42334)), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.73/3.55  tff(c_28, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.73/3.55  tff(c_6945, plain, (![A_9]: ('#skF_5'(k1_tarski(A_9))=A_9 | k1_tarski(A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6936, c_28])).
% 9.73/3.55  tff(c_14179, plain, (![A_9]: ('#skF_5'(k1_tarski(A_9))=A_9)), inference(negUnitSimplification, [status(thm)], [c_14178, c_6945])).
% 9.73/3.55  tff(c_30, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.73/3.55  tff(c_14310, plain, (![D_86856, A_86857, C_86858, E_86859]: (~r2_hidden(D_86856, A_86857) | k3_mcart_1(C_86858, D_86856, E_86859)!='#skF_5'(A_86857) | k1_xboole_0=A_86857)), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.73/3.55  tff(c_14324, plain, (![C_86858, C_13, E_86859]: (k3_mcart_1(C_86858, C_13, E_86859)!='#skF_5'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_14310])).
% 9.73/3.55  tff(c_14336, plain, (![C_86858, C_13, E_86859]: (k3_mcart_1(C_86858, C_13, E_86859)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14179, c_14324])).
% 9.73/3.55  tff(c_14337, plain, (![C_86858, C_13, E_86859]: (k3_mcart_1(C_86858, C_13, E_86859)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_14178, c_14336])).
% 9.73/3.55  tff(c_80, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.73/3.55  tff(c_7008, plain, (![A_42347, B_42348, C_42349]: (k4_tarski(k4_tarski(A_42347, B_42348), C_42349)=k3_mcart_1(A_42347, B_42348, C_42349))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.73/3.55  tff(c_76, plain, (![A_54, B_55]: (k2_mcart_1(k4_tarski(A_54, B_55))=B_55)), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.73/3.55  tff(c_62, plain, (![B_33, C_34]: (k2_mcart_1(k4_tarski(B_33, C_34))!=k4_tarski(B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.73/3.55  tff(c_88, plain, (![B_33, C_34]: (k4_tarski(B_33, C_34)!=C_34)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_62])).
% 9.73/3.55  tff(c_7026, plain, (![A_42347, B_42348, C_42349]: (k3_mcart_1(A_42347, B_42348, C_42349)!=C_42349)), inference(superposition, [status(thm), theory('equality')], [c_7008, c_88])).
% 9.73/3.55  tff(c_238, plain, (![B_94, C_95, A_96]: (r2_hidden(B_94, C_95) | k4_xboole_0(k2_tarski(A_96, B_94), C_95)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.73/3.55  tff(c_245, plain, (![B_94, A_96]: (r2_hidden(B_94, k1_xboole_0) | k2_tarski(A_96, B_94)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_238])).
% 9.73/3.55  tff(c_247, plain, (![A_97, B_98]: (k2_tarski(A_97, B_98)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_144, c_245])).
% 9.73/3.55  tff(c_249, plain, (![A_14]: (k1_tarski(A_14)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_247])).
% 9.73/3.55  tff(c_167, plain, (![A_81]: (r2_hidden('#skF_5'(A_81), A_81) | k1_xboole_0=A_81)), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.73/3.55  tff(c_176, plain, (![A_9]: ('#skF_5'(k1_tarski(A_9))=A_9 | k1_tarski(A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_167, c_28])).
% 9.73/3.55  tff(c_250, plain, (![A_9]: ('#skF_5'(k1_tarski(A_9))=A_9)), inference(negUnitSimplification, [status(thm)], [c_249, c_176])).
% 9.73/3.55  tff(c_862, plain, (![C_2416, A_2417, D_2418, E_2419]: (~r2_hidden(C_2416, A_2417) | k3_mcart_1(C_2416, D_2418, E_2419)!='#skF_5'(A_2417) | k1_xboole_0=A_2417)), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.73/3.55  tff(c_876, plain, (![C_13, D_2418, E_2419]: (k3_mcart_1(C_13, D_2418, E_2419)!='#skF_5'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_862])).
% 9.73/3.55  tff(c_888, plain, (![C_13, D_2418, E_2419]: (k3_mcart_1(C_13, D_2418, E_2419)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_250, c_876])).
% 9.73/3.55  tff(c_889, plain, (![C_13, D_2418, E_2419]: (k3_mcart_1(C_13, D_2418, E_2419)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_249, c_888])).
% 9.73/3.55  tff(c_78, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.73/3.55  tff(c_166, plain, (k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_78])).
% 9.73/3.55  tff(c_6759, plain, (![A_42060, B_42061, C_42062, D_42063]: (k3_mcart_1(k5_mcart_1(A_42060, B_42061, C_42062, D_42063), k6_mcart_1(A_42060, B_42061, C_42062, D_42063), k7_mcart_1(A_42060, B_42061, C_42062, D_42063))=D_42063 | ~m1_subset_1(D_42063, k3_zfmisc_1(A_42060, B_42061, C_42062)) | k1_xboole_0=C_42062 | k1_xboole_0=B_42061 | k1_xboole_0=A_42060)), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.73/3.55  tff(c_6921, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_166, c_6759])).
% 9.73/3.55  tff(c_6931, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_6921])).
% 9.73/3.55  tff(c_6933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_82, c_889, c_6931])).
% 9.73/3.55  tff(c_6934, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_78])).
% 9.73/3.55  tff(c_6949, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_6934])).
% 9.73/3.55  tff(c_13847, plain, (![A_86523, B_86524, C_86525, D_86526]: (k3_mcart_1(k5_mcart_1(A_86523, B_86524, C_86525, D_86526), k6_mcart_1(A_86523, B_86524, C_86525, D_86526), k7_mcart_1(A_86523, B_86524, C_86525, D_86526))=D_86526 | ~m1_subset_1(D_86526, k3_zfmisc_1(A_86523, B_86524, C_86525)) | k1_xboole_0=C_86525 | k1_xboole_0=B_86524 | k1_xboole_0=A_86523)), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.73/3.55  tff(c_14007, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_6949, c_13847])).
% 9.73/3.55  tff(c_14017, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_14007])).
% 9.73/3.55  tff(c_14019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_82, c_7026, c_14017])).
% 9.73/3.55  tff(c_14020, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_6934])).
% 9.73/3.55  tff(c_20172, plain, (![A_125702, B_125703, C_125704, D_125705]: (k3_mcart_1(k5_mcart_1(A_125702, B_125703, C_125704, D_125705), k6_mcart_1(A_125702, B_125703, C_125704, D_125705), k7_mcart_1(A_125702, B_125703, C_125704, D_125705))=D_125705 | ~m1_subset_1(D_125705, k3_zfmisc_1(A_125702, B_125703, C_125704)) | k1_xboole_0=C_125704 | k1_xboole_0=B_125703 | k1_xboole_0=A_125702)), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.73/3.55  tff(c_20321, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_14020, c_20172])).
% 9.73/3.55  tff(c_20330, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_20321])).
% 9.73/3.55  tff(c_20332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_82, c_14337, c_20330])).
% 9.73/3.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.73/3.55  
% 9.73/3.55  Inference rules
% 9.73/3.55  ----------------------
% 9.73/3.55  #Ref     : 24
% 9.73/3.55  #Sup     : 2540
% 9.73/3.55  #Fact    : 6
% 9.73/3.55  #Define  : 0
% 9.73/3.55  #Split   : 19
% 9.73/3.55  #Chain   : 0
% 9.73/3.55  #Close   : 0
% 9.73/3.55  
% 9.73/3.55  Ordering : KBO
% 9.73/3.55  
% 9.73/3.55  Simplification rules
% 9.73/3.55  ----------------------
% 9.73/3.55  #Subsume      : 482
% 9.73/3.55  #Demod        : 614
% 9.73/3.55  #Tautology    : 648
% 9.73/3.55  #SimpNegUnit  : 462
% 9.73/3.55  #BackRed      : 125
% 9.73/3.55  
% 9.73/3.55  #Partial instantiations: 39449
% 9.73/3.55  #Strategies tried      : 1
% 9.73/3.55  
% 9.73/3.55  Timing (in seconds)
% 9.73/3.55  ----------------------
% 9.73/3.55  Preprocessing        : 0.33
% 9.73/3.55  Parsing              : 0.17
% 9.73/3.55  CNF conversion       : 0.03
% 9.73/3.55  Main loop            : 2.45
% 9.73/3.55  Inferencing          : 1.31
% 9.73/3.55  Reduction            : 0.54
% 9.73/3.55  Demodulation         : 0.35
% 9.73/3.55  BG Simplification    : 0.08
% 9.73/3.55  Subsumption          : 0.37
% 9.73/3.55  Abstraction          : 0.12
% 9.73/3.55  MUC search           : 0.00
% 9.73/3.55  Cooper               : 0.00
% 9.73/3.55  Total                : 2.82
% 9.73/3.55  Index Insertion      : 0.00
% 9.73/3.55  Index Deletion       : 0.00
% 9.73/3.55  Index Matching       : 0.00
% 9.73/3.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
