%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:40 EST 2020

% Result     : Theorem 23.35s
% Output     : CNFRefutation 23.35s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 169 expanded)
%              Number of leaves         :   40 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 344 expanded)
%              Number of equality atoms :  110 ( 270 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_91,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_34,plain,(
    ! [C_16] : r2_hidden(C_16,k1_tarski(C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_116218,plain,(
    ! [A_114203,B_114204] : k4_xboole_0(A_114203,k4_xboole_0(A_114203,B_114204)) = k3_xboole_0(A_114203,B_114204) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116233,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_116218])).

tff(c_116237,plain,(
    ! [A_114205] : k4_xboole_0(A_114205,A_114205) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_116233])).

tff(c_48,plain,(
    ! [B_21,A_20] :
      ( ~ r2_hidden(B_21,A_20)
      | k4_xboole_0(A_20,k1_tarski(B_21)) != A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_116246,plain,(
    ! [B_21] :
      ( ~ r2_hidden(B_21,k1_tarski(B_21))
      | k1_tarski(B_21) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116237,c_48])).

tff(c_116260,plain,(
    ! [B_21] : k1_tarski(B_21) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_116246])).

tff(c_136,plain,(
    ! [A_72] :
      ( r2_hidden('#skF_5'(A_72),A_72)
      | k1_xboole_0 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_141,plain,(
    ! [A_12] :
      ( '#skF_5'(k1_tarski(A_12)) = A_12
      | k1_tarski(A_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_136,c_32])).

tff(c_116264,plain,(
    ! [A_12] : '#skF_5'(k1_tarski(A_12)) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_116260,c_141])).

tff(c_117135,plain,(
    ! [D_116363,A_116364,C_116365,E_116366] :
      ( ~ r2_hidden(D_116363,A_116364)
      | k3_mcart_1(C_116365,D_116363,E_116366) != '#skF_5'(A_116364)
      | k1_xboole_0 = A_116364 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_117149,plain,(
    ! [C_116365,C_16,E_116366] :
      ( k3_mcart_1(C_116365,C_16,E_116366) != '#skF_5'(k1_tarski(C_16))
      | k1_tarski(C_16) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_117135])).

tff(c_117157,plain,(
    ! [C_116365,C_16,E_116366] :
      ( k3_mcart_1(C_116365,C_16,E_116366) != C_16
      | k1_tarski(C_16) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116264,c_117149])).

tff(c_117158,plain,(
    ! [C_116365,C_16,E_116366] : k3_mcart_1(C_116365,C_16,E_116366) != C_16 ),
    inference(negUnitSimplification,[status(thm)],[c_116260,c_117157])).

tff(c_74,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_110137,plain,(
    ! [A_76799,B_76800,C_76801] : k4_tarski(k4_tarski(A_76799,B_76800),C_76801) = k3_mcart_1(A_76799,B_76800,C_76801) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    ! [A_52,B_53] : k2_mcart_1(k4_tarski(A_52,B_53)) = B_53 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,(
    ! [B_31,C_32] : k2_mcart_1(k4_tarski(B_31,C_32)) != k4_tarski(B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_82,plain,(
    ! [B_31,C_32] : k4_tarski(B_31,C_32) != C_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_56])).

tff(c_110152,plain,(
    ! [A_76799,B_76800,C_76801] : k3_mcart_1(A_76799,B_76800,C_76801) != C_76801 ),
    inference(superposition,[status(thm),theory(equality)],[c_110137,c_82])).

tff(c_192,plain,(
    ! [A_86,B_87] : k4_xboole_0(A_86,k4_xboole_0(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_192])).

tff(c_210,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_207])).

tff(c_273,plain,(
    ! [B_92,A_93] :
      ( ~ r2_hidden(B_92,A_93)
      | k4_xboole_0(A_93,k1_tarski(B_92)) != A_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_277,plain,(
    ! [B_92] :
      ( ~ r2_hidden(B_92,k1_tarski(B_92))
      | k1_tarski(B_92) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_273])).

tff(c_282,plain,(
    ! [B_92] : k1_tarski(B_92) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_277])).

tff(c_311,plain,(
    ! [A_12] : '#skF_5'(k1_tarski(A_12)) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_141])).

tff(c_408,plain,(
    ! [C_118,A_119,D_120,E_121] :
      ( ~ r2_hidden(C_118,A_119)
      | k3_mcart_1(C_118,D_120,E_121) != '#skF_5'(A_119)
      | k1_xboole_0 = A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_422,plain,(
    ! [C_16,D_120,E_121] :
      ( k3_mcart_1(C_16,D_120,E_121) != '#skF_5'(k1_tarski(C_16))
      | k1_tarski(C_16) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_408])).

tff(c_430,plain,(
    ! [C_16,D_120,E_121] :
      ( k3_mcart_1(C_16,D_120,E_121) != C_16
      | k1_tarski(C_16) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_422])).

tff(c_431,plain,(
    ! [C_16,D_120,E_121] : k3_mcart_1(C_16,D_120,E_121) != C_16 ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_430])).

tff(c_72,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_167,plain,(
    k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_106930,plain,(
    ! [A_76216,B_76217,C_76218,D_76219] :
      ( k3_mcart_1(k5_mcart_1(A_76216,B_76217,C_76218,D_76219),k6_mcart_1(A_76216,B_76217,C_76218,D_76219),k7_mcart_1(A_76216,B_76217,C_76218,D_76219)) = D_76219
      | ~ m1_subset_1(D_76219,k3_zfmisc_1(A_76216,B_76217,C_76218))
      | k1_xboole_0 = C_76218
      | k1_xboole_0 = B_76217
      | k1_xboole_0 = A_76216 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_109993,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_106930])).

tff(c_110003,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_109993])).

tff(c_110005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_431,c_110003])).

tff(c_110006,plain,
    ( k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_110014,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_110006])).

tff(c_116079,plain,(
    ! [A_113914,B_113915,C_113916,D_113917] :
      ( k3_mcart_1(k5_mcart_1(A_113914,B_113915,C_113916,D_113917),k6_mcart_1(A_113914,B_113915,C_113916,D_113917),k7_mcart_1(A_113914,B_113915,C_113916,D_113917)) = D_113917
      | ~ m1_subset_1(D_113917,k3_zfmisc_1(A_113914,B_113915,C_113916))
      | k1_xboole_0 = C_113916
      | k1_xboole_0 = B_113915
      | k1_xboole_0 = A_113914 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_116190,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_110014,c_116079])).

tff(c_116194,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_116190])).

tff(c_116196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_110152,c_116194])).

tff(c_116197,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_110006])).

tff(c_154036,plain,(
    ! [A_166339,B_166340,C_166341,D_166342] :
      ( k3_mcart_1(k5_mcart_1(A_166339,B_166340,C_166341,D_166342),k6_mcart_1(A_166339,B_166340,C_166341,D_166342),k7_mcart_1(A_166339,B_166340,C_166341,D_166342)) = D_166342
      | ~ m1_subset_1(D_166342,k3_zfmisc_1(A_166339,B_166340,C_166341))
      | k1_xboole_0 = C_166341
      | k1_xboole_0 = B_166340
      | k1_xboole_0 = A_166339 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_155131,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_116197,c_154036])).

tff(c_155137,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_155131])).

tff(c_155139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_78,c_76,c_117158,c_155137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.35/12.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.35/12.80  
% 23.35/12.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.35/12.80  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_4
% 23.35/12.80  
% 23.35/12.80  %Foreground sorts:
% 23.35/12.80  
% 23.35/12.80  
% 23.35/12.80  %Background operators:
% 23.35/12.80  
% 23.35/12.80  
% 23.35/12.80  %Foreground operators:
% 23.35/12.80  tff('#skF_5', type, '#skF_5': $i > $i).
% 23.35/12.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.35/12.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.35/12.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 23.35/12.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.35/12.80  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 23.35/12.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.35/12.80  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 23.35/12.80  tff('#skF_7', type, '#skF_7': $i).
% 23.35/12.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 23.35/12.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.35/12.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 23.35/12.80  tff('#skF_6', type, '#skF_6': $i).
% 23.35/12.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.35/12.80  tff('#skF_9', type, '#skF_9': $i).
% 23.35/12.80  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 23.35/12.80  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 23.35/12.80  tff('#skF_8', type, '#skF_8': $i).
% 23.35/12.80  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 23.35/12.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.35/12.80  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 23.35/12.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.35/12.80  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 23.35/12.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.35/12.80  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 23.35/12.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.35/12.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 23.35/12.80  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 23.35/12.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.35/12.80  
% 23.35/12.81  tff(f_135, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 23.35/12.81  tff(f_53, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 23.35/12.81  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 23.35/12.81  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 23.35/12.81  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 23.35/12.81  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 23.35/12.81  tff(f_91, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 23.35/12.81  tff(f_64, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 23.35/12.81  tff(f_111, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 23.35/12.81  tff(f_75, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 23.35/12.81  tff(f_107, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 23.35/12.81  tff(c_80, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_135])).
% 23.35/12.81  tff(c_78, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_135])).
% 23.35/12.81  tff(c_76, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_135])).
% 23.35/12.81  tff(c_34, plain, (![C_16]: (r2_hidden(C_16, k1_tarski(C_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.35/12.81  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.35/12.81  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.35/12.81  tff(c_116218, plain, (![A_114203, B_114204]: (k4_xboole_0(A_114203, k4_xboole_0(A_114203, B_114204))=k3_xboole_0(A_114203, B_114204))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.35/12.81  tff(c_116233, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_116218])).
% 23.35/12.81  tff(c_116237, plain, (![A_114205]: (k4_xboole_0(A_114205, A_114205)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_116233])).
% 23.35/12.81  tff(c_48, plain, (![B_21, A_20]: (~r2_hidden(B_21, A_20) | k4_xboole_0(A_20, k1_tarski(B_21))!=A_20)), inference(cnfTransformation, [status(thm)], [f_62])).
% 23.35/12.81  tff(c_116246, plain, (![B_21]: (~r2_hidden(B_21, k1_tarski(B_21)) | k1_tarski(B_21)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_116237, c_48])).
% 23.35/12.81  tff(c_116260, plain, (![B_21]: (k1_tarski(B_21)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_116246])).
% 23.35/12.81  tff(c_136, plain, (![A_72]: (r2_hidden('#skF_5'(A_72), A_72) | k1_xboole_0=A_72)), inference(cnfTransformation, [status(thm)], [f_91])).
% 23.35/12.81  tff(c_32, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.35/12.81  tff(c_141, plain, (![A_12]: ('#skF_5'(k1_tarski(A_12))=A_12 | k1_tarski(A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_136, c_32])).
% 23.35/12.81  tff(c_116264, plain, (![A_12]: ('#skF_5'(k1_tarski(A_12))=A_12)), inference(negUnitSimplification, [status(thm)], [c_116260, c_141])).
% 23.35/12.81  tff(c_117135, plain, (![D_116363, A_116364, C_116365, E_116366]: (~r2_hidden(D_116363, A_116364) | k3_mcart_1(C_116365, D_116363, E_116366)!='#skF_5'(A_116364) | k1_xboole_0=A_116364)), inference(cnfTransformation, [status(thm)], [f_91])).
% 23.35/12.81  tff(c_117149, plain, (![C_116365, C_16, E_116366]: (k3_mcart_1(C_116365, C_16, E_116366)!='#skF_5'(k1_tarski(C_16)) | k1_tarski(C_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_117135])).
% 23.35/12.81  tff(c_117157, plain, (![C_116365, C_16, E_116366]: (k3_mcart_1(C_116365, C_16, E_116366)!=C_16 | k1_tarski(C_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_116264, c_117149])).
% 23.35/12.81  tff(c_117158, plain, (![C_116365, C_16, E_116366]: (k3_mcart_1(C_116365, C_16, E_116366)!=C_16)), inference(negUnitSimplification, [status(thm)], [c_116260, c_117157])).
% 23.35/12.81  tff(c_74, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 23.35/12.81  tff(c_110137, plain, (![A_76799, B_76800, C_76801]: (k4_tarski(k4_tarski(A_76799, B_76800), C_76801)=k3_mcart_1(A_76799, B_76800, C_76801))), inference(cnfTransformation, [status(thm)], [f_64])).
% 23.35/12.81  tff(c_70, plain, (![A_52, B_53]: (k2_mcart_1(k4_tarski(A_52, B_53))=B_53)), inference(cnfTransformation, [status(thm)], [f_111])).
% 23.35/12.81  tff(c_56, plain, (![B_31, C_32]: (k2_mcart_1(k4_tarski(B_31, C_32))!=k4_tarski(B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.35/12.81  tff(c_82, plain, (![B_31, C_32]: (k4_tarski(B_31, C_32)!=C_32)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_56])).
% 23.35/12.81  tff(c_110152, plain, (![A_76799, B_76800, C_76801]: (k3_mcart_1(A_76799, B_76800, C_76801)!=C_76801)), inference(superposition, [status(thm), theory('equality')], [c_110137, c_82])).
% 23.35/12.81  tff(c_192, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k4_xboole_0(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.35/12.81  tff(c_207, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_192])).
% 23.35/12.81  tff(c_210, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_207])).
% 23.35/12.81  tff(c_273, plain, (![B_92, A_93]: (~r2_hidden(B_92, A_93) | k4_xboole_0(A_93, k1_tarski(B_92))!=A_93)), inference(cnfTransformation, [status(thm)], [f_62])).
% 23.35/12.81  tff(c_277, plain, (![B_92]: (~r2_hidden(B_92, k1_tarski(B_92)) | k1_tarski(B_92)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_210, c_273])).
% 23.35/12.81  tff(c_282, plain, (![B_92]: (k1_tarski(B_92)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_277])).
% 23.35/12.81  tff(c_311, plain, (![A_12]: ('#skF_5'(k1_tarski(A_12))=A_12)), inference(negUnitSimplification, [status(thm)], [c_282, c_141])).
% 23.35/12.81  tff(c_408, plain, (![C_118, A_119, D_120, E_121]: (~r2_hidden(C_118, A_119) | k3_mcart_1(C_118, D_120, E_121)!='#skF_5'(A_119) | k1_xboole_0=A_119)), inference(cnfTransformation, [status(thm)], [f_91])).
% 23.35/12.81  tff(c_422, plain, (![C_16, D_120, E_121]: (k3_mcart_1(C_16, D_120, E_121)!='#skF_5'(k1_tarski(C_16)) | k1_tarski(C_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_408])).
% 23.35/12.81  tff(c_430, plain, (![C_16, D_120, E_121]: (k3_mcart_1(C_16, D_120, E_121)!=C_16 | k1_tarski(C_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_311, c_422])).
% 23.35/12.81  tff(c_431, plain, (![C_16, D_120, E_121]: (k3_mcart_1(C_16, D_120, E_121)!=C_16)), inference(negUnitSimplification, [status(thm)], [c_282, c_430])).
% 23.35/12.81  tff(c_72, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_135])).
% 23.35/12.81  tff(c_167, plain, (k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_72])).
% 23.35/12.81  tff(c_106930, plain, (![A_76216, B_76217, C_76218, D_76219]: (k3_mcart_1(k5_mcart_1(A_76216, B_76217, C_76218, D_76219), k6_mcart_1(A_76216, B_76217, C_76218, D_76219), k7_mcart_1(A_76216, B_76217, C_76218, D_76219))=D_76219 | ~m1_subset_1(D_76219, k3_zfmisc_1(A_76216, B_76217, C_76218)) | k1_xboole_0=C_76218 | k1_xboole_0=B_76217 | k1_xboole_0=A_76216)), inference(cnfTransformation, [status(thm)], [f_107])).
% 23.35/12.81  tff(c_109993, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_167, c_106930])).
% 23.35/12.81  tff(c_110003, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_109993])).
% 23.35/12.81  tff(c_110005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_431, c_110003])).
% 23.35/12.81  tff(c_110006, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_72])).
% 23.35/12.81  tff(c_110014, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_110006])).
% 23.35/12.81  tff(c_116079, plain, (![A_113914, B_113915, C_113916, D_113917]: (k3_mcart_1(k5_mcart_1(A_113914, B_113915, C_113916, D_113917), k6_mcart_1(A_113914, B_113915, C_113916, D_113917), k7_mcart_1(A_113914, B_113915, C_113916, D_113917))=D_113917 | ~m1_subset_1(D_113917, k3_zfmisc_1(A_113914, B_113915, C_113916)) | k1_xboole_0=C_113916 | k1_xboole_0=B_113915 | k1_xboole_0=A_113914)), inference(cnfTransformation, [status(thm)], [f_107])).
% 23.35/12.81  tff(c_116190, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_110014, c_116079])).
% 23.35/12.81  tff(c_116194, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_116190])).
% 23.35/12.81  tff(c_116196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_110152, c_116194])).
% 23.35/12.81  tff(c_116197, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_110006])).
% 23.35/12.81  tff(c_154036, plain, (![A_166339, B_166340, C_166341, D_166342]: (k3_mcart_1(k5_mcart_1(A_166339, B_166340, C_166341, D_166342), k6_mcart_1(A_166339, B_166340, C_166341, D_166342), k7_mcart_1(A_166339, B_166340, C_166341, D_166342))=D_166342 | ~m1_subset_1(D_166342, k3_zfmisc_1(A_166339, B_166340, C_166341)) | k1_xboole_0=C_166341 | k1_xboole_0=B_166340 | k1_xboole_0=A_166339)), inference(cnfTransformation, [status(thm)], [f_107])).
% 23.35/12.81  tff(c_155131, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_116197, c_154036])).
% 23.35/12.81  tff(c_155137, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_155131])).
% 23.35/12.81  tff(c_155139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_78, c_76, c_117158, c_155137])).
% 23.35/12.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.35/12.81  
% 23.35/12.81  Inference rules
% 23.35/12.81  ----------------------
% 23.35/12.81  #Ref     : 0
% 23.35/12.81  #Sup     : 19685
% 23.35/12.81  #Fact    : 6
% 23.35/12.81  #Define  : 0
% 23.35/12.81  #Split   : 14
% 23.35/12.81  #Chain   : 0
% 23.35/12.81  #Close   : 0
% 23.35/12.81  
% 23.35/12.81  Ordering : KBO
% 23.35/12.81  
% 23.35/12.81  Simplification rules
% 23.35/12.81  ----------------------
% 23.35/12.81  #Subsume      : 3183
% 23.35/12.81  #Demod        : 9086
% 23.35/12.81  #Tautology    : 676
% 23.35/12.81  #SimpNegUnit  : 388
% 23.35/12.81  #BackRed      : 3
% 23.35/12.81  
% 23.35/12.81  #Partial instantiations: 59528
% 23.35/12.81  #Strategies tried      : 1
% 23.35/12.81  
% 23.35/12.81  Timing (in seconds)
% 23.35/12.81  ----------------------
% 23.35/12.82  Preprocessing        : 0.36
% 23.35/12.82  Parsing              : 0.18
% 23.35/12.82  CNF conversion       : 0.03
% 23.35/12.82  Main loop            : 11.69
% 23.35/12.82  Inferencing          : 3.51
% 23.35/12.82  Reduction            : 3.32
% 23.35/12.82  Demodulation         : 2.23
% 23.35/12.82  BG Simplification    : 0.53
% 23.35/12.82  Subsumption          : 3.94
% 23.35/12.82  Abstraction          : 0.87
% 23.35/12.82  MUC search           : 0.00
% 23.35/12.82  Cooper               : 0.00
% 23.35/12.82  Total                : 12.08
% 23.35/12.82  Index Insertion      : 0.00
% 23.35/12.82  Index Deletion       : 0.00
% 23.35/12.82  Index Matching       : 0.00
% 23.35/12.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
