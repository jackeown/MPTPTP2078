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
% DateTime   : Thu Dec  3 09:53:45 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 990 expanded)
%              Number of leaves         :   30 ( 299 expanded)
%              Depth                    :   14
%              Number of atoms          :  309 (2145 expanded)
%              Number of equality atoms :  151 (1592 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
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

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_142,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_188,plain,(
    ! [E_73,F_74,A_75,B_76] :
      ( r2_hidden(k4_tarski(E_73,F_74),k2_zfmisc_1(A_75,B_76))
      | ~ r2_hidden(F_74,B_76)
      | ~ r2_hidden(E_73,A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_193,plain,(
    ! [E_73,F_74] :
      ( r2_hidden(k4_tarski(E_73,F_74),k1_xboole_0)
      | ~ r2_hidden(F_74,'#skF_12')
      | ~ r2_hidden(E_73,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_188])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_195,plain,(
    ! [E_77,F_78] :
      ( r2_hidden(k4_tarski(E_77,F_78),k1_xboole_0)
      | ~ r2_hidden(F_78,'#skF_12')
      | ~ r2_hidden(E_77,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_188])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_147,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,B_64)
      | ~ r2_hidden(C_65,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    ! [C_65,B_13,A_12] :
      ( ~ r2_hidden(C_65,B_13)
      | ~ r2_hidden(C_65,A_12)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(resolution,[status(thm)],[c_18,c_147])).

tff(c_197,plain,(
    ! [E_77,F_78,A_12] :
      ( ~ r2_hidden(k4_tarski(E_77,F_78),A_12)
      | k4_xboole_0(A_12,k1_xboole_0) != A_12
      | ~ r2_hidden(F_78,'#skF_12')
      | ~ r2_hidden(E_77,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_195,c_150])).

tff(c_201,plain,(
    ! [E_79,F_80,A_81] :
      ( ~ r2_hidden(k4_tarski(E_79,F_80),A_81)
      | ~ r2_hidden(F_80,'#skF_12')
      | ~ r2_hidden(E_79,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_197])).

tff(c_208,plain,(
    ! [F_74,E_73] :
      ( ~ r2_hidden(F_74,'#skF_12')
      | ~ r2_hidden(E_73,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_193,c_201])).

tff(c_211,plain,(
    ! [E_82] : ~ r2_hidden(E_82,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_223,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_8,c_211])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_223])).

tff(c_231,plain,(
    ! [F_83] : ~ r2_hidden(F_83,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_243,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_8,c_231])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_243])).

tff(c_250,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_252,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_255,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_8])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_258,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_252,c_10])).

tff(c_281,plain,(
    ! [A_85] : k4_xboole_0(A_85,'#skF_10') = A_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_12])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_287,plain,(
    ! [A_85] : k4_xboole_0(A_85,A_85) = k3_xboole_0(A_85,'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_14])).

tff(c_292,plain,(
    ! [A_85] : k4_xboole_0(A_85,A_85) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_287])).

tff(c_24,plain,(
    ! [A_14,B_15,D_41] :
      ( r2_hidden('#skF_8'(A_14,B_15,k2_zfmisc_1(A_14,B_15),D_41),B_15)
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_556,plain,(
    ! [A_118,B_119,D_120] :
      ( r2_hidden('#skF_8'(A_118,B_119,k2_zfmisc_1(A_118,B_119),D_120),B_119)
      | ~ r2_hidden(D_120,k2_zfmisc_1(A_118,B_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_295,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,B_87)
      | ~ r2_hidden(C_88,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_298,plain,(
    ! [C_88,B_13,A_12] :
      ( ~ r2_hidden(C_88,B_13)
      | ~ r2_hidden(C_88,A_12)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(resolution,[status(thm)],[c_18,c_295])).

tff(c_7801,plain,(
    ! [A_337,B_338,D_339,A_340] :
      ( ~ r2_hidden('#skF_8'(A_337,B_338,k2_zfmisc_1(A_337,B_338),D_339),A_340)
      | k4_xboole_0(A_340,B_338) != A_340
      | ~ r2_hidden(D_339,k2_zfmisc_1(A_337,B_338)) ) ),
    inference(resolution,[status(thm)],[c_556,c_298])).

tff(c_7804,plain,(
    ! [B_15,D_41,A_14] :
      ( k4_xboole_0(B_15,B_15) != B_15
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(resolution,[status(thm)],[c_24,c_7801])).

tff(c_7808,plain,(
    ! [B_341,D_342,A_343] :
      ( B_341 != '#skF_10'
      | ~ r2_hidden(D_342,k2_zfmisc_1(A_343,B_341)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_7804])).

tff(c_7872,plain,(
    ! [A_343] : k2_zfmisc_1(A_343,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_255,c_7808])).

tff(c_52,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_74,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_254,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_74])).

tff(c_7875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7872,c_254])).

tff(c_7876,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_7882,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7876,c_8])).

tff(c_81,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_96,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_81])).

tff(c_99,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_96])).

tff(c_7880,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7876,c_99])).

tff(c_26,plain,(
    ! [A_14,B_15,D_41] :
      ( r2_hidden('#skF_7'(A_14,B_15,k2_zfmisc_1(A_14,B_15),D_41),A_14)
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8039,plain,(
    ! [A_367,B_368,D_369] :
      ( r2_hidden('#skF_7'(A_367,B_368,k2_zfmisc_1(A_367,B_368),D_369),A_367)
      | ~ r2_hidden(D_369,k2_zfmisc_1(A_367,B_368)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7941,plain,(
    ! [A_347,B_348,C_349] :
      ( ~ r1_xboole_0(A_347,B_348)
      | ~ r2_hidden(C_349,B_348)
      | ~ r2_hidden(C_349,A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7944,plain,(
    ! [C_349,B_13,A_12] :
      ( ~ r2_hidden(C_349,B_13)
      | ~ r2_hidden(C_349,A_12)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(resolution,[status(thm)],[c_18,c_7941])).

tff(c_14446,plain,(
    ! [A_591,B_592,D_593,A_594] :
      ( ~ r2_hidden('#skF_7'(A_591,B_592,k2_zfmisc_1(A_591,B_592),D_593),A_594)
      | k4_xboole_0(A_594,A_591) != A_594
      | ~ r2_hidden(D_593,k2_zfmisc_1(A_591,B_592)) ) ),
    inference(resolution,[status(thm)],[c_8039,c_7944])).

tff(c_14449,plain,(
    ! [A_14,D_41,B_15] :
      ( k4_xboole_0(A_14,A_14) != A_14
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(resolution,[status(thm)],[c_26,c_14446])).

tff(c_14453,plain,(
    ! [A_595,D_596,B_597] :
      ( A_595 != '#skF_9'
      | ~ r2_hidden(D_596,k2_zfmisc_1(A_595,B_597)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7880,c_14449])).

tff(c_14517,plain,(
    ! [B_597] : k2_zfmisc_1('#skF_9',B_597) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_7882,c_14453])).

tff(c_7881,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7876,c_74])).

tff(c_14520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14517,c_7881])).

tff(c_14521,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_14603,plain,(
    ! [E_613,F_614,A_615,B_616] :
      ( r2_hidden(k4_tarski(E_613,F_614),k2_zfmisc_1(A_615,B_616))
      | ~ r2_hidden(F_614,B_616)
      | ~ r2_hidden(E_613,A_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14609,plain,(
    ! [E_613,F_614] :
      ( r2_hidden(k4_tarski(E_613,F_614),k1_xboole_0)
      | ~ r2_hidden(F_614,'#skF_12')
      | ~ r2_hidden(E_613,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14521,c_14603])).

tff(c_14650,plain,(
    ! [E_624,F_625] :
      ( r2_hidden(k4_tarski(E_624,F_625),k1_xboole_0)
      | ~ r2_hidden(F_625,'#skF_12')
      | ~ r2_hidden(E_624,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14521,c_14603])).

tff(c_14599,plain,(
    ! [A_610,B_611,C_612] :
      ( ~ r1_xboole_0(A_610,B_611)
      | ~ r2_hidden(C_612,B_611)
      | ~ r2_hidden(C_612,A_610) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14602,plain,(
    ! [C_612,B_13,A_12] :
      ( ~ r2_hidden(C_612,B_13)
      | ~ r2_hidden(C_612,A_12)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(resolution,[status(thm)],[c_18,c_14599])).

tff(c_14652,plain,(
    ! [E_624,F_625,A_12] :
      ( ~ r2_hidden(k4_tarski(E_624,F_625),A_12)
      | k4_xboole_0(A_12,k1_xboole_0) != A_12
      | ~ r2_hidden(F_625,'#skF_12')
      | ~ r2_hidden(E_624,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_14650,c_14602])).

tff(c_14682,plain,(
    ! [E_633,F_634,A_635] :
      ( ~ r2_hidden(k4_tarski(E_633,F_634),A_635)
      | ~ r2_hidden(F_634,'#skF_12')
      | ~ r2_hidden(E_633,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14652])).

tff(c_14693,plain,(
    ! [F_614,E_613] :
      ( ~ r2_hidden(F_614,'#skF_12')
      | ~ r2_hidden(E_613,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_14609,c_14682])).

tff(c_14696,plain,(
    ! [E_636] : ~ r2_hidden(E_636,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_14693])).

tff(c_14712,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_8,c_14696])).

tff(c_14719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_14712])).

tff(c_14722,plain,(
    ! [F_637] : ~ r2_hidden(F_637,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_14693])).

tff(c_14738,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_8,c_14722])).

tff(c_14745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_14738])).

tff(c_14747,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_22889,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14747,c_8])).

tff(c_14749,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14747,c_14747,c_10])).

tff(c_14750,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_12') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14747,c_12])).

tff(c_22903,plain,(
    ! [A_929,B_930] : k4_xboole_0(A_929,k4_xboole_0(A_929,B_930)) = k3_xboole_0(A_929,B_930) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22918,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_14750,c_22903])).

tff(c_22921,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14749,c_22918])).

tff(c_23001,plain,(
    ! [A_945,B_946,D_947] :
      ( r2_hidden('#skF_8'(A_945,B_946,k2_zfmisc_1(A_945,B_946),D_947),B_946)
      | ~ r2_hidden(D_947,k2_zfmisc_1(A_945,B_946)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22962,plain,(
    ! [A_933,B_934,C_935] :
      ( ~ r1_xboole_0(A_933,B_934)
      | ~ r2_hidden(C_935,B_934)
      | ~ r2_hidden(C_935,A_933) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22965,plain,(
    ! [C_935,B_13,A_12] :
      ( ~ r2_hidden(C_935,B_13)
      | ~ r2_hidden(C_935,A_12)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(resolution,[status(thm)],[c_18,c_22962])).

tff(c_30041,plain,(
    ! [A_1185,B_1186,D_1187,A_1188] :
      ( ~ r2_hidden('#skF_8'(A_1185,B_1186,k2_zfmisc_1(A_1185,B_1186),D_1187),A_1188)
      | k4_xboole_0(A_1188,B_1186) != A_1188
      | ~ r2_hidden(D_1187,k2_zfmisc_1(A_1185,B_1186)) ) ),
    inference(resolution,[status(thm)],[c_23001,c_22965])).

tff(c_30044,plain,(
    ! [B_15,D_41,A_14] :
      ( k4_xboole_0(B_15,B_15) != B_15
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(resolution,[status(thm)],[c_24,c_30041])).

tff(c_30048,plain,(
    ! [B_1189,D_1190,A_1191] :
      ( B_1189 != '#skF_12'
      | ~ r2_hidden(D_1190,k2_zfmisc_1(A_1191,B_1189)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22921,c_30044])).

tff(c_30113,plain,(
    ! [B_1192,A_1193] :
      ( B_1192 != '#skF_12'
      | k2_zfmisc_1(A_1193,B_1192) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_22889,c_30048])).

tff(c_30046,plain,(
    ! [B_15,D_41,A_14] :
      ( B_15 != '#skF_12'
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22921,c_30044])).

tff(c_30119,plain,(
    ! [B_1192,D_41] :
      ( B_1192 != '#skF_12'
      | ~ r2_hidden(D_41,'#skF_12')
      | B_1192 != '#skF_12' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30113,c_30046])).

tff(c_30178,plain,(
    ! [B_1192] :
      ( B_1192 != '#skF_12'
      | B_1192 != '#skF_12' ) ),
    inference(splitLeft,[status(thm)],[c_30119])).

tff(c_30184,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_30178])).

tff(c_30186,plain,(
    ! [D_1200] : ~ r2_hidden(D_1200,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_30119])).

tff(c_30237,plain,(
    ! [D_1201,B_1202] : ~ r2_hidden(D_1201,k2_zfmisc_1('#skF_12',B_1202)) ),
    inference(resolution,[status(thm)],[c_26,c_30186])).

tff(c_30305,plain,(
    ! [B_1202] : k2_zfmisc_1('#skF_12',B_1202) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_22889,c_30237])).

tff(c_14779,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14747,c_8])).

tff(c_14791,plain,(
    ! [A_647,B_648] : k4_xboole_0(A_647,k4_xboole_0(A_647,B_648)) = k3_xboole_0(A_647,B_648) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14806,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_14750,c_14791])).

tff(c_14809,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14749,c_14806])).

tff(c_14915,plain,(
    ! [A_672,B_673,D_674] :
      ( r2_hidden('#skF_8'(A_672,B_673,k2_zfmisc_1(A_672,B_673),D_674),B_673)
      | ~ r2_hidden(D_674,k2_zfmisc_1(A_672,B_673)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14851,plain,(
    ! [A_653,B_654,C_655] :
      ( ~ r1_xboole_0(A_653,B_654)
      | ~ r2_hidden(C_655,B_654)
      | ~ r2_hidden(C_655,A_653) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14854,plain,(
    ! [C_655,B_13,A_12] :
      ( ~ r2_hidden(C_655,B_13)
      | ~ r2_hidden(C_655,A_12)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(resolution,[status(thm)],[c_18,c_14851])).

tff(c_22790,plain,(
    ! [A_911,B_912,D_913,A_914] :
      ( ~ r2_hidden('#skF_8'(A_911,B_912,k2_zfmisc_1(A_911,B_912),D_913),A_914)
      | k4_xboole_0(A_914,B_912) != A_914
      | ~ r2_hidden(D_913,k2_zfmisc_1(A_911,B_912)) ) ),
    inference(resolution,[status(thm)],[c_14915,c_14854])).

tff(c_22793,plain,(
    ! [B_15,D_41,A_14] :
      ( k4_xboole_0(B_15,B_15) != B_15
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(resolution,[status(thm)],[c_24,c_22790])).

tff(c_22797,plain,(
    ! [B_915,D_916,A_917] :
      ( B_915 != '#skF_12'
      | ~ r2_hidden(D_916,k2_zfmisc_1(A_917,B_915)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14809,c_22793])).

tff(c_22861,plain,(
    ! [A_917] : k2_zfmisc_1(A_917,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_14779,c_22797])).

tff(c_14746,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_14755,plain,
    ( '#skF_9' = '#skF_12'
    | '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14747,c_14747,c_14746])).

tff(c_14756,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_14755])).

tff(c_44,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14778,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14747,c_14756,c_14747,c_44])).

tff(c_22864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22861,c_14778])).

tff(c_22865,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_14755])).

tff(c_22872,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14747,c_22865,c_14747,c_44])).

tff(c_30309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30305,c_22872])).

tff(c_30311,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_30310,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_30318,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30311,c_30311,c_30310])).

tff(c_30319,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_30318])).

tff(c_30320,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30319,c_30311])).

tff(c_30350,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30320,c_8])).

tff(c_30312,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30311,c_30311,c_10])).

tff(c_30331,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30319,c_30319,c_30312])).

tff(c_30313,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_11') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30311,c_12])).

tff(c_30339,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_10') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30319,c_30313])).

tff(c_30363,plain,(
    ! [A_1214,B_1215] : k4_xboole_0(A_1214,k4_xboole_0(A_1214,B_1215)) = k3_xboole_0(A_1214,B_1215) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30378,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_30339,c_30363])).

tff(c_30381,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30331,c_30378])).

tff(c_30548,plain,(
    ! [A_1244,B_1245,D_1246] :
      ( r2_hidden('#skF_7'(A_1244,B_1245,k2_zfmisc_1(A_1244,B_1245),D_1246),A_1244)
      | ~ r2_hidden(D_1246,k2_zfmisc_1(A_1244,B_1245)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30422,plain,(
    ! [A_1218,B_1219,C_1220] :
      ( ~ r1_xboole_0(A_1218,B_1219)
      | ~ r2_hidden(C_1220,B_1219)
      | ~ r2_hidden(C_1220,A_1218) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30425,plain,(
    ! [C_1220,B_13,A_12] :
      ( ~ r2_hidden(C_1220,B_13)
      | ~ r2_hidden(C_1220,A_12)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(resolution,[status(thm)],[c_18,c_30422])).

tff(c_37911,plain,(
    ! [A_1472,B_1473,D_1474,A_1475] :
      ( ~ r2_hidden('#skF_7'(A_1472,B_1473,k2_zfmisc_1(A_1472,B_1473),D_1474),A_1475)
      | k4_xboole_0(A_1475,A_1472) != A_1475
      | ~ r2_hidden(D_1474,k2_zfmisc_1(A_1472,B_1473)) ) ),
    inference(resolution,[status(thm)],[c_30548,c_30425])).

tff(c_37914,plain,(
    ! [A_14,D_41,B_15] :
      ( k4_xboole_0(A_14,A_14) != A_14
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(resolution,[status(thm)],[c_26,c_37911])).

tff(c_37918,plain,(
    ! [A_1476,D_1477,B_1478] :
      ( A_1476 != '#skF_10'
      | ~ r2_hidden(D_1477,k2_zfmisc_1(A_1476,B_1478)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30381,c_37914])).

tff(c_37983,plain,(
    ! [A_1479,B_1480] :
      ( A_1479 != '#skF_10'
      | k2_zfmisc_1(A_1479,B_1480) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_30350,c_37918])).

tff(c_37916,plain,(
    ! [A_14,D_41,B_15] :
      ( A_14 != '#skF_10'
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30381,c_37914])).

tff(c_37989,plain,(
    ! [A_1479,D_41] :
      ( A_1479 != '#skF_10'
      | ~ r2_hidden(D_41,'#skF_10')
      | A_1479 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37983,c_37916])).

tff(c_38048,plain,(
    ! [A_1479] :
      ( A_1479 != '#skF_10'
      | A_1479 != '#skF_10' ) ),
    inference(splitLeft,[status(thm)],[c_37989])).

tff(c_38054,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_38048])).

tff(c_38056,plain,(
    ! [D_1487] : ~ r2_hidden(D_1487,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_37989])).

tff(c_38107,plain,(
    ! [D_1488,A_1489] : ~ r2_hidden(D_1488,k2_zfmisc_1(A_1489,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_24,c_38056])).

tff(c_38175,plain,(
    ! [A_1489] : k2_zfmisc_1(A_1489,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_30350,c_38107])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30330,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30320,c_30319,c_30320,c_48])).

tff(c_38188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38175,c_30330])).

tff(c_38189,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_30318])).

tff(c_38191,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38189,c_30311])).

tff(c_38235,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38191,c_8])).

tff(c_38223,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38189,c_38189,c_30312])).

tff(c_38212,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_9') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38189,c_30313])).

tff(c_38243,plain,(
    ! [A_1501,B_1502] : k4_xboole_0(A_1501,k4_xboole_0(A_1501,B_1502)) = k3_xboole_0(A_1501,B_1502) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38258,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_38212,c_38243])).

tff(c_38261,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38223,c_38258])).

tff(c_38458,plain,(
    ! [A_1532,B_1533,D_1534] :
      ( r2_hidden('#skF_7'(A_1532,B_1533,k2_zfmisc_1(A_1532,B_1533),D_1534),A_1532)
      | ~ r2_hidden(D_1534,k2_zfmisc_1(A_1532,B_1533)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38306,plain,(
    ! [A_1509,B_1510,C_1511] :
      ( ~ r1_xboole_0(A_1509,B_1510)
      | ~ r2_hidden(C_1511,B_1510)
      | ~ r2_hidden(C_1511,A_1509) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38309,plain,(
    ! [C_1511,B_13,A_12] :
      ( ~ r2_hidden(C_1511,B_13)
      | ~ r2_hidden(C_1511,A_12)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(resolution,[status(thm)],[c_18,c_38306])).

tff(c_44501,plain,(
    ! [A_1757,B_1758,D_1759,A_1760] :
      ( ~ r2_hidden('#skF_7'(A_1757,B_1758,k2_zfmisc_1(A_1757,B_1758),D_1759),A_1760)
      | k4_xboole_0(A_1760,A_1757) != A_1760
      | ~ r2_hidden(D_1759,k2_zfmisc_1(A_1757,B_1758)) ) ),
    inference(resolution,[status(thm)],[c_38458,c_38309])).

tff(c_44504,plain,(
    ! [A_14,D_41,B_15] :
      ( k4_xboole_0(A_14,A_14) != A_14
      | ~ r2_hidden(D_41,k2_zfmisc_1(A_14,B_15)) ) ),
    inference(resolution,[status(thm)],[c_26,c_44501])).

tff(c_44508,plain,(
    ! [A_1761,D_1762,B_1763] :
      ( A_1761 != '#skF_9'
      | ~ r2_hidden(D_1762,k2_zfmisc_1(A_1761,B_1763)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38261,c_44504])).

tff(c_44572,plain,(
    ! [B_1763] : k2_zfmisc_1('#skF_9',B_1763) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_38235,c_44508])).

tff(c_38197,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38189,c_48])).

tff(c_38198,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_38197])).

tff(c_38204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38191,c_38198])).

tff(c_38205,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38197])).

tff(c_38222,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38191,c_38205])).

tff(c_44575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44572,c_38222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:14:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.41/5.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/5.12  
% 11.41/5.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/5.12  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12
% 11.41/5.12  
% 11.41/5.12  %Foreground sorts:
% 11.41/5.12  
% 11.41/5.12  
% 11.41/5.12  %Background operators:
% 11.41/5.12  
% 11.41/5.12  
% 11.41/5.12  %Foreground operators:
% 11.41/5.12  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.41/5.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.41/5.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.41/5.12  tff('#skF_11', type, '#skF_11': $i).
% 11.41/5.12  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 11.41/5.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.41/5.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.41/5.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.41/5.12  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 11.41/5.12  tff('#skF_10', type, '#skF_10': $i).
% 11.41/5.12  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 11.41/5.12  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.41/5.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.41/5.12  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 11.41/5.12  tff('#skF_9', type, '#skF_9': $i).
% 11.41/5.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.41/5.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.41/5.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.41/5.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.41/5.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.41/5.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.41/5.12  tff('#skF_12', type, '#skF_12': $i).
% 11.41/5.12  
% 11.41/5.15  tff(f_80, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.41/5.15  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 11.41/5.15  tff(f_73, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 11.41/5.15  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 11.41/5.15  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.41/5.15  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.41/5.15  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 11.41/5.15  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.41/5.15  tff(c_46, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.41/5.15  tff(c_72, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_46])).
% 11.41/5.15  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.41/5.15  tff(c_50, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.41/5.15  tff(c_71, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_50])).
% 11.41/5.15  tff(c_54, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.41/5.15  tff(c_142, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 11.41/5.15  tff(c_188, plain, (![E_73, F_74, A_75, B_76]: (r2_hidden(k4_tarski(E_73, F_74), k2_zfmisc_1(A_75, B_76)) | ~r2_hidden(F_74, B_76) | ~r2_hidden(E_73, A_75))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.41/5.15  tff(c_193, plain, (![E_73, F_74]: (r2_hidden(k4_tarski(E_73, F_74), k1_xboole_0) | ~r2_hidden(F_74, '#skF_12') | ~r2_hidden(E_73, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_188])).
% 11.41/5.15  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.41/5.15  tff(c_195, plain, (![E_77, F_78]: (r2_hidden(k4_tarski(E_77, F_78), k1_xboole_0) | ~r2_hidden(F_78, '#skF_12') | ~r2_hidden(E_77, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_188])).
% 11.41/5.15  tff(c_18, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.41/5.15  tff(c_147, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, B_64) | ~r2_hidden(C_65, A_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.41/5.15  tff(c_150, plain, (![C_65, B_13, A_12]: (~r2_hidden(C_65, B_13) | ~r2_hidden(C_65, A_12) | k4_xboole_0(A_12, B_13)!=A_12)), inference(resolution, [status(thm)], [c_18, c_147])).
% 11.41/5.15  tff(c_197, plain, (![E_77, F_78, A_12]: (~r2_hidden(k4_tarski(E_77, F_78), A_12) | k4_xboole_0(A_12, k1_xboole_0)!=A_12 | ~r2_hidden(F_78, '#skF_12') | ~r2_hidden(E_77, '#skF_11'))), inference(resolution, [status(thm)], [c_195, c_150])).
% 11.41/5.15  tff(c_201, plain, (![E_79, F_80, A_81]: (~r2_hidden(k4_tarski(E_79, F_80), A_81) | ~r2_hidden(F_80, '#skF_12') | ~r2_hidden(E_79, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_197])).
% 11.41/5.15  tff(c_208, plain, (![F_74, E_73]: (~r2_hidden(F_74, '#skF_12') | ~r2_hidden(E_73, '#skF_11'))), inference(resolution, [status(thm)], [c_193, c_201])).
% 11.41/5.15  tff(c_211, plain, (![E_82]: (~r2_hidden(E_82, '#skF_11'))), inference(splitLeft, [status(thm)], [c_208])).
% 11.41/5.15  tff(c_223, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_8, c_211])).
% 11.41/5.15  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_223])).
% 11.41/5.15  tff(c_231, plain, (![F_83]: (~r2_hidden(F_83, '#skF_12'))), inference(splitRight, [status(thm)], [c_208])).
% 11.41/5.15  tff(c_243, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_8, c_231])).
% 11.41/5.15  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_243])).
% 11.41/5.15  tff(c_250, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_54])).
% 11.41/5.15  tff(c_252, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_250])).
% 11.41/5.15  tff(c_255, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_8])).
% 11.41/5.15  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.41/5.15  tff(c_258, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_252, c_252, c_10])).
% 11.41/5.15  tff(c_281, plain, (![A_85]: (k4_xboole_0(A_85, '#skF_10')=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_252, c_12])).
% 11.41/5.15  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.41/5.15  tff(c_287, plain, (![A_85]: (k4_xboole_0(A_85, A_85)=k3_xboole_0(A_85, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_281, c_14])).
% 11.41/5.15  tff(c_292, plain, (![A_85]: (k4_xboole_0(A_85, A_85)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_287])).
% 11.41/5.15  tff(c_24, plain, (![A_14, B_15, D_41]: (r2_hidden('#skF_8'(A_14, B_15, k2_zfmisc_1(A_14, B_15), D_41), B_15) | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.41/5.15  tff(c_556, plain, (![A_118, B_119, D_120]: (r2_hidden('#skF_8'(A_118, B_119, k2_zfmisc_1(A_118, B_119), D_120), B_119) | ~r2_hidden(D_120, k2_zfmisc_1(A_118, B_119)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.41/5.15  tff(c_295, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, B_87) | ~r2_hidden(C_88, A_86))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.41/5.15  tff(c_298, plain, (![C_88, B_13, A_12]: (~r2_hidden(C_88, B_13) | ~r2_hidden(C_88, A_12) | k4_xboole_0(A_12, B_13)!=A_12)), inference(resolution, [status(thm)], [c_18, c_295])).
% 11.41/5.15  tff(c_7801, plain, (![A_337, B_338, D_339, A_340]: (~r2_hidden('#skF_8'(A_337, B_338, k2_zfmisc_1(A_337, B_338), D_339), A_340) | k4_xboole_0(A_340, B_338)!=A_340 | ~r2_hidden(D_339, k2_zfmisc_1(A_337, B_338)))), inference(resolution, [status(thm)], [c_556, c_298])).
% 11.41/5.15  tff(c_7804, plain, (![B_15, D_41, A_14]: (k4_xboole_0(B_15, B_15)!=B_15 | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(resolution, [status(thm)], [c_24, c_7801])).
% 11.41/5.15  tff(c_7808, plain, (![B_341, D_342, A_343]: (B_341!='#skF_10' | ~r2_hidden(D_342, k2_zfmisc_1(A_343, B_341)))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_7804])).
% 11.41/5.15  tff(c_7872, plain, (![A_343]: (k2_zfmisc_1(A_343, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_255, c_7808])).
% 11.41/5.15  tff(c_52, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.41/5.15  tff(c_74, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_52])).
% 11.41/5.15  tff(c_254, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_74])).
% 11.41/5.15  tff(c_7875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7872, c_254])).
% 11.41/5.15  tff(c_7876, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_250])).
% 11.41/5.15  tff(c_7882, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7876, c_8])).
% 11.41/5.15  tff(c_81, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.41/5.15  tff(c_96, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_81])).
% 11.41/5.15  tff(c_99, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_96])).
% 11.41/5.15  tff(c_7880, plain, (![A_9]: (k4_xboole_0(A_9, A_9)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7876, c_99])).
% 11.41/5.15  tff(c_26, plain, (![A_14, B_15, D_41]: (r2_hidden('#skF_7'(A_14, B_15, k2_zfmisc_1(A_14, B_15), D_41), A_14) | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.41/5.15  tff(c_8039, plain, (![A_367, B_368, D_369]: (r2_hidden('#skF_7'(A_367, B_368, k2_zfmisc_1(A_367, B_368), D_369), A_367) | ~r2_hidden(D_369, k2_zfmisc_1(A_367, B_368)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.41/5.15  tff(c_7941, plain, (![A_347, B_348, C_349]: (~r1_xboole_0(A_347, B_348) | ~r2_hidden(C_349, B_348) | ~r2_hidden(C_349, A_347))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.41/5.15  tff(c_7944, plain, (![C_349, B_13, A_12]: (~r2_hidden(C_349, B_13) | ~r2_hidden(C_349, A_12) | k4_xboole_0(A_12, B_13)!=A_12)), inference(resolution, [status(thm)], [c_18, c_7941])).
% 11.41/5.15  tff(c_14446, plain, (![A_591, B_592, D_593, A_594]: (~r2_hidden('#skF_7'(A_591, B_592, k2_zfmisc_1(A_591, B_592), D_593), A_594) | k4_xboole_0(A_594, A_591)!=A_594 | ~r2_hidden(D_593, k2_zfmisc_1(A_591, B_592)))), inference(resolution, [status(thm)], [c_8039, c_7944])).
% 11.41/5.15  tff(c_14449, plain, (![A_14, D_41, B_15]: (k4_xboole_0(A_14, A_14)!=A_14 | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(resolution, [status(thm)], [c_26, c_14446])).
% 11.41/5.15  tff(c_14453, plain, (![A_595, D_596, B_597]: (A_595!='#skF_9' | ~r2_hidden(D_596, k2_zfmisc_1(A_595, B_597)))), inference(demodulation, [status(thm), theory('equality')], [c_7880, c_14449])).
% 11.41/5.15  tff(c_14517, plain, (![B_597]: (k2_zfmisc_1('#skF_9', B_597)='#skF_9')), inference(resolution, [status(thm)], [c_7882, c_14453])).
% 11.41/5.15  tff(c_7881, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_7876, c_74])).
% 11.41/5.15  tff(c_14520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14517, c_7881])).
% 11.41/5.15  tff(c_14521, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_52])).
% 11.41/5.15  tff(c_14603, plain, (![E_613, F_614, A_615, B_616]: (r2_hidden(k4_tarski(E_613, F_614), k2_zfmisc_1(A_615, B_616)) | ~r2_hidden(F_614, B_616) | ~r2_hidden(E_613, A_615))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.41/5.15  tff(c_14609, plain, (![E_613, F_614]: (r2_hidden(k4_tarski(E_613, F_614), k1_xboole_0) | ~r2_hidden(F_614, '#skF_12') | ~r2_hidden(E_613, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_14521, c_14603])).
% 11.41/5.15  tff(c_14650, plain, (![E_624, F_625]: (r2_hidden(k4_tarski(E_624, F_625), k1_xboole_0) | ~r2_hidden(F_625, '#skF_12') | ~r2_hidden(E_624, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_14521, c_14603])).
% 11.41/5.15  tff(c_14599, plain, (![A_610, B_611, C_612]: (~r1_xboole_0(A_610, B_611) | ~r2_hidden(C_612, B_611) | ~r2_hidden(C_612, A_610))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.41/5.15  tff(c_14602, plain, (![C_612, B_13, A_12]: (~r2_hidden(C_612, B_13) | ~r2_hidden(C_612, A_12) | k4_xboole_0(A_12, B_13)!=A_12)), inference(resolution, [status(thm)], [c_18, c_14599])).
% 11.41/5.15  tff(c_14652, plain, (![E_624, F_625, A_12]: (~r2_hidden(k4_tarski(E_624, F_625), A_12) | k4_xboole_0(A_12, k1_xboole_0)!=A_12 | ~r2_hidden(F_625, '#skF_12') | ~r2_hidden(E_624, '#skF_11'))), inference(resolution, [status(thm)], [c_14650, c_14602])).
% 11.41/5.15  tff(c_14682, plain, (![E_633, F_634, A_635]: (~r2_hidden(k4_tarski(E_633, F_634), A_635) | ~r2_hidden(F_634, '#skF_12') | ~r2_hidden(E_633, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14652])).
% 11.41/5.15  tff(c_14693, plain, (![F_614, E_613]: (~r2_hidden(F_614, '#skF_12') | ~r2_hidden(E_613, '#skF_11'))), inference(resolution, [status(thm)], [c_14609, c_14682])).
% 11.41/5.15  tff(c_14696, plain, (![E_636]: (~r2_hidden(E_636, '#skF_11'))), inference(splitLeft, [status(thm)], [c_14693])).
% 11.41/5.15  tff(c_14712, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_8, c_14696])).
% 11.41/5.15  tff(c_14719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_14712])).
% 11.41/5.15  tff(c_14722, plain, (![F_637]: (~r2_hidden(F_637, '#skF_12'))), inference(splitRight, [status(thm)], [c_14693])).
% 11.41/5.15  tff(c_14738, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_8, c_14722])).
% 11.41/5.15  tff(c_14745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_14738])).
% 11.41/5.15  tff(c_14747, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_46])).
% 11.41/5.15  tff(c_22889, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_14747, c_8])).
% 11.41/5.15  tff(c_14749, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_14747, c_14747, c_10])).
% 11.41/5.15  tff(c_14750, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_12')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_14747, c_12])).
% 11.41/5.15  tff(c_22903, plain, (![A_929, B_930]: (k4_xboole_0(A_929, k4_xboole_0(A_929, B_930))=k3_xboole_0(A_929, B_930))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.41/5.15  tff(c_22918, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_14750, c_22903])).
% 11.41/5.15  tff(c_22921, plain, (![A_9]: (k4_xboole_0(A_9, A_9)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_14749, c_22918])).
% 11.41/5.15  tff(c_23001, plain, (![A_945, B_946, D_947]: (r2_hidden('#skF_8'(A_945, B_946, k2_zfmisc_1(A_945, B_946), D_947), B_946) | ~r2_hidden(D_947, k2_zfmisc_1(A_945, B_946)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.41/5.15  tff(c_22962, plain, (![A_933, B_934, C_935]: (~r1_xboole_0(A_933, B_934) | ~r2_hidden(C_935, B_934) | ~r2_hidden(C_935, A_933))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.41/5.15  tff(c_22965, plain, (![C_935, B_13, A_12]: (~r2_hidden(C_935, B_13) | ~r2_hidden(C_935, A_12) | k4_xboole_0(A_12, B_13)!=A_12)), inference(resolution, [status(thm)], [c_18, c_22962])).
% 11.41/5.15  tff(c_30041, plain, (![A_1185, B_1186, D_1187, A_1188]: (~r2_hidden('#skF_8'(A_1185, B_1186, k2_zfmisc_1(A_1185, B_1186), D_1187), A_1188) | k4_xboole_0(A_1188, B_1186)!=A_1188 | ~r2_hidden(D_1187, k2_zfmisc_1(A_1185, B_1186)))), inference(resolution, [status(thm)], [c_23001, c_22965])).
% 11.41/5.15  tff(c_30044, plain, (![B_15, D_41, A_14]: (k4_xboole_0(B_15, B_15)!=B_15 | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(resolution, [status(thm)], [c_24, c_30041])).
% 11.41/5.15  tff(c_30048, plain, (![B_1189, D_1190, A_1191]: (B_1189!='#skF_12' | ~r2_hidden(D_1190, k2_zfmisc_1(A_1191, B_1189)))), inference(demodulation, [status(thm), theory('equality')], [c_22921, c_30044])).
% 11.41/5.15  tff(c_30113, plain, (![B_1192, A_1193]: (B_1192!='#skF_12' | k2_zfmisc_1(A_1193, B_1192)='#skF_12')), inference(resolution, [status(thm)], [c_22889, c_30048])).
% 11.41/5.15  tff(c_30046, plain, (![B_15, D_41, A_14]: (B_15!='#skF_12' | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(demodulation, [status(thm), theory('equality')], [c_22921, c_30044])).
% 11.41/5.15  tff(c_30119, plain, (![B_1192, D_41]: (B_1192!='#skF_12' | ~r2_hidden(D_41, '#skF_12') | B_1192!='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_30113, c_30046])).
% 11.41/5.15  tff(c_30178, plain, (![B_1192]: (B_1192!='#skF_12' | B_1192!='#skF_12')), inference(splitLeft, [status(thm)], [c_30119])).
% 11.41/5.15  tff(c_30184, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_30178])).
% 11.41/5.15  tff(c_30186, plain, (![D_1200]: (~r2_hidden(D_1200, '#skF_12'))), inference(splitRight, [status(thm)], [c_30119])).
% 11.41/5.15  tff(c_30237, plain, (![D_1201, B_1202]: (~r2_hidden(D_1201, k2_zfmisc_1('#skF_12', B_1202)))), inference(resolution, [status(thm)], [c_26, c_30186])).
% 11.41/5.15  tff(c_30305, plain, (![B_1202]: (k2_zfmisc_1('#skF_12', B_1202)='#skF_12')), inference(resolution, [status(thm)], [c_22889, c_30237])).
% 11.41/5.15  tff(c_14779, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_14747, c_8])).
% 11.41/5.15  tff(c_14791, plain, (![A_647, B_648]: (k4_xboole_0(A_647, k4_xboole_0(A_647, B_648))=k3_xboole_0(A_647, B_648))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.41/5.15  tff(c_14806, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_14750, c_14791])).
% 11.41/5.15  tff(c_14809, plain, (![A_9]: (k4_xboole_0(A_9, A_9)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_14749, c_14806])).
% 11.41/5.15  tff(c_14915, plain, (![A_672, B_673, D_674]: (r2_hidden('#skF_8'(A_672, B_673, k2_zfmisc_1(A_672, B_673), D_674), B_673) | ~r2_hidden(D_674, k2_zfmisc_1(A_672, B_673)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.41/5.15  tff(c_14851, plain, (![A_653, B_654, C_655]: (~r1_xboole_0(A_653, B_654) | ~r2_hidden(C_655, B_654) | ~r2_hidden(C_655, A_653))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.41/5.15  tff(c_14854, plain, (![C_655, B_13, A_12]: (~r2_hidden(C_655, B_13) | ~r2_hidden(C_655, A_12) | k4_xboole_0(A_12, B_13)!=A_12)), inference(resolution, [status(thm)], [c_18, c_14851])).
% 11.41/5.15  tff(c_22790, plain, (![A_911, B_912, D_913, A_914]: (~r2_hidden('#skF_8'(A_911, B_912, k2_zfmisc_1(A_911, B_912), D_913), A_914) | k4_xboole_0(A_914, B_912)!=A_914 | ~r2_hidden(D_913, k2_zfmisc_1(A_911, B_912)))), inference(resolution, [status(thm)], [c_14915, c_14854])).
% 11.41/5.15  tff(c_22793, plain, (![B_15, D_41, A_14]: (k4_xboole_0(B_15, B_15)!=B_15 | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(resolution, [status(thm)], [c_24, c_22790])).
% 11.41/5.15  tff(c_22797, plain, (![B_915, D_916, A_917]: (B_915!='#skF_12' | ~r2_hidden(D_916, k2_zfmisc_1(A_917, B_915)))), inference(demodulation, [status(thm), theory('equality')], [c_14809, c_22793])).
% 11.41/5.15  tff(c_22861, plain, (![A_917]: (k2_zfmisc_1(A_917, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_14779, c_22797])).
% 11.41/5.15  tff(c_14746, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_46])).
% 11.41/5.15  tff(c_14755, plain, ('#skF_9'='#skF_12' | '#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_14747, c_14747, c_14746])).
% 11.41/5.15  tff(c_14756, plain, ('#skF_10'='#skF_12'), inference(splitLeft, [status(thm)], [c_14755])).
% 11.41/5.15  tff(c_44, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.41/5.15  tff(c_14778, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_14747, c_14756, c_14747, c_44])).
% 11.41/5.15  tff(c_22864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22861, c_14778])).
% 11.41/5.15  tff(c_22865, plain, ('#skF_9'='#skF_12'), inference(splitRight, [status(thm)], [c_14755])).
% 11.41/5.15  tff(c_22872, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_14747, c_22865, c_14747, c_44])).
% 11.41/5.15  tff(c_30309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30305, c_22872])).
% 11.41/5.15  tff(c_30311, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_50])).
% 11.41/5.15  tff(c_30310, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_50])).
% 11.41/5.15  tff(c_30318, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_30311, c_30311, c_30310])).
% 11.41/5.15  tff(c_30319, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_30318])).
% 11.41/5.15  tff(c_30320, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_30319, c_30311])).
% 11.41/5.15  tff(c_30350, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_30320, c_8])).
% 11.41/5.15  tff(c_30312, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_30311, c_30311, c_10])).
% 11.41/5.15  tff(c_30331, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_30319, c_30319, c_30312])).
% 11.41/5.15  tff(c_30313, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_11')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_30311, c_12])).
% 11.41/5.15  tff(c_30339, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_10')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_30319, c_30313])).
% 11.41/5.15  tff(c_30363, plain, (![A_1214, B_1215]: (k4_xboole_0(A_1214, k4_xboole_0(A_1214, B_1215))=k3_xboole_0(A_1214, B_1215))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.41/5.15  tff(c_30378, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_30339, c_30363])).
% 11.41/5.15  tff(c_30381, plain, (![A_9]: (k4_xboole_0(A_9, A_9)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_30331, c_30378])).
% 11.41/5.15  tff(c_30548, plain, (![A_1244, B_1245, D_1246]: (r2_hidden('#skF_7'(A_1244, B_1245, k2_zfmisc_1(A_1244, B_1245), D_1246), A_1244) | ~r2_hidden(D_1246, k2_zfmisc_1(A_1244, B_1245)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.41/5.15  tff(c_30422, plain, (![A_1218, B_1219, C_1220]: (~r1_xboole_0(A_1218, B_1219) | ~r2_hidden(C_1220, B_1219) | ~r2_hidden(C_1220, A_1218))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.41/5.15  tff(c_30425, plain, (![C_1220, B_13, A_12]: (~r2_hidden(C_1220, B_13) | ~r2_hidden(C_1220, A_12) | k4_xboole_0(A_12, B_13)!=A_12)), inference(resolution, [status(thm)], [c_18, c_30422])).
% 11.41/5.15  tff(c_37911, plain, (![A_1472, B_1473, D_1474, A_1475]: (~r2_hidden('#skF_7'(A_1472, B_1473, k2_zfmisc_1(A_1472, B_1473), D_1474), A_1475) | k4_xboole_0(A_1475, A_1472)!=A_1475 | ~r2_hidden(D_1474, k2_zfmisc_1(A_1472, B_1473)))), inference(resolution, [status(thm)], [c_30548, c_30425])).
% 11.41/5.15  tff(c_37914, plain, (![A_14, D_41, B_15]: (k4_xboole_0(A_14, A_14)!=A_14 | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(resolution, [status(thm)], [c_26, c_37911])).
% 11.41/5.15  tff(c_37918, plain, (![A_1476, D_1477, B_1478]: (A_1476!='#skF_10' | ~r2_hidden(D_1477, k2_zfmisc_1(A_1476, B_1478)))), inference(demodulation, [status(thm), theory('equality')], [c_30381, c_37914])).
% 11.41/5.15  tff(c_37983, plain, (![A_1479, B_1480]: (A_1479!='#skF_10' | k2_zfmisc_1(A_1479, B_1480)='#skF_10')), inference(resolution, [status(thm)], [c_30350, c_37918])).
% 11.41/5.15  tff(c_37916, plain, (![A_14, D_41, B_15]: (A_14!='#skF_10' | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(demodulation, [status(thm), theory('equality')], [c_30381, c_37914])).
% 11.41/5.15  tff(c_37989, plain, (![A_1479, D_41]: (A_1479!='#skF_10' | ~r2_hidden(D_41, '#skF_10') | A_1479!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_37983, c_37916])).
% 11.41/5.15  tff(c_38048, plain, (![A_1479]: (A_1479!='#skF_10' | A_1479!='#skF_10')), inference(splitLeft, [status(thm)], [c_37989])).
% 11.41/5.15  tff(c_38054, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_38048])).
% 11.41/5.15  tff(c_38056, plain, (![D_1487]: (~r2_hidden(D_1487, '#skF_10'))), inference(splitRight, [status(thm)], [c_37989])).
% 11.41/5.15  tff(c_38107, plain, (![D_1488, A_1489]: (~r2_hidden(D_1488, k2_zfmisc_1(A_1489, '#skF_10')))), inference(resolution, [status(thm)], [c_24, c_38056])).
% 11.41/5.15  tff(c_38175, plain, (![A_1489]: (k2_zfmisc_1(A_1489, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_30350, c_38107])).
% 11.41/5.15  tff(c_48, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.41/5.15  tff(c_30330, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_30320, c_30319, c_30320, c_48])).
% 11.41/5.15  tff(c_38188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38175, c_30330])).
% 11.41/5.15  tff(c_38189, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_30318])).
% 11.41/5.15  tff(c_38191, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_38189, c_30311])).
% 11.41/5.15  tff(c_38235, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38191, c_8])).
% 11.41/5.15  tff(c_38223, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38189, c_38189, c_30312])).
% 11.41/5.15  tff(c_38212, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_9')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_38189, c_30313])).
% 11.41/5.15  tff(c_38243, plain, (![A_1501, B_1502]: (k4_xboole_0(A_1501, k4_xboole_0(A_1501, B_1502))=k3_xboole_0(A_1501, B_1502))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.41/5.15  tff(c_38258, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_38212, c_38243])).
% 11.41/5.15  tff(c_38261, plain, (![A_9]: (k4_xboole_0(A_9, A_9)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38223, c_38258])).
% 11.41/5.15  tff(c_38458, plain, (![A_1532, B_1533, D_1534]: (r2_hidden('#skF_7'(A_1532, B_1533, k2_zfmisc_1(A_1532, B_1533), D_1534), A_1532) | ~r2_hidden(D_1534, k2_zfmisc_1(A_1532, B_1533)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.41/5.15  tff(c_38306, plain, (![A_1509, B_1510, C_1511]: (~r1_xboole_0(A_1509, B_1510) | ~r2_hidden(C_1511, B_1510) | ~r2_hidden(C_1511, A_1509))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.41/5.15  tff(c_38309, plain, (![C_1511, B_13, A_12]: (~r2_hidden(C_1511, B_13) | ~r2_hidden(C_1511, A_12) | k4_xboole_0(A_12, B_13)!=A_12)), inference(resolution, [status(thm)], [c_18, c_38306])).
% 11.41/5.15  tff(c_44501, plain, (![A_1757, B_1758, D_1759, A_1760]: (~r2_hidden('#skF_7'(A_1757, B_1758, k2_zfmisc_1(A_1757, B_1758), D_1759), A_1760) | k4_xboole_0(A_1760, A_1757)!=A_1760 | ~r2_hidden(D_1759, k2_zfmisc_1(A_1757, B_1758)))), inference(resolution, [status(thm)], [c_38458, c_38309])).
% 11.41/5.15  tff(c_44504, plain, (![A_14, D_41, B_15]: (k4_xboole_0(A_14, A_14)!=A_14 | ~r2_hidden(D_41, k2_zfmisc_1(A_14, B_15)))), inference(resolution, [status(thm)], [c_26, c_44501])).
% 11.41/5.15  tff(c_44508, plain, (![A_1761, D_1762, B_1763]: (A_1761!='#skF_9' | ~r2_hidden(D_1762, k2_zfmisc_1(A_1761, B_1763)))), inference(demodulation, [status(thm), theory('equality')], [c_38261, c_44504])).
% 11.41/5.15  tff(c_44572, plain, (![B_1763]: (k2_zfmisc_1('#skF_9', B_1763)='#skF_9')), inference(resolution, [status(thm)], [c_38235, c_44508])).
% 11.41/5.15  tff(c_38197, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_38189, c_48])).
% 11.41/5.15  tff(c_38198, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_38197])).
% 11.41/5.15  tff(c_38204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38191, c_38198])).
% 11.41/5.15  tff(c_38205, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38197])).
% 11.41/5.15  tff(c_38222, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_38191, c_38205])).
% 11.41/5.15  tff(c_44575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44572, c_38222])).
% 11.41/5.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/5.15  
% 11.41/5.15  Inference rules
% 11.41/5.15  ----------------------
% 11.41/5.15  #Ref     : 20
% 11.41/5.15  #Sup     : 10838
% 11.41/5.15  #Fact    : 0
% 11.41/5.15  #Define  : 0
% 11.41/5.15  #Split   : 12
% 11.41/5.15  #Chain   : 0
% 11.41/5.15  #Close   : 0
% 11.41/5.15  
% 11.41/5.15  Ordering : KBO
% 11.41/5.15  
% 11.41/5.15  Simplification rules
% 11.41/5.15  ----------------------
% 11.41/5.15  #Subsume      : 3561
% 11.41/5.15  #Demod        : 10697
% 11.41/5.15  #Tautology    : 5282
% 11.41/5.15  #SimpNegUnit  : 8
% 11.41/5.15  #BackRed      : 32
% 11.41/5.15  
% 11.41/5.15  #Partial instantiations: 0
% 11.41/5.15  #Strategies tried      : 1
% 11.41/5.15  
% 11.41/5.15  Timing (in seconds)
% 11.41/5.15  ----------------------
% 11.41/5.15  Preprocessing        : 0.34
% 11.41/5.15  Parsing              : 0.17
% 11.41/5.15  CNF conversion       : 0.03
% 11.41/5.15  Main loop            : 3.98
% 11.41/5.15  Inferencing          : 1.10
% 11.41/5.15  Reduction            : 1.57
% 11.41/5.15  Demodulation         : 1.25
% 11.41/5.15  BG Simplification    : 0.13
% 11.41/5.15  Subsumption          : 0.98
% 11.41/5.15  Abstraction          : 0.23
% 11.41/5.15  MUC search           : 0.00
% 11.41/5.15  Cooper               : 0.00
% 11.41/5.15  Total                : 4.38
% 11.41/5.15  Index Insertion      : 0.00
% 11.41/5.15  Index Deletion       : 0.00
% 11.41/5.15  Index Matching       : 0.00
% 11.41/5.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
