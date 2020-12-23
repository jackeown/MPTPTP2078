%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:54 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 289 expanded)
%              Number of leaves         :   26 ( 103 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 490 expanded)
%              Number of equality atoms :   71 ( 422 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) != k1_xboole_0
       => ! [C] :
            ( m1_subset_1(C,k2_zfmisc_1(A,B))
           => ( C != k1_mcart_1(C)
              & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => ( C != k1_mcart_1(C)
                & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(c_24,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_54,plain,(
    k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_149,plain,(
    ! [C_44,A_45,B_46] :
      ( k1_mcart_1(C_44) != C_44
      | ~ m1_subset_1(C_44,k2_zfmisc_1(A_45,B_46))
      | k1_xboole_0 = B_46
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_155,plain,
    ( k1_mcart_1('#skF_3') != '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_149])).

tff(c_159,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_155])).

tff(c_160,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_92,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_86])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_77])).

tff(c_100,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_89])).

tff(c_163,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_100])).

tff(c_258,plain,(
    ! [A_59,C_60,B_61] : k4_xboole_0(k2_zfmisc_1(A_59,C_60),k2_zfmisc_1(B_61,C_60)) = k2_zfmisc_1(k4_xboole_0(A_59,B_61),C_60) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_265,plain,(
    ! [B_61,C_60] : k2_zfmisc_1(k4_xboole_0(B_61,B_61),C_60) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_163])).

tff(c_288,plain,(
    ! [C_60] : k2_zfmisc_1('#skF_1',C_60) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_265])).

tff(c_28,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_166,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_28])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_166])).

tff(c_299,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_117,plain,(
    ! [C_40,A_41,B_42] : k4_xboole_0(k2_zfmisc_1(C_40,A_41),k2_zfmisc_1(C_40,B_42)) = k2_zfmisc_1(C_40,k4_xboole_0(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_131,plain,(
    ! [C_40,A_41] : k2_zfmisc_1(C_40,k4_xboole_0(A_41,A_41)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_117])).

tff(c_135,plain,(
    ! [C_40] : k2_zfmisc_1(C_40,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_131])).

tff(c_345,plain,(
    ! [C_40] : k2_zfmisc_1(C_40,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_299,c_135])).

tff(c_307,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_28])).

tff(c_349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_307])).

tff(c_350,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_446,plain,(
    ! [C_82,A_83,B_84] :
      ( k2_mcart_1(C_82) != C_82
      | ~ m1_subset_1(C_82,k2_zfmisc_1(A_83,B_84))
      | k1_xboole_0 = B_84
      | k1_xboole_0 = A_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_452,plain,
    ( k2_mcart_1('#skF_3') != '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_446])).

tff(c_456,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_452])).

tff(c_457,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_456])).

tff(c_374,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_383,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k5_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_374])).

tff(c_389,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_383])).

tff(c_386,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_374])).

tff(c_406,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_386])).

tff(c_414,plain,(
    ! [A_78,C_79,B_80] : k4_xboole_0(k2_zfmisc_1(A_78,C_79),k2_zfmisc_1(B_80,C_79)) = k2_zfmisc_1(k4_xboole_0(A_78,B_80),C_79) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_428,plain,(
    ! [A_78,C_79] : k2_zfmisc_1(k4_xboole_0(A_78,A_78),C_79) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_414])).

tff(c_432,plain,(
    ! [C_79] : k2_zfmisc_1(k1_xboole_0,C_79) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_428])).

tff(c_498,plain,(
    ! [C_79] : k2_zfmisc_1('#skF_1',C_79) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_457,c_432])).

tff(c_463,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_28])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_463])).

tff(c_503,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_456])).

tff(c_507,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_406])).

tff(c_555,plain,(
    ! [C_93,A_94,B_95] : k4_xboole_0(k2_zfmisc_1(C_93,A_94),k2_zfmisc_1(C_93,B_95)) = k2_zfmisc_1(C_93,k4_xboole_0(A_94,B_95)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_562,plain,(
    ! [C_93,B_95] : k2_zfmisc_1(C_93,k4_xboole_0(B_95,B_95)) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_507])).

tff(c_585,plain,(
    ! [C_93] : k2_zfmisc_1(C_93,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_562])).

tff(c_510,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_28])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.32  
% 2.33/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.33  %$ m1_subset_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.33/1.33  
% 2.33/1.33  %Foreground sorts:
% 2.33/1.33  
% 2.33/1.33  
% 2.33/1.33  %Background operators:
% 2.33/1.33  
% 2.33/1.33  
% 2.33/1.33  %Foreground operators:
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.33/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.33/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.33/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.33/1.33  
% 2.33/1.34  tff(f_73, negated_conjecture, ~(![A, B]: (~(k2_zfmisc_1(A, B) = k1_xboole_0) => (![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_mcart_1)).
% 2.33/1.34  tff(f_60, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_mcart_1)).
% 2.33/1.34  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.33/1.34  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.33/1.34  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.33/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.33/1.34  tff(f_41, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 2.33/1.34  tff(c_24, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.33/1.34  tff(c_54, plain, (k1_mcart_1('#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_24])).
% 2.33/1.34  tff(c_26, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.33/1.34  tff(c_149, plain, (![C_44, A_45, B_46]: (k1_mcart_1(C_44)!=C_44 | ~m1_subset_1(C_44, k2_zfmisc_1(A_45, B_46)) | k1_xboole_0=B_46 | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.33/1.34  tff(c_155, plain, (k1_mcart_1('#skF_3')!='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_149])).
% 2.33/1.34  tff(c_159, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_155])).
% 2.33/1.34  tff(c_160, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_159])).
% 2.33/1.34  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.33/1.34  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.34  tff(c_77, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.34  tff(c_86, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_77])).
% 2.33/1.34  tff(c_92, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_86])).
% 2.33/1.34  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.33/1.34  tff(c_89, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_77])).
% 2.33/1.34  tff(c_100, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_89])).
% 2.33/1.34  tff(c_163, plain, (![A_1]: (k4_xboole_0(A_1, A_1)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_100])).
% 2.33/1.34  tff(c_258, plain, (![A_59, C_60, B_61]: (k4_xboole_0(k2_zfmisc_1(A_59, C_60), k2_zfmisc_1(B_61, C_60))=k2_zfmisc_1(k4_xboole_0(A_59, B_61), C_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.34  tff(c_265, plain, (![B_61, C_60]: (k2_zfmisc_1(k4_xboole_0(B_61, B_61), C_60)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_258, c_163])).
% 2.33/1.34  tff(c_288, plain, (![C_60]: (k2_zfmisc_1('#skF_1', C_60)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_265])).
% 2.33/1.34  tff(c_28, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.33/1.34  tff(c_166, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_28])).
% 2.33/1.34  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_288, c_166])).
% 2.33/1.34  tff(c_299, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_159])).
% 2.33/1.34  tff(c_117, plain, (![C_40, A_41, B_42]: (k4_xboole_0(k2_zfmisc_1(C_40, A_41), k2_zfmisc_1(C_40, B_42))=k2_zfmisc_1(C_40, k4_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.34  tff(c_131, plain, (![C_40, A_41]: (k2_zfmisc_1(C_40, k4_xboole_0(A_41, A_41))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_117])).
% 2.33/1.34  tff(c_135, plain, (![C_40]: (k2_zfmisc_1(C_40, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_100, c_131])).
% 2.33/1.34  tff(c_345, plain, (![C_40]: (k2_zfmisc_1(C_40, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_299, c_135])).
% 2.33/1.34  tff(c_307, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_299, c_28])).
% 2.33/1.34  tff(c_349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_345, c_307])).
% 2.33/1.34  tff(c_350, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.33/1.34  tff(c_446, plain, (![C_82, A_83, B_84]: (k2_mcart_1(C_82)!=C_82 | ~m1_subset_1(C_82, k2_zfmisc_1(A_83, B_84)) | k1_xboole_0=B_84 | k1_xboole_0=A_83)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.33/1.34  tff(c_452, plain, (k2_mcart_1('#skF_3')!='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_446])).
% 2.33/1.34  tff(c_456, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_452])).
% 2.33/1.34  tff(c_457, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_456])).
% 2.33/1.34  tff(c_374, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.34  tff(c_383, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k5_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_374])).
% 2.33/1.34  tff(c_389, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_383])).
% 2.33/1.34  tff(c_386, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_374])).
% 2.33/1.34  tff(c_406, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_389, c_386])).
% 2.33/1.34  tff(c_414, plain, (![A_78, C_79, B_80]: (k4_xboole_0(k2_zfmisc_1(A_78, C_79), k2_zfmisc_1(B_80, C_79))=k2_zfmisc_1(k4_xboole_0(A_78, B_80), C_79))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.34  tff(c_428, plain, (![A_78, C_79]: (k2_zfmisc_1(k4_xboole_0(A_78, A_78), C_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_406, c_414])).
% 2.33/1.34  tff(c_432, plain, (![C_79]: (k2_zfmisc_1(k1_xboole_0, C_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_406, c_428])).
% 2.33/1.34  tff(c_498, plain, (![C_79]: (k2_zfmisc_1('#skF_1', C_79)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_457, c_432])).
% 2.33/1.34  tff(c_463, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_28])).
% 2.33/1.34  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_498, c_463])).
% 2.33/1.34  tff(c_503, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_456])).
% 2.33/1.34  tff(c_507, plain, (![A_1]: (k4_xboole_0(A_1, A_1)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_406])).
% 2.33/1.34  tff(c_555, plain, (![C_93, A_94, B_95]: (k4_xboole_0(k2_zfmisc_1(C_93, A_94), k2_zfmisc_1(C_93, B_95))=k2_zfmisc_1(C_93, k4_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.34  tff(c_562, plain, (![C_93, B_95]: (k2_zfmisc_1(C_93, k4_xboole_0(B_95, B_95))='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_555, c_507])).
% 2.33/1.34  tff(c_585, plain, (![C_93]: (k2_zfmisc_1(C_93, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_507, c_562])).
% 2.33/1.34  tff(c_510, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_503, c_28])).
% 2.33/1.34  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_585, c_510])).
% 2.33/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  Inference rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Ref     : 0
% 2.33/1.34  #Sup     : 126
% 2.33/1.34  #Fact    : 0
% 2.33/1.34  #Define  : 0
% 2.33/1.34  #Split   : 3
% 2.33/1.34  #Chain   : 0
% 2.33/1.34  #Close   : 0
% 2.33/1.34  
% 2.33/1.34  Ordering : KBO
% 2.33/1.34  
% 2.33/1.34  Simplification rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Subsume      : 1
% 2.33/1.34  #Demod        : 118
% 2.33/1.34  #Tautology    : 97
% 2.33/1.34  #SimpNegUnit  : 1
% 2.33/1.34  #BackRed      : 33
% 2.33/1.34  
% 2.33/1.34  #Partial instantiations: 0
% 2.33/1.34  #Strategies tried      : 1
% 2.33/1.34  
% 2.33/1.34  Timing (in seconds)
% 2.33/1.34  ----------------------
% 2.33/1.34  Preprocessing        : 0.30
% 2.33/1.34  Parsing              : 0.16
% 2.33/1.34  CNF conversion       : 0.02
% 2.33/1.34  Main loop            : 0.26
% 2.33/1.34  Inferencing          : 0.10
% 2.33/1.35  Reduction            : 0.09
% 2.33/1.35  Demodulation         : 0.07
% 2.33/1.35  BG Simplification    : 0.02
% 2.33/1.35  Subsumption          : 0.03
% 2.33/1.35  Abstraction          : 0.02
% 2.33/1.35  MUC search           : 0.00
% 2.33/1.35  Cooper               : 0.00
% 2.33/1.35  Total                : 0.60
% 2.33/1.35  Index Insertion      : 0.00
% 2.33/1.35  Index Deletion       : 0.00
% 2.33/1.35  Index Matching       : 0.00
% 2.33/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
