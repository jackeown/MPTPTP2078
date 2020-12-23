%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:42 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 130 expanded)
%              Number of leaves         :   35 (  63 expanded)
%              Depth                    :    6
%              Number of atoms          :  117 ( 288 expanded)
%              Number of equality atoms :   96 ( 234 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_10 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_101,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_75,plain,(
    ! [A_84,B_85] : k2_xboole_0(k1_tarski(A_84),B_85) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    ! [A_84] : k1_tarski(A_84) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_40,plain,(
    ! [A_56] :
      ( r2_hidden('#skF_6'(A_56),A_56)
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_100,plain,(
    ! [C_92,A_93] :
      ( C_92 = A_93
      | ~ r2_hidden(C_92,k1_tarski(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_104,plain,(
    ! [A_93] :
      ( '#skF_6'(k1_tarski(A_93)) = A_93
      | k1_tarski(A_93) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_100])).

tff(c_110,plain,(
    ! [A_93] : '#skF_6'(k1_tarski(A_93)) = A_93 ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_104])).

tff(c_6,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2227,plain,(
    ! [D_4942,A_4943,C_4944,E_4945] :
      ( ~ r2_hidden(D_4942,A_4943)
      | k3_mcart_1(C_4944,D_4942,E_4945) != '#skF_6'(A_4943)
      | k1_xboole_0 = A_4943 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2231,plain,(
    ! [C_4944,C_7,E_4945] :
      ( k3_mcart_1(C_4944,C_7,E_4945) != '#skF_6'(k1_tarski(C_7))
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_2227])).

tff(c_2234,plain,(
    ! [C_4944,C_7,E_4945] :
      ( k3_mcart_1(C_4944,C_7,E_4945) != C_7
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2231])).

tff(c_2235,plain,(
    ! [C_4944,C_7,E_4945] : k3_mcart_1(C_4944,C_7,E_4945) != C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_2234])).

tff(c_54,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_162,plain,(
    ! [A_99,B_100,C_101] : k4_tarski(k4_tarski(A_99,B_100),C_101) = k3_mcart_1(A_99,B_100,C_101) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_75,B_76] : k2_mcart_1(k4_tarski(A_75,B_76)) = B_76 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    ! [B_48,C_49] : k2_mcart_1(k4_tarski(B_48,C_49)) != k4_tarski(B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_62,plain,(
    ! [B_48,C_49] : k4_tarski(B_48,C_49) != C_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30])).

tff(c_180,plain,(
    ! [A_99,B_100,C_101] : k3_mcart_1(A_99,B_100,C_101) != C_101 ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_62])).

tff(c_239,plain,(
    ! [C_139,A_140,D_141,E_142] :
      ( ~ r2_hidden(C_139,A_140)
      | k3_mcart_1(C_139,D_141,E_142) != '#skF_6'(A_140)
      | k1_xboole_0 = A_140 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_243,plain,(
    ! [C_7,D_141,E_142] :
      ( k3_mcart_1(C_7,D_141,E_142) != '#skF_6'(k1_tarski(C_7))
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_239])).

tff(c_246,plain,(
    ! [C_7,D_141,E_142] :
      ( k3_mcart_1(C_7,D_141,E_142) != C_7
      | k1_tarski(C_7) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_243])).

tff(c_247,plain,(
    ! [C_7,D_141,E_142] : k3_mcart_1(C_7,D_141,E_142) != C_7 ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_246])).

tff(c_52,plain,
    ( k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10'
    | k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10'
    | k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_190,plain,(
    k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1169,plain,(
    ! [A_2546,B_2547,C_2548,D_2549] :
      ( k3_mcart_1(k5_mcart_1(A_2546,B_2547,C_2548,D_2549),k6_mcart_1(A_2546,B_2547,C_2548,D_2549),k7_mcart_1(A_2546,B_2547,C_2548,D_2549)) = D_2549
      | ~ m1_subset_1(D_2549,k3_zfmisc_1(A_2546,B_2547,C_2548))
      | k1_xboole_0 = C_2548
      | k1_xboole_0 = B_2547
      | k1_xboole_0 = A_2546 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1247,plain,
    ( k3_mcart_1('#skF_10',k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_1169])).

tff(c_1251,plain,
    ( k3_mcart_1('#skF_10',k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10')) = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1247])).

tff(c_1253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_247,c_1251])).

tff(c_1254,plain,
    ( k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10'
    | k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1266,plain,(
    k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_1254])).

tff(c_2124,plain,(
    ! [A_4875,B_4876,C_4877,D_4878] :
      ( k3_mcart_1(k5_mcart_1(A_4875,B_4876,C_4877,D_4878),k6_mcart_1(A_4875,B_4876,C_4877,D_4878),k7_mcart_1(A_4875,B_4876,C_4877,D_4878)) = D_4878
      | ~ m1_subset_1(D_4878,k3_zfmisc_1(A_4875,B_4876,C_4877))
      | k1_xboole_0 = C_4877
      | k1_xboole_0 = B_4876
      | k1_xboole_0 = A_4875 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2190,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_10') = '#skF_10'
    | ~ m1_subset_1('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_2124])).

tff(c_2194,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_10') = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2190])).

tff(c_2196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_180,c_2194])).

tff(c_2197,plain,(
    k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_1254])).

tff(c_3165,plain,(
    ! [A_7385,B_7386,C_7387,D_7388] :
      ( k3_mcart_1(k5_mcart_1(A_7385,B_7386,C_7387,D_7388),k6_mcart_1(A_7385,B_7386,C_7387,D_7388),k7_mcart_1(A_7385,B_7386,C_7387,D_7388)) = D_7388
      | ~ m1_subset_1(D_7388,k3_zfmisc_1(A_7385,B_7386,C_7387))
      | k1_xboole_0 = C_7387
      | k1_xboole_0 = B_7386
      | k1_xboole_0 = A_7385 ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3241,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_10',k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_2197,c_3165])).

tff(c_3245,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10'),'#skF_10',k7_mcart_1('#skF_7','#skF_8','#skF_9','#skF_10')) = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3241])).

tff(c_3247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_2235,c_3245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.77  
% 4.51/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.77  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_xboole_0 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_10 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_6
% 4.51/1.77  
% 4.51/1.77  %Foreground sorts:
% 4.51/1.77  
% 4.51/1.77  
% 4.51/1.77  %Background operators:
% 4.51/1.77  
% 4.51/1.77  
% 4.51/1.77  %Foreground operators:
% 4.51/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.51/1.77  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.51/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.77  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.51/1.77  tff('#skF_7', type, '#skF_7': $i).
% 4.51/1.77  tff('#skF_10', type, '#skF_10': $i).
% 4.51/1.77  tff('#skF_9', type, '#skF_9': $i).
% 4.51/1.77  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.51/1.77  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.51/1.77  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.51/1.77  tff('#skF_8', type, '#skF_8': $i).
% 4.51/1.77  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.51/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.77  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.51/1.77  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.51/1.77  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.51/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.51/1.77  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.51/1.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.51/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.51/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.51/1.77  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.51/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.77  
% 4.51/1.78  tff(f_145, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 4.51/1.78  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.51/1.78  tff(f_41, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 4.51/1.78  tff(f_101, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 4.51/1.78  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.51/1.78  tff(f_43, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 4.51/1.78  tff(f_121, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 4.51/1.78  tff(f_77, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 4.51/1.78  tff(f_117, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 4.51/1.78  tff(c_60, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.51/1.78  tff(c_58, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.51/1.78  tff(c_56, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.51/1.78  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.51/1.78  tff(c_75, plain, (![A_84, B_85]: (k2_xboole_0(k1_tarski(A_84), B_85)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.51/1.78  tff(c_79, plain, (![A_84]: (k1_tarski(A_84)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 4.51/1.78  tff(c_40, plain, (![A_56]: (r2_hidden('#skF_6'(A_56), A_56) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.51/1.78  tff(c_100, plain, (![C_92, A_93]: (C_92=A_93 | ~r2_hidden(C_92, k1_tarski(A_93)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.51/1.78  tff(c_104, plain, (![A_93]: ('#skF_6'(k1_tarski(A_93))=A_93 | k1_tarski(A_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_100])).
% 4.51/1.78  tff(c_110, plain, (![A_93]: ('#skF_6'(k1_tarski(A_93))=A_93)), inference(negUnitSimplification, [status(thm)], [c_79, c_104])).
% 4.51/1.78  tff(c_6, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.51/1.78  tff(c_2227, plain, (![D_4942, A_4943, C_4944, E_4945]: (~r2_hidden(D_4942, A_4943) | k3_mcart_1(C_4944, D_4942, E_4945)!='#skF_6'(A_4943) | k1_xboole_0=A_4943)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.51/1.78  tff(c_2231, plain, (![C_4944, C_7, E_4945]: (k3_mcart_1(C_4944, C_7, E_4945)!='#skF_6'(k1_tarski(C_7)) | k1_tarski(C_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2227])).
% 4.51/1.78  tff(c_2234, plain, (![C_4944, C_7, E_4945]: (k3_mcart_1(C_4944, C_7, E_4945)!=C_7 | k1_tarski(C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2231])).
% 4.51/1.78  tff(c_2235, plain, (![C_4944, C_7, E_4945]: (k3_mcart_1(C_4944, C_7, E_4945)!=C_7)), inference(negUnitSimplification, [status(thm)], [c_79, c_2234])).
% 4.51/1.78  tff(c_54, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.51/1.78  tff(c_162, plain, (![A_99, B_100, C_101]: (k4_tarski(k4_tarski(A_99, B_100), C_101)=k3_mcart_1(A_99, B_100, C_101))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.51/1.78  tff(c_50, plain, (![A_75, B_76]: (k2_mcart_1(k4_tarski(A_75, B_76))=B_76)), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.51/1.78  tff(c_30, plain, (![B_48, C_49]: (k2_mcart_1(k4_tarski(B_48, C_49))!=k4_tarski(B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.51/1.78  tff(c_62, plain, (![B_48, C_49]: (k4_tarski(B_48, C_49)!=C_49)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_30])).
% 4.51/1.78  tff(c_180, plain, (![A_99, B_100, C_101]: (k3_mcart_1(A_99, B_100, C_101)!=C_101)), inference(superposition, [status(thm), theory('equality')], [c_162, c_62])).
% 4.51/1.78  tff(c_239, plain, (![C_139, A_140, D_141, E_142]: (~r2_hidden(C_139, A_140) | k3_mcart_1(C_139, D_141, E_142)!='#skF_6'(A_140) | k1_xboole_0=A_140)), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.51/1.78  tff(c_243, plain, (![C_7, D_141, E_142]: (k3_mcart_1(C_7, D_141, E_142)!='#skF_6'(k1_tarski(C_7)) | k1_tarski(C_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_239])).
% 4.51/1.78  tff(c_246, plain, (![C_7, D_141, E_142]: (k3_mcart_1(C_7, D_141, E_142)!=C_7 | k1_tarski(C_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_243])).
% 4.51/1.78  tff(c_247, plain, (![C_7, D_141, E_142]: (k3_mcart_1(C_7, D_141, E_142)!=C_7)), inference(negUnitSimplification, [status(thm)], [c_79, c_246])).
% 4.51/1.78  tff(c_52, plain, (k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10' | k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10' | k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.51/1.78  tff(c_190, plain, (k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(splitLeft, [status(thm)], [c_52])).
% 4.51/1.78  tff(c_1169, plain, (![A_2546, B_2547, C_2548, D_2549]: (k3_mcart_1(k5_mcart_1(A_2546, B_2547, C_2548, D_2549), k6_mcart_1(A_2546, B_2547, C_2548, D_2549), k7_mcart_1(A_2546, B_2547, C_2548, D_2549))=D_2549 | ~m1_subset_1(D_2549, k3_zfmisc_1(A_2546, B_2547, C_2548)) | k1_xboole_0=C_2548 | k1_xboole_0=B_2547 | k1_xboole_0=A_2546)), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.51/1.78  tff(c_1247, plain, (k3_mcart_1('#skF_10', k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_190, c_1169])).
% 4.51/1.78  tff(c_1251, plain, (k3_mcart_1('#skF_10', k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1247])).
% 4.51/1.78  tff(c_1253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_247, c_1251])).
% 4.51/1.78  tff(c_1254, plain, (k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10' | k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_52])).
% 4.51/1.78  tff(c_1266, plain, (k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(splitLeft, [status(thm)], [c_1254])).
% 4.51/1.78  tff(c_2124, plain, (![A_4875, B_4876, C_4877, D_4878]: (k3_mcart_1(k5_mcart_1(A_4875, B_4876, C_4877, D_4878), k6_mcart_1(A_4875, B_4876, C_4877, D_4878), k7_mcart_1(A_4875, B_4876, C_4877, D_4878))=D_4878 | ~m1_subset_1(D_4878, k3_zfmisc_1(A_4875, B_4876, C_4877)) | k1_xboole_0=C_4877 | k1_xboole_0=B_4876 | k1_xboole_0=A_4875)), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.51/1.78  tff(c_2190, plain, (k3_mcart_1(k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), '#skF_10')='#skF_10' | ~m1_subset_1('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1266, c_2124])).
% 4.51/1.78  tff(c_2194, plain, (k3_mcart_1(k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), '#skF_10')='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2190])).
% 4.51/1.78  tff(c_2196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_180, c_2194])).
% 4.51/1.78  tff(c_2197, plain, (k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10')='#skF_10'), inference(splitRight, [status(thm)], [c_1254])).
% 4.51/1.78  tff(c_3165, plain, (![A_7385, B_7386, C_7387, D_7388]: (k3_mcart_1(k5_mcart_1(A_7385, B_7386, C_7387, D_7388), k6_mcart_1(A_7385, B_7386, C_7387, D_7388), k7_mcart_1(A_7385, B_7386, C_7387, D_7388))=D_7388 | ~m1_subset_1(D_7388, k3_zfmisc_1(A_7385, B_7386, C_7387)) | k1_xboole_0=C_7387 | k1_xboole_0=B_7386 | k1_xboole_0=A_7385)), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.51/1.78  tff(c_3241, plain, (k3_mcart_1(k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), '#skF_10', k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_2197, c_3165])).
% 4.51/1.78  tff(c_3245, plain, (k3_mcart_1(k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'), '#skF_10', k7_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3241])).
% 4.51/1.78  tff(c_3247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_2235, c_3245])).
% 4.51/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.78  
% 4.51/1.78  Inference rules
% 4.51/1.78  ----------------------
% 4.51/1.78  #Ref     : 11
% 4.51/1.78  #Sup     : 437
% 4.51/1.78  #Fact    : 0
% 4.51/1.78  #Define  : 0
% 4.51/1.78  #Split   : 5
% 4.51/1.78  #Chain   : 0
% 4.51/1.78  #Close   : 0
% 4.51/1.78  
% 4.51/1.78  Ordering : KBO
% 4.51/1.78  
% 4.51/1.78  Simplification rules
% 4.51/1.78  ----------------------
% 4.51/1.78  #Subsume      : 121
% 4.51/1.78  #Demod        : 79
% 4.51/1.78  #Tautology    : 138
% 4.51/1.78  #SimpNegUnit  : 23
% 4.51/1.78  #BackRed      : 0
% 4.51/1.78  
% 4.51/1.78  #Partial instantiations: 3465
% 4.51/1.78  #Strategies tried      : 1
% 4.51/1.78  
% 4.51/1.78  Timing (in seconds)
% 4.51/1.78  ----------------------
% 4.59/1.79  Preprocessing        : 0.34
% 4.59/1.79  Parsing              : 0.19
% 4.59/1.79  CNF conversion       : 0.03
% 4.59/1.79  Main loop            : 0.68
% 4.59/1.79  Inferencing          : 0.34
% 4.59/1.79  Reduction            : 0.14
% 4.59/1.79  Demodulation         : 0.08
% 4.59/1.79  BG Simplification    : 0.03
% 4.59/1.79  Subsumption          : 0.13
% 4.59/1.79  Abstraction          : 0.03
% 4.59/1.79  MUC search           : 0.00
% 4.59/1.79  Cooper               : 0.00
% 4.59/1.79  Total                : 1.05
% 4.59/1.79  Index Insertion      : 0.00
% 4.59/1.79  Index Deletion       : 0.00
% 4.59/1.79  Index Matching       : 0.00
% 4.59/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
