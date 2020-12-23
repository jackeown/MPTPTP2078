%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:56 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 101 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :    6
%              Number of atoms          :   84 ( 267 expanded)
%              Number of equality atoms :   75 ( 237 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
       => ~ ( A != k1_xboole_0
            & B != k1_xboole_0
            & C != k1_xboole_0
            & ? [E,F,G] :
                ( D = k3_mcart_1(E,F,G)
                & ~ ( k5_mcart_1(A,B,C,D) = E
                    & k6_mcart_1(A,B,C,D) = F
                    & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7'
    | k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6'
    | k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_82,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_18,plain,(
    k3_mcart_1('#skF_5','#skF_6','#skF_7') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_49,plain,(
    ! [A_21,B_22,C_23] : k4_tarski(k4_tarski(A_21,B_22),C_23) = k3_mcart_1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_mcart_1(k4_tarski(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    ! [A_27,B_28,C_29] : k1_mcart_1(k3_mcart_1(A_27,B_28,C_29)) = k4_tarski(A_27,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_12])).

tff(c_96,plain,(
    k4_tarski('#skF_5','#skF_6') = k1_mcart_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_87])).

tff(c_108,plain,(
    k1_mcart_1(k1_mcart_1('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_12])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_262,plain,(
    ! [A_53,B_54,C_55,D_56] :
      ( k5_mcart_1(A_53,B_54,C_55,D_56) = k1_mcart_1(k1_mcart_1(D_56))
      | ~ m1_subset_1(D_56,k3_zfmisc_1(A_53,B_54,C_55))
      | k1_xboole_0 = C_55
      | k1_xboole_0 = B_54
      | k1_xboole_0 = A_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_268,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_4')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_262])).

tff(c_270,plain,
    ( k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_268])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_82,c_270])).

tff(c_273,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6'
    | k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_386,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_mcart_1(k4_tarski(A_12,B_13)) = B_13 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    ! [A_24,B_25,C_26] : k2_mcart_1(k3_mcart_1(A_24,B_25,C_26)) = C_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_14])).

tff(c_79,plain,(
    k2_mcart_1('#skF_4') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_70])).

tff(c_431,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k7_mcart_1(A_75,B_76,C_77,D_78) = k2_mcart_1(D_78)
      | ~ m1_subset_1(D_78,k3_zfmisc_1(A_75,B_76,C_77))
      | k1_xboole_0 = C_77
      | k1_xboole_0 = B_76
      | k1_xboole_0 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_437,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_431])).

tff(c_439,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_7'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_437])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_386,c_439])).

tff(c_442,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_283,plain,(
    ! [A_57,B_58,C_59] : k1_mcart_1(k3_mcart_1(A_57,B_58,C_59)) = k4_tarski(A_57,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_12])).

tff(c_292,plain,(
    k4_tarski('#skF_5','#skF_6') = k1_mcart_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_283])).

tff(c_301,plain,(
    k2_mcart_1(k1_mcart_1('#skF_4')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_14])).

tff(c_502,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k6_mcart_1(A_91,B_92,C_93,D_94) = k2_mcart_1(k1_mcart_1(D_94))
      | ~ m1_subset_1(D_94,k3_zfmisc_1(A_91,B_92,C_93))
      | k1_xboole_0 = C_93
      | k1_xboole_0 = B_92
      | k1_xboole_0 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_508,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_4')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_502])).

tff(c_510,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_508])).

tff(c_512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_442,c_510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:52:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.28  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.15/1.28  
% 2.15/1.28  %Foreground sorts:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Background operators:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Foreground operators:
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.15/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.28  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.15/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.28  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.15/1.28  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.28  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.15/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.28  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.28  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.15/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.28  
% 2.15/1.29  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_mcart_1)).
% 2.15/1.29  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.15/1.29  tff(f_53, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.15/1.29  tff(f_49, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 2.15/1.29  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.15/1.29  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.15/1.29  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.15/1.29  tff(c_16, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7' | k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6' | k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.15/1.29  tff(c_82, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_16])).
% 2.15/1.29  tff(c_18, plain, (k3_mcart_1('#skF_5', '#skF_6', '#skF_7')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.15/1.29  tff(c_49, plain, (![A_21, B_22, C_23]: (k4_tarski(k4_tarski(A_21, B_22), C_23)=k3_mcart_1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.29  tff(c_12, plain, (![A_12, B_13]: (k1_mcart_1(k4_tarski(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.29  tff(c_87, plain, (![A_27, B_28, C_29]: (k1_mcart_1(k3_mcart_1(A_27, B_28, C_29))=k4_tarski(A_27, B_28))), inference(superposition, [status(thm), theory('equality')], [c_49, c_12])).
% 2.15/1.29  tff(c_96, plain, (k4_tarski('#skF_5', '#skF_6')=k1_mcart_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_87])).
% 2.15/1.29  tff(c_108, plain, (k1_mcart_1(k1_mcart_1('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_96, c_12])).
% 2.15/1.29  tff(c_26, plain, (m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.15/1.29  tff(c_262, plain, (![A_53, B_54, C_55, D_56]: (k5_mcart_1(A_53, B_54, C_55, D_56)=k1_mcart_1(k1_mcart_1(D_56)) | ~m1_subset_1(D_56, k3_zfmisc_1(A_53, B_54, C_55)) | k1_xboole_0=C_55 | k1_xboole_0=B_54 | k1_xboole_0=A_53)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.29  tff(c_268, plain, (k1_mcart_1(k1_mcart_1('#skF_4'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_262])).
% 2.15/1.29  tff(c_270, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_5' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_268])).
% 2.15/1.29  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_82, c_270])).
% 2.15/1.29  tff(c_273, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6' | k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(splitRight, [status(thm)], [c_16])).
% 2.15/1.29  tff(c_386, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_7'), inference(splitLeft, [status(thm)], [c_273])).
% 2.15/1.29  tff(c_14, plain, (![A_12, B_13]: (k2_mcart_1(k4_tarski(A_12, B_13))=B_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.29  tff(c_70, plain, (![A_24, B_25, C_26]: (k2_mcart_1(k3_mcart_1(A_24, B_25, C_26))=C_26)), inference(superposition, [status(thm), theory('equality')], [c_49, c_14])).
% 2.15/1.29  tff(c_79, plain, (k2_mcart_1('#skF_4')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_18, c_70])).
% 2.15/1.29  tff(c_431, plain, (![A_75, B_76, C_77, D_78]: (k7_mcart_1(A_75, B_76, C_77, D_78)=k2_mcart_1(D_78) | ~m1_subset_1(D_78, k3_zfmisc_1(A_75, B_76, C_77)) | k1_xboole_0=C_77 | k1_xboole_0=B_76 | k1_xboole_0=A_75)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.29  tff(c_437, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_431])).
% 2.15/1.29  tff(c_439, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_7' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_437])).
% 2.15/1.29  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_386, c_439])).
% 2.15/1.29  tff(c_442, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_273])).
% 2.15/1.29  tff(c_283, plain, (![A_57, B_58, C_59]: (k1_mcart_1(k3_mcart_1(A_57, B_58, C_59))=k4_tarski(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_49, c_12])).
% 2.15/1.29  tff(c_292, plain, (k4_tarski('#skF_5', '#skF_6')=k1_mcart_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_283])).
% 2.15/1.29  tff(c_301, plain, (k2_mcart_1(k1_mcart_1('#skF_4'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_292, c_14])).
% 2.15/1.29  tff(c_502, plain, (![A_91, B_92, C_93, D_94]: (k6_mcart_1(A_91, B_92, C_93, D_94)=k2_mcart_1(k1_mcart_1(D_94)) | ~m1_subset_1(D_94, k3_zfmisc_1(A_91, B_92, C_93)) | k1_xboole_0=C_93 | k1_xboole_0=B_92 | k1_xboole_0=A_91)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.29  tff(c_508, plain, (k2_mcart_1(k1_mcart_1('#skF_4'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_502])).
% 2.15/1.29  tff(c_510, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')='#skF_6' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_508])).
% 2.15/1.29  tff(c_512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_442, c_510])).
% 2.15/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  Inference rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Ref     : 0
% 2.15/1.29  #Sup     : 129
% 2.15/1.29  #Fact    : 0
% 2.15/1.29  #Define  : 0
% 2.15/1.29  #Split   : 2
% 2.15/1.29  #Chain   : 0
% 2.15/1.29  #Close   : 0
% 2.15/1.29  
% 2.15/1.29  Ordering : KBO
% 2.15/1.29  
% 2.15/1.29  Simplification rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Subsume      : 0
% 2.15/1.29  #Demod        : 55
% 2.15/1.29  #Tautology    : 103
% 2.15/1.29  #SimpNegUnit  : 6
% 2.15/1.29  #BackRed      : 0
% 2.15/1.29  
% 2.15/1.29  #Partial instantiations: 0
% 2.15/1.29  #Strategies tried      : 1
% 2.15/1.29  
% 2.15/1.29  Timing (in seconds)
% 2.15/1.29  ----------------------
% 2.15/1.30  Preprocessing        : 0.29
% 2.15/1.30  Parsing              : 0.15
% 2.15/1.30  CNF conversion       : 0.02
% 2.15/1.30  Main loop            : 0.25
% 2.15/1.30  Inferencing          : 0.10
% 2.15/1.30  Reduction            : 0.08
% 2.15/1.30  Demodulation         : 0.06
% 2.15/1.30  BG Simplification    : 0.01
% 2.15/1.30  Subsumption          : 0.03
% 2.15/1.30  Abstraction          : 0.01
% 2.15/1.30  MUC search           : 0.00
% 2.15/1.30  Cooper               : 0.00
% 2.15/1.30  Total                : 0.56
% 2.15/1.30  Index Insertion      : 0.00
% 2.15/1.30  Index Deletion       : 0.00
% 2.15/1.30  Index Matching       : 0.00
% 2.15/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
