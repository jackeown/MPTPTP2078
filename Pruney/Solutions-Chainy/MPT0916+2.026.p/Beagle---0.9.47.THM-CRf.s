%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:13 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.86s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 710 expanded)
%              Number of leaves         :   34 ( 241 expanded)
%              Depth                    :   13
%              Number of atoms          :  381 (2037 expanded)
%              Number of equality atoms :  100 ( 513 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_70,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

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

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_96,axiom,(
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

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(c_40,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] : k2_zfmisc_1(k2_zfmisc_1(A_18,B_19),C_20) = k3_zfmisc_1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2437,plain,(
    ! [A_474,B_475,C_476] :
      ( r2_hidden(k1_mcart_1(A_474),B_475)
      | ~ r2_hidden(A_474,k2_zfmisc_1(B_475,C_476)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3776,plain,(
    ! [A_686,A_687,B_688,C_689] :
      ( r2_hidden(k1_mcart_1(A_686),k2_zfmisc_1(A_687,B_688))
      | ~ r2_hidden(A_686,k3_zfmisc_1(A_687,B_688,C_689)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2437])).

tff(c_3790,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_3776])).

tff(c_22,plain,(
    ! [A_21,C_23,B_22] :
      ( r2_hidden(k2_mcart_1(A_21),C_23)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3816,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_3790,c_22])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_55,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_55])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_66,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_55])).

tff(c_1848,plain,(
    ! [A_368,C_369,B_370] :
      ( r2_hidden(k2_mcart_1(A_368),C_369)
      | ~ r2_hidden(A_368,k2_zfmisc_1(B_370,C_369)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2004,plain,(
    ! [A_401,C_402,A_403,B_404] :
      ( r2_hidden(k2_mcart_1(A_401),C_402)
      | ~ r2_hidden(A_401,k3_zfmisc_1(A_403,B_404,C_402)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1848])).

tff(c_2015,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_2004])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_67,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_55])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2182,plain,(
    ! [A_437,B_438,C_439,D_440] :
      ( k7_mcart_1(A_437,B_438,C_439,D_440) = k2_mcart_1(D_440)
      | ~ m1_subset_1(D_440,k3_zfmisc_1(A_437,B_438,C_439))
      | k1_xboole_0 = C_439
      | k1_xboole_0 = B_438
      | k1_xboole_0 = A_437 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2189,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_2182])).

tff(c_2200,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2189])).

tff(c_142,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden(k1_mcart_1(A_74),B_75)
      | ~ r2_hidden(A_74,k2_zfmisc_1(B_75,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1645,plain,(
    ! [A_332,A_333,B_334,C_335] :
      ( r2_hidden(k1_mcart_1(A_332),k2_zfmisc_1(A_333,B_334))
      | ~ r2_hidden(A_332,k3_zfmisc_1(A_333,B_334,C_335)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_142])).

tff(c_1656,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_1645])).

tff(c_24,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k1_mcart_1(A_21),B_22)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1679,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1656,c_24])).

tff(c_38,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_68,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_409,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k7_mcart_1(A_142,B_143,C_144,D_145) = k2_mcart_1(D_145)
      | ~ m1_subset_1(D_145,k3_zfmisc_1(A_142,B_143,C_144))
      | k1_xboole_0 = C_144
      | k1_xboole_0 = B_143
      | k1_xboole_0 = A_142 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_413,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_409])).

tff(c_451,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_471,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_8])).

tff(c_79,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_xboole_0(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_105,plain,(
    ! [A_65,B_66] :
      ( ~ r1_tarski(A_65,'#skF_1'(A_65,B_66))
      | r1_xboole_0(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_79,c_18])).

tff(c_110,plain,(
    ! [B_66] : r1_xboole_0(k1_xboole_0,B_66) ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_153,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_xboole_0(A_77,C_78)
      | ~ r1_xboole_0(B_79,C_78)
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_161,plain,(
    ! [A_80,B_81] :
      ( r1_xboole_0(A_80,B_81)
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_110,c_153])).

tff(c_10,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_xboole_0(A_7,C_9)
      | ~ r1_xboole_0(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_175,plain,(
    ! [A_88,B_89,A_90] :
      ( r1_xboole_0(A_88,B_89)
      | ~ r1_tarski(A_88,A_90)
      | ~ r1_tarski(A_90,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_161,c_10])).

tff(c_185,plain,(
    ! [B_89] :
      ( r1_xboole_0('#skF_5',B_89)
      | ~ r1_tarski('#skF_2',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_67,c_175])).

tff(c_190,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_464,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_190])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_464])).

tff(c_523,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_605,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( k6_mcart_1(A_168,B_169,C_170,D_171) = k2_mcart_1(k1_mcart_1(D_171))
      | ~ m1_subset_1(D_171,k3_zfmisc_1(A_168,B_169,C_170))
      | k1_xboole_0 = C_170
      | k1_xboole_0 = B_169
      | k1_xboole_0 = A_168 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_611,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_605])).

tff(c_614,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_523,c_611])).

tff(c_615,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_614])).

tff(c_529,plain,(
    ! [A_157,A_158,B_159,C_160] :
      ( r2_hidden(k1_mcart_1(A_157),k2_zfmisc_1(A_158,B_159))
      | ~ r2_hidden(A_157,k3_zfmisc_1(A_158,B_159,C_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_142])).

tff(c_543,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_529])).

tff(c_558,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_543,c_22])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_167,plain,(
    ! [C_5,B_81,A_80] :
      ( ~ r2_hidden(C_5,B_81)
      | ~ r2_hidden(C_5,A_80)
      | ~ r1_tarski(A_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_600,plain,(
    ! [A_167] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),A_167)
      | ~ r1_tarski(A_167,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_558,c_167])).

tff(c_604,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_558,c_600])).

tff(c_617,plain,(
    ~ r1_tarski('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_604])).

tff(c_647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_617])).

tff(c_649,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_614])).

tff(c_580,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k5_mcart_1(A_161,B_162,C_163,D_164) = k1_mcart_1(k1_mcart_1(D_164))
      | ~ m1_subset_1(D_164,k3_zfmisc_1(A_161,B_162,C_163))
      | k1_xboole_0 = C_163
      | k1_xboole_0 = B_162
      | k1_xboole_0 = A_161 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_586,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_580])).

tff(c_589,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_523,c_586])).

tff(c_668,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_649,c_589])).

tff(c_669,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_668])).

tff(c_125,plain,(
    ! [A_71,B_72,C_73] : k2_zfmisc_1(k2_zfmisc_1(A_71,B_72),C_73) = k3_zfmisc_1(A_71,B_72,C_73) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_318,plain,(
    ! [A_120,C_121,A_122,B_123] :
      ( r2_hidden(k2_mcart_1(A_120),C_121)
      | ~ r2_hidden(A_120,k3_zfmisc_1(A_122,B_123,C_121)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_22])).

tff(c_329,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_318])).

tff(c_74,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),B_54)
      | r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [B_57,A_58] :
      ( ~ r1_tarski(B_57,'#skF_1'(A_58,B_57))
      | r1_xboole_0(A_58,B_57) ) ),
    inference(resolution,[status(thm)],[c_74,c_18])).

tff(c_89,plain,(
    ! [A_58] : r1_xboole_0(A_58,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_191,plain,(
    ! [A_91,C_92,B_93,D_94] :
      ( r1_xboole_0(A_91,C_92)
      | ~ r1_xboole_0(B_93,D_94)
      | ~ r1_tarski(C_92,D_94)
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_205,plain,(
    ! [A_95,C_96,A_97] :
      ( r1_xboole_0(A_95,C_96)
      | ~ r1_tarski(C_96,k1_xboole_0)
      | ~ r1_tarski(A_95,A_97) ) ),
    inference(resolution,[status(thm)],[c_89,c_191])).

tff(c_229,plain,(
    ! [C_99] :
      ( r1_xboole_0('#skF_7',C_99)
      | ~ r1_tarski(C_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_65,c_205])).

tff(c_238,plain,(
    ! [C_5,C_99] :
      ( ~ r2_hidden(C_5,C_99)
      | ~ r2_hidden(C_5,'#skF_7')
      | ~ r1_tarski(C_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_229,c_2])).

tff(c_331,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7')
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_329,c_238])).

tff(c_343,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_331])).

tff(c_685,plain,(
    ~ r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_343])).

tff(c_701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_685])).

tff(c_702,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_668])).

tff(c_557,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_543,c_24])).

tff(c_720,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_702,c_557])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_720])).

tff(c_725,plain,(
    ! [B_175] : r1_xboole_0('#skF_5',B_175) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_774,plain,(
    ! [C_183,B_184] :
      ( ~ r2_hidden(C_183,B_184)
      | ~ r2_hidden(C_183,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_725,c_2])).

tff(c_804,plain,(
    ! [A_189,B_190] :
      ( ~ r2_hidden('#skF_1'(A_189,B_190),'#skF_5')
      | r1_xboole_0(A_189,B_190) ) ),
    inference(resolution,[status(thm)],[c_4,c_774])).

tff(c_826,plain,(
    ! [A_197] : r1_xboole_0(A_197,'#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_804])).

tff(c_836,plain,(
    ! [C_5,A_197] :
      ( ~ r2_hidden(C_5,'#skF_5')
      | ~ r2_hidden(C_5,A_197) ) ),
    inference(resolution,[status(thm)],[c_826,c_2])).

tff(c_1702,plain,(
    ! [A_197] : ~ r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),A_197) ),
    inference(resolution,[status(thm)],[c_1679,c_836])).

tff(c_1726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1702,c_1679])).

tff(c_1728,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1739,plain,(
    ! [A_338,B_339] :
      ( r2_hidden('#skF_1'(A_338,B_339),B_339)
      | r1_xboole_0(A_338,B_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1749,plain,(
    ! [B_342,A_343] :
      ( ~ r1_tarski(B_342,'#skF_1'(A_343,B_342))
      | r1_xboole_0(A_343,B_342) ) ),
    inference(resolution,[status(thm)],[c_1739,c_18])).

tff(c_1754,plain,(
    ! [A_343] : r1_xboole_0(A_343,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1749])).

tff(c_1892,plain,(
    ! [A_378,C_379,B_380,D_381] :
      ( r1_xboole_0(A_378,C_379)
      | ~ r1_xboole_0(B_380,D_381)
      | ~ r1_tarski(C_379,D_381)
      | ~ r1_tarski(A_378,B_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1904,plain,(
    ! [A_382,C_383,A_384] :
      ( r1_xboole_0(A_382,C_383)
      | ~ r1_tarski(C_383,k1_xboole_0)
      | ~ r1_tarski(A_382,A_384) ) ),
    inference(resolution,[status(thm)],[c_1754,c_1892])).

tff(c_1928,plain,(
    ! [C_386] :
      ( r1_xboole_0('#skF_5',C_386)
      | ~ r1_tarski(C_386,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_67,c_1904])).

tff(c_1984,plain,(
    ! [C_398,C_399] :
      ( ~ r2_hidden(C_398,C_399)
      | ~ r2_hidden(C_398,'#skF_5')
      | ~ r1_tarski(C_399,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1928,c_2])).

tff(c_1990,plain,
    ( ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5')
    | ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1728,c_1984])).

tff(c_1997,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1728,c_1990])).

tff(c_2208,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2200,c_1997])).

tff(c_2227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2208])).

tff(c_2228,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_2189])).

tff(c_2255,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2228])).

tff(c_1727,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1738,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1727])).

tff(c_2256,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_1738])).

tff(c_2259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2015,c_2256])).

tff(c_2260,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2228])).

tff(c_2262,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2260])).

tff(c_1772,plain,(
    ! [A_351,B_352,C_353] : k2_zfmisc_1(k2_zfmisc_1(A_351,B_352),C_353) = k3_zfmisc_1(A_351,B_352,C_353) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2141,plain,(
    ! [A_433,A_434,B_435,C_436] :
      ( r2_hidden(k1_mcart_1(A_433),k2_zfmisc_1(A_434,B_435))
      | ~ r2_hidden(A_433,k3_zfmisc_1(A_434,B_435,C_436)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1772,c_24])).

tff(c_2155,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_2141])).

tff(c_2169,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2155,c_22])).

tff(c_1744,plain,(
    ! [A_340,B_341] :
      ( r2_hidden('#skF_1'(A_340,B_341),A_340)
      | r1_xboole_0(A_340,B_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1765,plain,(
    ! [A_348,B_349] :
      ( ~ r1_tarski(A_348,'#skF_1'(A_348,B_349))
      | r1_xboole_0(A_348,B_349) ) ),
    inference(resolution,[status(thm)],[c_1744,c_18])).

tff(c_1770,plain,(
    ! [B_349] : r1_xboole_0(k1_xboole_0,B_349) ),
    inference(resolution,[status(thm)],[c_8,c_1765])).

tff(c_1820,plain,(
    ! [A_361,C_362,B_363] :
      ( r1_xboole_0(A_361,C_362)
      | ~ r1_xboole_0(B_363,C_362)
      | ~ r1_tarski(A_361,B_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1828,plain,(
    ! [A_364,B_365] :
      ( r1_xboole_0(A_364,B_365)
      | ~ r1_tarski(A_364,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1770,c_1820])).

tff(c_1834,plain,(
    ! [C_5,B_365,A_364] :
      ( ~ r2_hidden(C_5,B_365)
      | ~ r2_hidden(C_5,A_364)
      | ~ r1_tarski(A_364,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1828,c_2])).

tff(c_2250,plain,(
    ! [A_447] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),A_447)
      | ~ r1_tarski(A_447,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2169,c_1834])).

tff(c_2254,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2169,c_2250])).

tff(c_2263,plain,(
    ~ r1_tarski('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2262,c_2254])).

tff(c_2296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2263])).

tff(c_2297,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2260])).

tff(c_1938,plain,(
    ! [C_387] :
      ( r1_xboole_0('#skF_7',C_387)
      | ~ r1_tarski(C_387,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_65,c_1904])).

tff(c_1947,plain,(
    ! [C_5,C_387] :
      ( ~ r2_hidden(C_5,C_387)
      | ~ r2_hidden(C_5,'#skF_7')
      | ~ r1_tarski(C_387,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1938,c_2])).

tff(c_2019,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7')
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2015,c_1947])).

tff(c_2030,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2015,c_2019])).

tff(c_2324,plain,(
    ~ r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2297,c_2030])).

tff(c_2344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_2324])).

tff(c_2345,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1727])).

tff(c_2712,plain,(
    ! [A_538,B_539,C_540,D_541] :
      ( k7_mcart_1(A_538,B_539,C_540,D_541) = k2_mcart_1(D_541)
      | ~ m1_subset_1(D_541,k3_zfmisc_1(A_538,B_539,C_540))
      | k1_xboole_0 = C_540
      | k1_xboole_0 = B_539
      | k1_xboole_0 = A_538 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2716,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_2712])).

tff(c_2736,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2716])).

tff(c_2351,plain,(
    ! [A_452,B_453] :
      ( r2_hidden('#skF_1'(A_452,B_453),A_452)
      | r1_xboole_0(A_452,B_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2361,plain,(
    ! [A_456,B_457] :
      ( ~ r1_tarski(A_456,'#skF_1'(A_456,B_457))
      | r1_xboole_0(A_456,B_457) ) ),
    inference(resolution,[status(thm)],[c_2351,c_18])).

tff(c_2366,plain,(
    ! [B_457] : r1_xboole_0(k1_xboole_0,B_457) ),
    inference(resolution,[status(thm)],[c_8,c_2361])).

tff(c_2448,plain,(
    ! [A_477,C_478,B_479] :
      ( r1_xboole_0(A_477,C_478)
      | ~ r1_xboole_0(B_479,C_478)
      | ~ r1_tarski(A_477,B_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2467,plain,(
    ! [A_483,B_484] :
      ( r1_xboole_0(A_483,B_484)
      | ~ r1_tarski(A_483,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2366,c_2448])).

tff(c_2555,plain,(
    ! [C_504,B_505,A_506] :
      ( ~ r2_hidden(C_504,B_505)
      | ~ r2_hidden(C_504,A_506)
      | ~ r1_tarski(A_506,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2467,c_2])).

tff(c_2602,plain,(
    ! [A_516] :
      ( ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),A_516)
      | ~ r1_tarski(A_516,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1728,c_2555])).

tff(c_2606,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1728,c_2602])).

tff(c_2744,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2736,c_2606])).

tff(c_2764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2744])).

tff(c_2766,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2716])).

tff(c_2777,plain,(
    ! [A_545,B_546,C_547,D_548] :
      ( k5_mcart_1(A_545,B_546,C_547,D_548) = k1_mcart_1(k1_mcart_1(D_548))
      | ~ m1_subset_1(D_548,k3_zfmisc_1(A_545,B_546,C_547))
      | k1_xboole_0 = C_547
      | k1_xboole_0 = B_546
      | k1_xboole_0 = A_545 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2780,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_2777])).

tff(c_2783,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2766,c_2780])).

tff(c_2823,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2783])).

tff(c_2849,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2823,c_8])).

tff(c_2474,plain,(
    ! [A_485,B_486,A_487] :
      ( r1_xboole_0(A_485,B_486)
      | ~ r1_tarski(A_485,A_487)
      | ~ r1_tarski(A_487,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2467,c_10])).

tff(c_2483,plain,(
    ! [B_486] :
      ( r1_xboole_0('#skF_6',B_486)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_66,c_2474])).

tff(c_2488,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2483])).

tff(c_2840,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2823,c_2488])).

tff(c_2906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2849,c_2840])).

tff(c_2908,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2783])).

tff(c_2910,plain,(
    ! [A_561,B_562,C_563,D_564] :
      ( k6_mcart_1(A_561,B_562,C_563,D_564) = k2_mcart_1(k1_mcart_1(D_564))
      | ~ m1_subset_1(D_564,k3_zfmisc_1(A_561,B_562,C_563))
      | k1_xboole_0 = C_563
      | k1_xboole_0 = B_562
      | k1_xboole_0 = A_561 ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2916,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_2910])).

tff(c_2919,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2766,c_2908,c_2916])).

tff(c_2924,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2919])).

tff(c_2346,plain,(
    r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1727])).

tff(c_2356,plain,(
    ! [A_454,B_455] :
      ( r2_hidden('#skF_1'(A_454,B_455),B_455)
      | r1_xboole_0(A_454,B_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2388,plain,(
    ! [B_464,A_465] :
      ( ~ r1_tarski(B_464,'#skF_1'(A_465,B_464))
      | r1_xboole_0(A_465,B_464) ) ),
    inference(resolution,[status(thm)],[c_2356,c_18])).

tff(c_2393,plain,(
    ! [A_465] : r1_xboole_0(A_465,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_2388])).

tff(c_2498,plain,(
    ! [A_494,C_495,B_496,D_497] :
      ( r1_xboole_0(A_494,C_495)
      | ~ r1_xboole_0(B_496,D_497)
      | ~ r1_tarski(C_495,D_497)
      | ~ r1_tarski(A_494,B_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2511,plain,(
    ! [A_498,C_499,A_500] :
      ( r1_xboole_0(A_498,C_499)
      | ~ r1_tarski(C_499,k1_xboole_0)
      | ~ r1_tarski(A_498,A_500) ) ),
    inference(resolution,[status(thm)],[c_2393,c_2498])).

tff(c_2545,plain,(
    ! [C_503] :
      ( r1_xboole_0('#skF_7',C_503)
      | ~ r1_tarski(C_503,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_65,c_2511])).

tff(c_2625,plain,(
    ! [C_519,C_520] :
      ( ~ r2_hidden(C_519,C_520)
      | ~ r2_hidden(C_519,'#skF_7')
      | ~ r1_tarski(C_520,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2545,c_2])).

tff(c_2631,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2346,c_2625])).

tff(c_2640,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2346,c_2631])).

tff(c_2935,plain,(
    ~ r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2924,c_2640])).

tff(c_2955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_2935])).

tff(c_2956,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2919])).

tff(c_2963,plain,(
    ! [A_565,A_566,B_567,C_568] :
      ( r2_hidden(k1_mcart_1(A_565),k2_zfmisc_1(A_566,B_567))
      | ~ r2_hidden(A_565,k3_zfmisc_1(A_566,B_567,C_568)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2437])).

tff(c_2977,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_2963])).

tff(c_2983,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2977,c_22])).

tff(c_2992,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2956,c_2983])).

tff(c_2994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2345,c_2992])).

tff(c_2997,plain,(
    ! [B_569] : r1_xboole_0('#skF_6',B_569) ),
    inference(splitRight,[status(thm)],[c_2483])).

tff(c_3032,plain,(
    ! [C_579,B_580] :
      ( ~ r2_hidden(C_579,B_580)
      | ~ r2_hidden(C_579,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2997,c_2])).

tff(c_3078,plain,(
    ! [A_591,B_592] :
      ( ~ r2_hidden('#skF_1'(A_591,B_592),'#skF_6')
      | r1_xboole_0(A_591,B_592) ) ),
    inference(resolution,[status(thm)],[c_6,c_3032])).

tff(c_3090,plain,(
    ! [A_593] : r1_xboole_0(A_593,'#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_3078])).

tff(c_3097,plain,(
    ! [C_5,A_593] :
      ( ~ r2_hidden(C_5,'#skF_6')
      | ~ r2_hidden(C_5,A_593) ) ),
    inference(resolution,[status(thm)],[c_3090,c_2])).

tff(c_3846,plain,(
    ! [A_593] : ~ r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),A_593) ),
    inference(resolution,[status(thm)],[c_3816,c_3097])).

tff(c_3875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3846,c_3816])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.07  
% 5.86/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 5.86/2.07  
% 5.86/2.07  %Foreground sorts:
% 5.86/2.07  
% 5.86/2.07  
% 5.86/2.07  %Background operators:
% 5.86/2.07  
% 5.86/2.07  
% 5.86/2.07  %Foreground operators:
% 5.86/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.86/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.86/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.86/2.07  tff('#skF_7', type, '#skF_7': $i).
% 5.86/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.86/2.07  tff('#skF_5', type, '#skF_5': $i).
% 5.86/2.07  tff('#skF_6', type, '#skF_6': $i).
% 5.86/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.86/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.86/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.86/2.07  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 5.86/2.07  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 5.86/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.86/2.07  tff('#skF_8', type, '#skF_8': $i).
% 5.86/2.07  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 5.86/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.86/2.07  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 5.86/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.86/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.86/2.07  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 5.86/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.86/2.07  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 5.86/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.86/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.86/2.07  
% 5.86/2.10  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 5.86/2.10  tff(f_70, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 5.86/2.10  tff(f_76, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 5.86/2.10  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.86/2.10  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.86/2.10  tff(f_96, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 5.86/2.10  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.86/2.10  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.86/2.10  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 5.86/2.10  tff(f_59, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 5.86/2.10  tff(c_40, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.86/2.10  tff(c_20, plain, (![A_18, B_19, C_20]: (k2_zfmisc_1(k2_zfmisc_1(A_18, B_19), C_20)=k3_zfmisc_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.86/2.10  tff(c_2437, plain, (![A_474, B_475, C_476]: (r2_hidden(k1_mcart_1(A_474), B_475) | ~r2_hidden(A_474, k2_zfmisc_1(B_475, C_476)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.86/2.10  tff(c_3776, plain, (![A_686, A_687, B_688, C_689]: (r2_hidden(k1_mcart_1(A_686), k2_zfmisc_1(A_687, B_688)) | ~r2_hidden(A_686, k3_zfmisc_1(A_687, B_688, C_689)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2437])).
% 5.86/2.10  tff(c_3790, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_3776])).
% 5.86/2.10  tff(c_22, plain, (![A_21, C_23, B_22]: (r2_hidden(k2_mcart_1(A_21), C_23) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.86/2.10  tff(c_3816, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_3790, c_22])).
% 5.86/2.10  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.86/2.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.86/2.10  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.86/2.10  tff(c_55, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.86/2.10  tff(c_65, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_55])).
% 5.86/2.10  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.86/2.10  tff(c_66, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_55])).
% 5.86/2.10  tff(c_1848, plain, (![A_368, C_369, B_370]: (r2_hidden(k2_mcart_1(A_368), C_369) | ~r2_hidden(A_368, k2_zfmisc_1(B_370, C_369)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.86/2.10  tff(c_2004, plain, (![A_401, C_402, A_403, B_404]: (r2_hidden(k2_mcart_1(A_401), C_402) | ~r2_hidden(A_401, k3_zfmisc_1(A_403, B_404, C_402)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1848])).
% 5.86/2.10  tff(c_2015, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_40, c_2004])).
% 5.86/2.10  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.86/2.10  tff(c_67, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_55])).
% 5.86/2.10  tff(c_42, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.86/2.10  tff(c_2182, plain, (![A_437, B_438, C_439, D_440]: (k7_mcart_1(A_437, B_438, C_439, D_440)=k2_mcart_1(D_440) | ~m1_subset_1(D_440, k3_zfmisc_1(A_437, B_438, C_439)) | k1_xboole_0=C_439 | k1_xboole_0=B_438 | k1_xboole_0=A_437)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.86/2.10  tff(c_2189, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_42, c_2182])).
% 5.86/2.10  tff(c_2200, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2189])).
% 5.86/2.10  tff(c_142, plain, (![A_74, B_75, C_76]: (r2_hidden(k1_mcart_1(A_74), B_75) | ~r2_hidden(A_74, k2_zfmisc_1(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.86/2.10  tff(c_1645, plain, (![A_332, A_333, B_334, C_335]: (r2_hidden(k1_mcart_1(A_332), k2_zfmisc_1(A_333, B_334)) | ~r2_hidden(A_332, k3_zfmisc_1(A_333, B_334, C_335)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_142])).
% 5.86/2.10  tff(c_1656, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_1645])).
% 5.86/2.10  tff(c_24, plain, (![A_21, B_22, C_23]: (r2_hidden(k1_mcart_1(A_21), B_22) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.86/2.10  tff(c_1679, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_1656, c_24])).
% 5.86/2.10  tff(c_38, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.86/2.10  tff(c_68, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_38])).
% 5.86/2.10  tff(c_409, plain, (![A_142, B_143, C_144, D_145]: (k7_mcart_1(A_142, B_143, C_144, D_145)=k2_mcart_1(D_145) | ~m1_subset_1(D_145, k3_zfmisc_1(A_142, B_143, C_144)) | k1_xboole_0=C_144 | k1_xboole_0=B_143 | k1_xboole_0=A_142)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.86/2.10  tff(c_413, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_42, c_409])).
% 5.86/2.10  tff(c_451, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_413])).
% 5.86/2.10  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.86/2.10  tff(c_471, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_451, c_8])).
% 5.86/2.10  tff(c_79, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.86/2.10  tff(c_18, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.86/2.10  tff(c_105, plain, (![A_65, B_66]: (~r1_tarski(A_65, '#skF_1'(A_65, B_66)) | r1_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_79, c_18])).
% 5.86/2.10  tff(c_110, plain, (![B_66]: (r1_xboole_0(k1_xboole_0, B_66))), inference(resolution, [status(thm)], [c_8, c_105])).
% 5.86/2.10  tff(c_153, plain, (![A_77, C_78, B_79]: (r1_xboole_0(A_77, C_78) | ~r1_xboole_0(B_79, C_78) | ~r1_tarski(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.86/2.10  tff(c_161, plain, (![A_80, B_81]: (r1_xboole_0(A_80, B_81) | ~r1_tarski(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_110, c_153])).
% 5.86/2.10  tff(c_10, plain, (![A_7, C_9, B_8]: (r1_xboole_0(A_7, C_9) | ~r1_xboole_0(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.86/2.10  tff(c_175, plain, (![A_88, B_89, A_90]: (r1_xboole_0(A_88, B_89) | ~r1_tarski(A_88, A_90) | ~r1_tarski(A_90, k1_xboole_0))), inference(resolution, [status(thm)], [c_161, c_10])).
% 5.86/2.10  tff(c_185, plain, (![B_89]: (r1_xboole_0('#skF_5', B_89) | ~r1_tarski('#skF_2', k1_xboole_0))), inference(resolution, [status(thm)], [c_67, c_175])).
% 5.86/2.10  tff(c_190, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_185])).
% 5.86/2.10  tff(c_464, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_451, c_190])).
% 5.86/2.10  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_471, c_464])).
% 5.86/2.10  tff(c_523, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_413])).
% 5.86/2.10  tff(c_605, plain, (![A_168, B_169, C_170, D_171]: (k6_mcart_1(A_168, B_169, C_170, D_171)=k2_mcart_1(k1_mcart_1(D_171)) | ~m1_subset_1(D_171, k3_zfmisc_1(A_168, B_169, C_170)) | k1_xboole_0=C_170 | k1_xboole_0=B_169 | k1_xboole_0=A_168)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.86/2.10  tff(c_611, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_42, c_605])).
% 5.86/2.10  tff(c_614, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_523, c_611])).
% 5.86/2.10  tff(c_615, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_614])).
% 5.86/2.10  tff(c_529, plain, (![A_157, A_158, B_159, C_160]: (r2_hidden(k1_mcart_1(A_157), k2_zfmisc_1(A_158, B_159)) | ~r2_hidden(A_157, k3_zfmisc_1(A_158, B_159, C_160)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_142])).
% 5.86/2.10  tff(c_543, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_529])).
% 5.86/2.10  tff(c_558, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_543, c_22])).
% 5.86/2.10  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.86/2.10  tff(c_167, plain, (![C_5, B_81, A_80]: (~r2_hidden(C_5, B_81) | ~r2_hidden(C_5, A_80) | ~r1_tarski(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_161, c_2])).
% 5.86/2.10  tff(c_600, plain, (![A_167]: (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), A_167) | ~r1_tarski(A_167, k1_xboole_0))), inference(resolution, [status(thm)], [c_558, c_167])).
% 5.86/2.10  tff(c_604, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_558, c_600])).
% 5.86/2.10  tff(c_617, plain, (~r1_tarski('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_615, c_604])).
% 5.86/2.10  tff(c_647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_617])).
% 5.86/2.10  tff(c_649, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_614])).
% 5.86/2.10  tff(c_580, plain, (![A_161, B_162, C_163, D_164]: (k5_mcart_1(A_161, B_162, C_163, D_164)=k1_mcart_1(k1_mcart_1(D_164)) | ~m1_subset_1(D_164, k3_zfmisc_1(A_161, B_162, C_163)) | k1_xboole_0=C_163 | k1_xboole_0=B_162 | k1_xboole_0=A_161)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.86/2.10  tff(c_586, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_42, c_580])).
% 5.86/2.10  tff(c_589, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_523, c_586])).
% 5.86/2.10  tff(c_668, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_649, c_589])).
% 5.86/2.10  tff(c_669, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_668])).
% 5.86/2.10  tff(c_125, plain, (![A_71, B_72, C_73]: (k2_zfmisc_1(k2_zfmisc_1(A_71, B_72), C_73)=k3_zfmisc_1(A_71, B_72, C_73))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.86/2.10  tff(c_318, plain, (![A_120, C_121, A_122, B_123]: (r2_hidden(k2_mcart_1(A_120), C_121) | ~r2_hidden(A_120, k3_zfmisc_1(A_122, B_123, C_121)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_22])).
% 5.86/2.10  tff(c_329, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_40, c_318])).
% 5.86/2.10  tff(c_74, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), B_54) | r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.86/2.10  tff(c_84, plain, (![B_57, A_58]: (~r1_tarski(B_57, '#skF_1'(A_58, B_57)) | r1_xboole_0(A_58, B_57))), inference(resolution, [status(thm)], [c_74, c_18])).
% 5.86/2.10  tff(c_89, plain, (![A_58]: (r1_xboole_0(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_84])).
% 5.86/2.10  tff(c_191, plain, (![A_91, C_92, B_93, D_94]: (r1_xboole_0(A_91, C_92) | ~r1_xboole_0(B_93, D_94) | ~r1_tarski(C_92, D_94) | ~r1_tarski(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.86/2.10  tff(c_205, plain, (![A_95, C_96, A_97]: (r1_xboole_0(A_95, C_96) | ~r1_tarski(C_96, k1_xboole_0) | ~r1_tarski(A_95, A_97))), inference(resolution, [status(thm)], [c_89, c_191])).
% 5.86/2.10  tff(c_229, plain, (![C_99]: (r1_xboole_0('#skF_7', C_99) | ~r1_tarski(C_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_65, c_205])).
% 5.86/2.10  tff(c_238, plain, (![C_5, C_99]: (~r2_hidden(C_5, C_99) | ~r2_hidden(C_5, '#skF_7') | ~r1_tarski(C_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_229, c_2])).
% 5.86/2.10  tff(c_331, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7') | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_329, c_238])).
% 5.86/2.10  tff(c_343, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_329, c_331])).
% 5.86/2.10  tff(c_685, plain, (~r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_669, c_343])).
% 5.86/2.10  tff(c_701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_685])).
% 5.86/2.10  tff(c_702, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_668])).
% 5.86/2.10  tff(c_557, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_543, c_24])).
% 5.86/2.10  tff(c_720, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_702, c_557])).
% 5.86/2.10  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_720])).
% 5.86/2.10  tff(c_725, plain, (![B_175]: (r1_xboole_0('#skF_5', B_175))), inference(splitRight, [status(thm)], [c_185])).
% 5.86/2.10  tff(c_774, plain, (![C_183, B_184]: (~r2_hidden(C_183, B_184) | ~r2_hidden(C_183, '#skF_5'))), inference(resolution, [status(thm)], [c_725, c_2])).
% 5.86/2.10  tff(c_804, plain, (![A_189, B_190]: (~r2_hidden('#skF_1'(A_189, B_190), '#skF_5') | r1_xboole_0(A_189, B_190))), inference(resolution, [status(thm)], [c_4, c_774])).
% 5.86/2.10  tff(c_826, plain, (![A_197]: (r1_xboole_0(A_197, '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_804])).
% 5.86/2.10  tff(c_836, plain, (![C_5, A_197]: (~r2_hidden(C_5, '#skF_5') | ~r2_hidden(C_5, A_197))), inference(resolution, [status(thm)], [c_826, c_2])).
% 5.86/2.10  tff(c_1702, plain, (![A_197]: (~r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), A_197))), inference(resolution, [status(thm)], [c_1679, c_836])).
% 5.86/2.10  tff(c_1726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1702, c_1679])).
% 5.86/2.10  tff(c_1728, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 5.86/2.10  tff(c_1739, plain, (![A_338, B_339]: (r2_hidden('#skF_1'(A_338, B_339), B_339) | r1_xboole_0(A_338, B_339))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.86/2.10  tff(c_1749, plain, (![B_342, A_343]: (~r1_tarski(B_342, '#skF_1'(A_343, B_342)) | r1_xboole_0(A_343, B_342))), inference(resolution, [status(thm)], [c_1739, c_18])).
% 5.86/2.10  tff(c_1754, plain, (![A_343]: (r1_xboole_0(A_343, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1749])).
% 5.86/2.10  tff(c_1892, plain, (![A_378, C_379, B_380, D_381]: (r1_xboole_0(A_378, C_379) | ~r1_xboole_0(B_380, D_381) | ~r1_tarski(C_379, D_381) | ~r1_tarski(A_378, B_380))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.86/2.10  tff(c_1904, plain, (![A_382, C_383, A_384]: (r1_xboole_0(A_382, C_383) | ~r1_tarski(C_383, k1_xboole_0) | ~r1_tarski(A_382, A_384))), inference(resolution, [status(thm)], [c_1754, c_1892])).
% 5.86/2.10  tff(c_1928, plain, (![C_386]: (r1_xboole_0('#skF_5', C_386) | ~r1_tarski(C_386, k1_xboole_0))), inference(resolution, [status(thm)], [c_67, c_1904])).
% 5.86/2.10  tff(c_1984, plain, (![C_398, C_399]: (~r2_hidden(C_398, C_399) | ~r2_hidden(C_398, '#skF_5') | ~r1_tarski(C_399, k1_xboole_0))), inference(resolution, [status(thm)], [c_1928, c_2])).
% 5.86/2.10  tff(c_1990, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5') | ~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_1728, c_1984])).
% 5.86/2.10  tff(c_1997, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1728, c_1990])).
% 5.86/2.10  tff(c_2208, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2200, c_1997])).
% 5.86/2.10  tff(c_2227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_2208])).
% 5.86/2.10  tff(c_2228, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_2189])).
% 5.86/2.10  tff(c_2255, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_2228])).
% 5.86/2.10  tff(c_1727, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_38])).
% 5.86/2.10  tff(c_1738, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1727])).
% 5.86/2.10  tff(c_2256, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2255, c_1738])).
% 5.86/2.10  tff(c_2259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2015, c_2256])).
% 5.86/2.10  tff(c_2260, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2228])).
% 5.86/2.10  tff(c_2262, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2260])).
% 5.86/2.10  tff(c_1772, plain, (![A_351, B_352, C_353]: (k2_zfmisc_1(k2_zfmisc_1(A_351, B_352), C_353)=k3_zfmisc_1(A_351, B_352, C_353))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.86/2.10  tff(c_2141, plain, (![A_433, A_434, B_435, C_436]: (r2_hidden(k1_mcart_1(A_433), k2_zfmisc_1(A_434, B_435)) | ~r2_hidden(A_433, k3_zfmisc_1(A_434, B_435, C_436)))), inference(superposition, [status(thm), theory('equality')], [c_1772, c_24])).
% 5.86/2.10  tff(c_2155, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_2141])).
% 5.86/2.10  tff(c_2169, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2155, c_22])).
% 5.86/2.10  tff(c_1744, plain, (![A_340, B_341]: (r2_hidden('#skF_1'(A_340, B_341), A_340) | r1_xboole_0(A_340, B_341))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.86/2.10  tff(c_1765, plain, (![A_348, B_349]: (~r1_tarski(A_348, '#skF_1'(A_348, B_349)) | r1_xboole_0(A_348, B_349))), inference(resolution, [status(thm)], [c_1744, c_18])).
% 5.86/2.10  tff(c_1770, plain, (![B_349]: (r1_xboole_0(k1_xboole_0, B_349))), inference(resolution, [status(thm)], [c_8, c_1765])).
% 5.86/2.10  tff(c_1820, plain, (![A_361, C_362, B_363]: (r1_xboole_0(A_361, C_362) | ~r1_xboole_0(B_363, C_362) | ~r1_tarski(A_361, B_363))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.86/2.10  tff(c_1828, plain, (![A_364, B_365]: (r1_xboole_0(A_364, B_365) | ~r1_tarski(A_364, k1_xboole_0))), inference(resolution, [status(thm)], [c_1770, c_1820])).
% 5.86/2.10  tff(c_1834, plain, (![C_5, B_365, A_364]: (~r2_hidden(C_5, B_365) | ~r2_hidden(C_5, A_364) | ~r1_tarski(A_364, k1_xboole_0))), inference(resolution, [status(thm)], [c_1828, c_2])).
% 5.86/2.10  tff(c_2250, plain, (![A_447]: (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), A_447) | ~r1_tarski(A_447, k1_xboole_0))), inference(resolution, [status(thm)], [c_2169, c_1834])).
% 5.86/2.10  tff(c_2254, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_2169, c_2250])).
% 5.86/2.10  tff(c_2263, plain, (~r1_tarski('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2262, c_2254])).
% 5.86/2.10  tff(c_2296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_2263])).
% 5.86/2.10  tff(c_2297, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2260])).
% 5.86/2.10  tff(c_1938, plain, (![C_387]: (r1_xboole_0('#skF_7', C_387) | ~r1_tarski(C_387, k1_xboole_0))), inference(resolution, [status(thm)], [c_65, c_1904])).
% 5.86/2.10  tff(c_1947, plain, (![C_5, C_387]: (~r2_hidden(C_5, C_387) | ~r2_hidden(C_5, '#skF_7') | ~r1_tarski(C_387, k1_xboole_0))), inference(resolution, [status(thm)], [c_1938, c_2])).
% 5.86/2.10  tff(c_2019, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7') | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_2015, c_1947])).
% 5.86/2.10  tff(c_2030, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2015, c_2019])).
% 5.86/2.10  tff(c_2324, plain, (~r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2297, c_2030])).
% 5.86/2.10  tff(c_2344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_2324])).
% 5.86/2.10  tff(c_2345, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_1727])).
% 5.86/2.10  tff(c_2712, plain, (![A_538, B_539, C_540, D_541]: (k7_mcart_1(A_538, B_539, C_540, D_541)=k2_mcart_1(D_541) | ~m1_subset_1(D_541, k3_zfmisc_1(A_538, B_539, C_540)) | k1_xboole_0=C_540 | k1_xboole_0=B_539 | k1_xboole_0=A_538)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.86/2.10  tff(c_2716, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_42, c_2712])).
% 5.86/2.10  tff(c_2736, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2716])).
% 5.86/2.10  tff(c_2351, plain, (![A_452, B_453]: (r2_hidden('#skF_1'(A_452, B_453), A_452) | r1_xboole_0(A_452, B_453))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.86/2.10  tff(c_2361, plain, (![A_456, B_457]: (~r1_tarski(A_456, '#skF_1'(A_456, B_457)) | r1_xboole_0(A_456, B_457))), inference(resolution, [status(thm)], [c_2351, c_18])).
% 5.86/2.10  tff(c_2366, plain, (![B_457]: (r1_xboole_0(k1_xboole_0, B_457))), inference(resolution, [status(thm)], [c_8, c_2361])).
% 5.86/2.10  tff(c_2448, plain, (![A_477, C_478, B_479]: (r1_xboole_0(A_477, C_478) | ~r1_xboole_0(B_479, C_478) | ~r1_tarski(A_477, B_479))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.86/2.10  tff(c_2467, plain, (![A_483, B_484]: (r1_xboole_0(A_483, B_484) | ~r1_tarski(A_483, k1_xboole_0))), inference(resolution, [status(thm)], [c_2366, c_2448])).
% 5.86/2.10  tff(c_2555, plain, (![C_504, B_505, A_506]: (~r2_hidden(C_504, B_505) | ~r2_hidden(C_504, A_506) | ~r1_tarski(A_506, k1_xboole_0))), inference(resolution, [status(thm)], [c_2467, c_2])).
% 5.86/2.10  tff(c_2602, plain, (![A_516]: (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), A_516) | ~r1_tarski(A_516, k1_xboole_0))), inference(resolution, [status(thm)], [c_1728, c_2555])).
% 5.86/2.10  tff(c_2606, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_1728, c_2602])).
% 5.86/2.10  tff(c_2744, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2736, c_2606])).
% 5.86/2.10  tff(c_2764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_2744])).
% 5.86/2.10  tff(c_2766, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2716])).
% 5.86/2.10  tff(c_2777, plain, (![A_545, B_546, C_547, D_548]: (k5_mcart_1(A_545, B_546, C_547, D_548)=k1_mcart_1(k1_mcart_1(D_548)) | ~m1_subset_1(D_548, k3_zfmisc_1(A_545, B_546, C_547)) | k1_xboole_0=C_547 | k1_xboole_0=B_546 | k1_xboole_0=A_545)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.86/2.10  tff(c_2780, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_42, c_2777])).
% 5.86/2.10  tff(c_2783, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2766, c_2780])).
% 5.86/2.10  tff(c_2823, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2783])).
% 5.86/2.10  tff(c_2849, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2823, c_8])).
% 5.86/2.10  tff(c_2474, plain, (![A_485, B_486, A_487]: (r1_xboole_0(A_485, B_486) | ~r1_tarski(A_485, A_487) | ~r1_tarski(A_487, k1_xboole_0))), inference(resolution, [status(thm)], [c_2467, c_10])).
% 5.86/2.10  tff(c_2483, plain, (![B_486]: (r1_xboole_0('#skF_6', B_486) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_66, c_2474])).
% 5.86/2.10  tff(c_2488, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2483])).
% 5.86/2.10  tff(c_2840, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2823, c_2488])).
% 5.86/2.10  tff(c_2906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2849, c_2840])).
% 5.86/2.10  tff(c_2908, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2783])).
% 5.86/2.10  tff(c_2910, plain, (![A_561, B_562, C_563, D_564]: (k6_mcart_1(A_561, B_562, C_563, D_564)=k2_mcart_1(k1_mcart_1(D_564)) | ~m1_subset_1(D_564, k3_zfmisc_1(A_561, B_562, C_563)) | k1_xboole_0=C_563 | k1_xboole_0=B_562 | k1_xboole_0=A_561)), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.86/2.10  tff(c_2916, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_42, c_2910])).
% 5.86/2.10  tff(c_2919, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2766, c_2908, c_2916])).
% 5.86/2.10  tff(c_2924, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2919])).
% 5.86/2.10  tff(c_2346, plain, (r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_1727])).
% 5.86/2.10  tff(c_2356, plain, (![A_454, B_455]: (r2_hidden('#skF_1'(A_454, B_455), B_455) | r1_xboole_0(A_454, B_455))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.86/2.10  tff(c_2388, plain, (![B_464, A_465]: (~r1_tarski(B_464, '#skF_1'(A_465, B_464)) | r1_xboole_0(A_465, B_464))), inference(resolution, [status(thm)], [c_2356, c_18])).
% 5.86/2.10  tff(c_2393, plain, (![A_465]: (r1_xboole_0(A_465, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_2388])).
% 5.86/2.10  tff(c_2498, plain, (![A_494, C_495, B_496, D_497]: (r1_xboole_0(A_494, C_495) | ~r1_xboole_0(B_496, D_497) | ~r1_tarski(C_495, D_497) | ~r1_tarski(A_494, B_496))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.86/2.10  tff(c_2511, plain, (![A_498, C_499, A_500]: (r1_xboole_0(A_498, C_499) | ~r1_tarski(C_499, k1_xboole_0) | ~r1_tarski(A_498, A_500))), inference(resolution, [status(thm)], [c_2393, c_2498])).
% 5.86/2.10  tff(c_2545, plain, (![C_503]: (r1_xboole_0('#skF_7', C_503) | ~r1_tarski(C_503, k1_xboole_0))), inference(resolution, [status(thm)], [c_65, c_2511])).
% 5.86/2.10  tff(c_2625, plain, (![C_519, C_520]: (~r2_hidden(C_519, C_520) | ~r2_hidden(C_519, '#skF_7') | ~r1_tarski(C_520, k1_xboole_0))), inference(resolution, [status(thm)], [c_2545, c_2])).
% 5.86/2.10  tff(c_2631, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_2346, c_2625])).
% 5.86/2.10  tff(c_2640, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2346, c_2631])).
% 5.86/2.10  tff(c_2935, plain, (~r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2924, c_2640])).
% 5.86/2.10  tff(c_2955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_2935])).
% 5.86/2.10  tff(c_2956, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_2919])).
% 5.86/2.10  tff(c_2963, plain, (![A_565, A_566, B_567, C_568]: (r2_hidden(k1_mcart_1(A_565), k2_zfmisc_1(A_566, B_567)) | ~r2_hidden(A_565, k3_zfmisc_1(A_566, B_567, C_568)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2437])).
% 5.86/2.10  tff(c_2977, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_2963])).
% 5.86/2.10  tff(c_2983, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2977, c_22])).
% 5.86/2.10  tff(c_2992, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2956, c_2983])).
% 5.86/2.10  tff(c_2994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2345, c_2992])).
% 5.86/2.10  tff(c_2997, plain, (![B_569]: (r1_xboole_0('#skF_6', B_569))), inference(splitRight, [status(thm)], [c_2483])).
% 5.86/2.10  tff(c_3032, plain, (![C_579, B_580]: (~r2_hidden(C_579, B_580) | ~r2_hidden(C_579, '#skF_6'))), inference(resolution, [status(thm)], [c_2997, c_2])).
% 5.86/2.10  tff(c_3078, plain, (![A_591, B_592]: (~r2_hidden('#skF_1'(A_591, B_592), '#skF_6') | r1_xboole_0(A_591, B_592))), inference(resolution, [status(thm)], [c_6, c_3032])).
% 5.86/2.10  tff(c_3090, plain, (![A_593]: (r1_xboole_0(A_593, '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_3078])).
% 5.86/2.10  tff(c_3097, plain, (![C_5, A_593]: (~r2_hidden(C_5, '#skF_6') | ~r2_hidden(C_5, A_593))), inference(resolution, [status(thm)], [c_3090, c_2])).
% 5.86/2.10  tff(c_3846, plain, (![A_593]: (~r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), A_593))), inference(resolution, [status(thm)], [c_3816, c_3097])).
% 5.86/2.10  tff(c_3875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3846, c_3816])).
% 5.86/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.10  
% 5.86/2.10  Inference rules
% 5.86/2.10  ----------------------
% 5.86/2.10  #Ref     : 0
% 5.86/2.10  #Sup     : 908
% 5.86/2.10  #Fact    : 0
% 5.86/2.10  #Define  : 0
% 5.86/2.10  #Split   : 40
% 5.86/2.10  #Chain   : 0
% 5.86/2.10  #Close   : 0
% 5.86/2.10  
% 5.86/2.10  Ordering : KBO
% 5.86/2.10  
% 5.86/2.10  Simplification rules
% 5.86/2.10  ----------------------
% 5.86/2.10  #Subsume      : 290
% 5.86/2.10  #Demod        : 568
% 5.86/2.10  #Tautology    : 154
% 5.86/2.10  #SimpNegUnit  : 17
% 5.86/2.10  #BackRed      : 335
% 5.86/2.10  
% 5.86/2.10  #Partial instantiations: 0
% 5.86/2.10  #Strategies tried      : 1
% 5.86/2.10  
% 5.86/2.10  Timing (in seconds)
% 5.86/2.10  ----------------------
% 5.86/2.10  Preprocessing        : 0.32
% 5.86/2.10  Parsing              : 0.17
% 5.86/2.10  CNF conversion       : 0.02
% 5.86/2.10  Main loop            : 0.98
% 5.86/2.10  Inferencing          : 0.32
% 5.86/2.10  Reduction            : 0.30
% 5.86/2.10  Demodulation         : 0.21
% 5.86/2.10  BG Simplification    : 0.04
% 5.86/2.10  Subsumption          : 0.22
% 5.86/2.10  Abstraction          : 0.04
% 5.86/2.10  MUC search           : 0.00
% 5.86/2.10  Cooper               : 0.00
% 5.86/2.10  Total                : 1.37
% 5.86/2.10  Index Insertion      : 0.00
% 5.86/2.10  Index Deletion       : 0.00
% 5.86/2.10  Index Matching       : 0.00
% 5.86/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
