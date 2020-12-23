%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:57 EST 2020

% Result     : Theorem 27.06s
% Output     : CNFRefutation 27.06s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 564 expanded)
%              Number of leaves         :   32 ( 213 expanded)
%              Depth                    :   14
%              Number of atoms          :  205 (2176 expanded)
%              Number of equality atoms :   93 (1172 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = F ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k5_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_115,axiom,(
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

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(B_8,A_7)
      | ~ v1_xboole_0(B_8)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_337,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k7_mcart_1(A_102,B_103,C_104,D_105) = k2_mcart_1(D_105)
      | ~ m1_subset_1(D_105,k3_zfmisc_1(A_102,B_103,C_104))
      | k1_xboole_0 = C_104
      | k1_xboole_0 = B_103
      | k1_xboole_0 = A_102 ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_352,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') = k2_mcart_1('#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_337])).

tff(c_367,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') = k2_mcart_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_352])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( m1_subset_1(k7_mcart_1(A_15,B_16,C_17,D_18),C_17)
      | ~ m1_subset_1(D_18,k3_zfmisc_1(A_15,B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_430,plain,
    ( m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_6',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_22])).

tff(c_434,plain,(
    m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_430])).

tff(c_768,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k3_mcart_1(k5_mcart_1(A_143,B_144,C_145,D_146),k6_mcart_1(A_143,B_144,C_145,D_146),k7_mcart_1(A_143,B_144,C_145,D_146)) = D_146
      | ~ m1_subset_1(D_146,k3_zfmisc_1(A_143,B_144,C_145))
      | k1_xboole_0 = C_145
      | k1_xboole_0 = B_144
      | k1_xboole_0 = A_143 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_779,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k3_zfmisc_1('#skF_2','#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_768])).

tff(c_783,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_779])).

tff(c_784,plain,(
    k3_mcart_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_783])).

tff(c_52,plain,(
    ! [F_42,G_46,H_48] :
      ( F_42 = '#skF_5'
      | k3_mcart_1(F_42,G_46,H_48) != '#skF_6'
      | ~ m1_subset_1(H_48,'#skF_4')
      | ~ m1_subset_1(G_46,'#skF_3')
      | ~ m1_subset_1(F_42,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_787,plain,
    ( k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') = '#skF_5'
    | ~ m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4')
    | ~ m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3')
    | ~ m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_52])).

tff(c_792,plain,
    ( k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') = '#skF_5'
    | ~ m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3')
    | ~ m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_787])).

tff(c_793,plain,
    ( ~ m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3')
    | ~ m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_792])).

tff(c_1088,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_793])).

tff(c_1092,plain,
    ( ~ v1_xboole_0(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1088])).

tff(c_1215,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1092])).

tff(c_529,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k5_mcart_1(A_124,B_125,C_126,D_127) = k1_mcart_1(k1_mcart_1(D_127))
      | ~ m1_subset_1(D_127,k3_zfmisc_1(A_124,B_125,C_126))
      | k1_xboole_0 = C_126
      | k1_xboole_0 = B_125
      | k1_xboole_0 = A_124 ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_544,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_6')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_529])).

tff(c_559,plain,(
    k1_mcart_1(k1_mcart_1('#skF_6')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_544])).

tff(c_116,plain,(
    ! [B_61,A_62] :
      ( v1_xboole_0(B_61)
      | ~ m1_subset_1(B_61,A_62)
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_116])).

tff(c_136,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14] : k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k3_zfmisc_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( r2_hidden(B_8,A_7)
      | ~ m1_subset_1(B_8,A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden(k1_mcart_1(A_76),B_77)
      | ~ r2_hidden(A_76,k2_zfmisc_1(B_77,C_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4941,plain,(
    ! [B_328,B_329,C_330] :
      ( r2_hidden(k1_mcart_1(B_328),B_329)
      | ~ m1_subset_1(B_328,k2_zfmisc_1(B_329,C_330))
      | v1_xboole_0(k2_zfmisc_1(B_329,C_330)) ) ),
    inference(resolution,[status(thm)],[c_12,c_162])).

tff(c_4970,plain,(
    ! [B_328,A_12,B_13,C_14] :
      ( r2_hidden(k1_mcart_1(B_328),k2_zfmisc_1(A_12,B_13))
      | ~ m1_subset_1(B_328,k3_zfmisc_1(A_12,B_13,C_14))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4941])).

tff(c_48201,plain,(
    ! [B_1149,A_1150,B_1151,C_1152] :
      ( r2_hidden(k1_mcart_1(B_1149),k2_zfmisc_1(A_1150,B_1151))
      | ~ m1_subset_1(B_1149,k3_zfmisc_1(A_1150,B_1151,C_1152))
      | v1_xboole_0(k3_zfmisc_1(A_1150,B_1151,C_1152)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4970])).

tff(c_48274,plain,
    ( r2_hidden(k1_mcart_1('#skF_6'),k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_48201])).

tff(c_48289,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_48274])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(k1_mcart_1(A_19),B_20)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48298,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_6')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_48289,c_26])).

tff(c_48308,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_48298])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(B_8,A_7)
      | ~ r2_hidden(B_8,A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48339,plain,
    ( m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_48308,c_10])).

tff(c_48346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1215,c_1088,c_48339])).

tff(c_48348,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1092])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [B_58,A_59] :
      ( ~ v1_xboole_0(B_58)
      | B_58 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_109,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_48369,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48348,c_109])).

tff(c_48384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48369])).

tff(c_48385,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_793])).

tff(c_48390,plain,
    ( ~ v1_xboole_0(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_48385])).

tff(c_48637,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48390])).

tff(c_470,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k6_mcart_1(A_114,B_115,C_116,D_117) = k2_mcart_1(k1_mcart_1(D_117))
      | ~ m1_subset_1(D_117,k3_zfmisc_1(A_114,B_115,C_116))
      | k1_xboole_0 = C_116
      | k1_xboole_0 = B_115
      | k1_xboole_0 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_485,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_6')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_470])).

tff(c_500,plain,(
    k2_mcart_1(k1_mcart_1('#skF_6')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_485])).

tff(c_180,plain,(
    ! [A_82,B_83,C_84] : k2_zfmisc_1(k2_zfmisc_1(A_82,B_83),C_84) = k3_zfmisc_1(A_82,B_83,C_84) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49414,plain,(
    ! [A_1204,A_1205,B_1206,C_1207] :
      ( r2_hidden(k1_mcart_1(A_1204),k2_zfmisc_1(A_1205,B_1206))
      | ~ r2_hidden(A_1204,k3_zfmisc_1(A_1205,B_1206,C_1207)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_26])).

tff(c_94935,plain,(
    ! [B_2110,A_2111,B_2112,C_2113] :
      ( r2_hidden(k1_mcart_1(B_2110),k2_zfmisc_1(A_2111,B_2112))
      | ~ m1_subset_1(B_2110,k3_zfmisc_1(A_2111,B_2112,C_2113))
      | v1_xboole_0(k3_zfmisc_1(A_2111,B_2112,C_2113)) ) ),
    inference(resolution,[status(thm)],[c_12,c_49414])).

tff(c_95008,plain,
    ( r2_hidden(k1_mcart_1('#skF_6'),k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_94935])).

tff(c_95023,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_95008])).

tff(c_24,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(k2_mcart_1(A_19),C_21)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_95030,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_6')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_95023,c_24])).

tff(c_95040,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_500,c_95030])).

tff(c_95063,plain,
    ( m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_95040,c_10])).

tff(c_95070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48637,c_48385,c_95063])).

tff(c_95072,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_48390])).

tff(c_95098,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_95072,c_109])).

tff(c_95113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_95098])).

tff(c_95114,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_95121,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_95114,c_109])).

tff(c_95130,plain,(
    '#skF_6' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95121,c_50])).

tff(c_95129,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95121,c_48])).

tff(c_95128,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95121,c_46])).

tff(c_95115,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_95123,plain,(
    ! [A_59] :
      ( A_59 = '#skF_6'
      | ~ v1_xboole_0(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95121,c_109])).

tff(c_95157,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_95115,c_95123])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24] :
      ( k3_zfmisc_1(A_22,B_23,C_24) != k1_xboole_0
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_95323,plain,(
    ! [A_2148,B_2149,C_2150] :
      ( k3_zfmisc_1(A_2148,B_2149,C_2150) != '#skF_6'
      | C_2150 = '#skF_6'
      | B_2149 = '#skF_6'
      | A_2148 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95121,c_95121,c_95121,c_95121,c_28])).

tff(c_95326,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_95157,c_95323])).

tff(c_95339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95130,c_95129,c_95128,c_95326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.06/19.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.06/19.13  
% 27.06/19.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.06/19.14  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 27.06/19.14  
% 27.06/19.14  %Foreground sorts:
% 27.06/19.14  
% 27.06/19.14  
% 27.06/19.14  %Background operators:
% 27.06/19.14  
% 27.06/19.14  
% 27.06/19.14  %Foreground operators:
% 27.06/19.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.06/19.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.06/19.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 27.06/19.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 27.06/19.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.06/19.14  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 27.06/19.14  tff('#skF_5', type, '#skF_5': $i).
% 27.06/19.14  tff('#skF_6', type, '#skF_6': $i).
% 27.06/19.14  tff('#skF_2', type, '#skF_2': $i).
% 27.06/19.14  tff('#skF_3', type, '#skF_3': $i).
% 27.06/19.14  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 27.06/19.14  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 27.06/19.14  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 27.06/19.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.06/19.14  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 27.06/19.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.06/19.14  tff('#skF_4', type, '#skF_4': $i).
% 27.06/19.14  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 27.06/19.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.06/19.14  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 27.06/19.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 27.06/19.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.06/19.14  
% 27.06/19.15  tff(f_139, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = F)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k5_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 27.06/19.15  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 27.06/19.15  tff(f_115, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 27.06/19.15  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 27.06/19.15  tff(f_95, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 27.06/19.15  tff(f_57, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 27.06/19.15  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 27.06/19.15  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 27.06/19.15  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 27.06/19.15  tff(f_79, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 27.06/19.15  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.06/19.15  tff(c_14, plain, (![B_8, A_7]: (m1_subset_1(B_8, A_7) | ~v1_xboole_0(B_8) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.06/19.15  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.06/19.15  tff(c_44, plain, (k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.06/19.15  tff(c_54, plain, (m1_subset_1('#skF_6', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.06/19.15  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.06/19.15  tff(c_337, plain, (![A_102, B_103, C_104, D_105]: (k7_mcart_1(A_102, B_103, C_104, D_105)=k2_mcart_1(D_105) | ~m1_subset_1(D_105, k3_zfmisc_1(A_102, B_103, C_104)) | k1_xboole_0=C_104 | k1_xboole_0=B_103 | k1_xboole_0=A_102)), inference(cnfTransformation, [status(thm)], [f_115])).
% 27.06/19.15  tff(c_352, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_mcart_1('#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_54, c_337])).
% 27.06/19.15  tff(c_367, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_mcart_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_46, c_352])).
% 27.06/19.15  tff(c_22, plain, (![A_15, B_16, C_17, D_18]: (m1_subset_1(k7_mcart_1(A_15, B_16, C_17, D_18), C_17) | ~m1_subset_1(D_18, k3_zfmisc_1(A_15, B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 27.06/19.15  tff(c_430, plain, (m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4') | ~m1_subset_1('#skF_6', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_367, c_22])).
% 27.06/19.15  tff(c_434, plain, (m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_430])).
% 27.06/19.15  tff(c_768, plain, (![A_143, B_144, C_145, D_146]: (k3_mcart_1(k5_mcart_1(A_143, B_144, C_145, D_146), k6_mcart_1(A_143, B_144, C_145, D_146), k7_mcart_1(A_143, B_144, C_145, D_146))=D_146 | ~m1_subset_1(D_146, k3_zfmisc_1(A_143, B_144, C_145)) | k1_xboole_0=C_145 | k1_xboole_0=B_144 | k1_xboole_0=A_143)), inference(cnfTransformation, [status(thm)], [f_95])).
% 27.06/19.15  tff(c_779, plain, (k3_mcart_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')) | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_367, c_768])).
% 27.06/19.15  tff(c_783, plain, (k3_mcart_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_779])).
% 27.06/19.15  tff(c_784, plain, (k3_mcart_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), k2_mcart_1('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_46, c_783])).
% 27.06/19.15  tff(c_52, plain, (![F_42, G_46, H_48]: (F_42='#skF_5' | k3_mcart_1(F_42, G_46, H_48)!='#skF_6' | ~m1_subset_1(H_48, '#skF_4') | ~m1_subset_1(G_46, '#skF_3') | ~m1_subset_1(F_42, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.06/19.15  tff(c_787, plain, (k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')='#skF_5' | ~m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4') | ~m1_subset_1(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_784, c_52])).
% 27.06/19.15  tff(c_792, plain, (k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')='#skF_5' | ~m1_subset_1(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_434, c_787])).
% 27.06/19.15  tff(c_793, plain, (~m1_subset_1(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_792])).
% 27.06/19.15  tff(c_1088, plain, (~m1_subset_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(splitLeft, [status(thm)], [c_793])).
% 27.06/19.15  tff(c_1092, plain, (~v1_xboole_0(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_1088])).
% 27.06/19.15  tff(c_1215, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1092])).
% 27.06/19.15  tff(c_529, plain, (![A_124, B_125, C_126, D_127]: (k5_mcart_1(A_124, B_125, C_126, D_127)=k1_mcart_1(k1_mcart_1(D_127)) | ~m1_subset_1(D_127, k3_zfmisc_1(A_124, B_125, C_126)) | k1_xboole_0=C_126 | k1_xboole_0=B_125 | k1_xboole_0=A_124)), inference(cnfTransformation, [status(thm)], [f_115])).
% 27.06/19.15  tff(c_544, plain, (k1_mcart_1(k1_mcart_1('#skF_6'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_54, c_529])).
% 27.06/19.15  tff(c_559, plain, (k1_mcart_1(k1_mcart_1('#skF_6'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_46, c_544])).
% 27.06/19.15  tff(c_116, plain, (![B_61, A_62]: (v1_xboole_0(B_61) | ~m1_subset_1(B_61, A_62) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.06/19.15  tff(c_120, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_116])).
% 27.06/19.15  tff(c_136, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_120])).
% 27.06/19.15  tff(c_20, plain, (![A_12, B_13, C_14]: (k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k3_zfmisc_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.06/19.15  tff(c_12, plain, (![B_8, A_7]: (r2_hidden(B_8, A_7) | ~m1_subset_1(B_8, A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.06/19.15  tff(c_162, plain, (![A_76, B_77, C_78]: (r2_hidden(k1_mcart_1(A_76), B_77) | ~r2_hidden(A_76, k2_zfmisc_1(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 27.06/19.15  tff(c_4941, plain, (![B_328, B_329, C_330]: (r2_hidden(k1_mcart_1(B_328), B_329) | ~m1_subset_1(B_328, k2_zfmisc_1(B_329, C_330)) | v1_xboole_0(k2_zfmisc_1(B_329, C_330)))), inference(resolution, [status(thm)], [c_12, c_162])).
% 27.06/19.15  tff(c_4970, plain, (![B_328, A_12, B_13, C_14]: (r2_hidden(k1_mcart_1(B_328), k2_zfmisc_1(A_12, B_13)) | ~m1_subset_1(B_328, k3_zfmisc_1(A_12, B_13, C_14)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4941])).
% 27.06/19.15  tff(c_48201, plain, (![B_1149, A_1150, B_1151, C_1152]: (r2_hidden(k1_mcart_1(B_1149), k2_zfmisc_1(A_1150, B_1151)) | ~m1_subset_1(B_1149, k3_zfmisc_1(A_1150, B_1151, C_1152)) | v1_xboole_0(k3_zfmisc_1(A_1150, B_1151, C_1152)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4970])).
% 27.06/19.15  tff(c_48274, plain, (r2_hidden(k1_mcart_1('#skF_6'), k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_48201])).
% 27.06/19.15  tff(c_48289, plain, (r2_hidden(k1_mcart_1('#skF_6'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_136, c_48274])).
% 27.06/19.15  tff(c_26, plain, (![A_19, B_20, C_21]: (r2_hidden(k1_mcart_1(A_19), B_20) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 27.06/19.15  tff(c_48298, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_6')), '#skF_2')), inference(resolution, [status(thm)], [c_48289, c_26])).
% 27.06/19.15  tff(c_48308, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_48298])).
% 27.06/19.15  tff(c_10, plain, (![B_8, A_7]: (m1_subset_1(B_8, A_7) | ~r2_hidden(B_8, A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.06/19.15  tff(c_48339, plain, (m1_subset_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_48308, c_10])).
% 27.06/19.15  tff(c_48346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1215, c_1088, c_48339])).
% 27.06/19.15  tff(c_48348, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_1092])).
% 27.06/19.15  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.06/19.15  tff(c_106, plain, (![B_58, A_59]: (~v1_xboole_0(B_58) | B_58=A_59 | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_40])).
% 27.06/19.15  tff(c_109, plain, (![A_59]: (k1_xboole_0=A_59 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_6, c_106])).
% 27.06/19.15  tff(c_48369, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_48348, c_109])).
% 27.06/19.15  tff(c_48384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_48369])).
% 27.06/19.15  tff(c_48385, plain, (~m1_subset_1(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(splitRight, [status(thm)], [c_793])).
% 27.06/19.15  tff(c_48390, plain, (~v1_xboole_0(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_48385])).
% 27.06/19.15  tff(c_48637, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_48390])).
% 27.06/19.15  tff(c_470, plain, (![A_114, B_115, C_116, D_117]: (k6_mcart_1(A_114, B_115, C_116, D_117)=k2_mcart_1(k1_mcart_1(D_117)) | ~m1_subset_1(D_117, k3_zfmisc_1(A_114, B_115, C_116)) | k1_xboole_0=C_116 | k1_xboole_0=B_115 | k1_xboole_0=A_114)), inference(cnfTransformation, [status(thm)], [f_115])).
% 27.06/19.15  tff(c_485, plain, (k2_mcart_1(k1_mcart_1('#skF_6'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_54, c_470])).
% 27.06/19.15  tff(c_500, plain, (k2_mcart_1(k1_mcart_1('#skF_6'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_46, c_485])).
% 27.06/19.15  tff(c_180, plain, (![A_82, B_83, C_84]: (k2_zfmisc_1(k2_zfmisc_1(A_82, B_83), C_84)=k3_zfmisc_1(A_82, B_83, C_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 27.06/19.15  tff(c_49414, plain, (![A_1204, A_1205, B_1206, C_1207]: (r2_hidden(k1_mcart_1(A_1204), k2_zfmisc_1(A_1205, B_1206)) | ~r2_hidden(A_1204, k3_zfmisc_1(A_1205, B_1206, C_1207)))), inference(superposition, [status(thm), theory('equality')], [c_180, c_26])).
% 27.06/19.15  tff(c_94935, plain, (![B_2110, A_2111, B_2112, C_2113]: (r2_hidden(k1_mcart_1(B_2110), k2_zfmisc_1(A_2111, B_2112)) | ~m1_subset_1(B_2110, k3_zfmisc_1(A_2111, B_2112, C_2113)) | v1_xboole_0(k3_zfmisc_1(A_2111, B_2112, C_2113)))), inference(resolution, [status(thm)], [c_12, c_49414])).
% 27.06/19.15  tff(c_95008, plain, (r2_hidden(k1_mcart_1('#skF_6'), k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_94935])).
% 27.06/19.15  tff(c_95023, plain, (r2_hidden(k1_mcart_1('#skF_6'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_136, c_95008])).
% 27.06/19.15  tff(c_24, plain, (![A_19, C_21, B_20]: (r2_hidden(k2_mcart_1(A_19), C_21) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 27.06/19.15  tff(c_95030, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_6')), '#skF_3')), inference(resolution, [status(thm)], [c_95023, c_24])).
% 27.06/19.15  tff(c_95040, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_500, c_95030])).
% 27.06/19.15  tff(c_95063, plain, (m1_subset_1(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_95040, c_10])).
% 27.06/19.15  tff(c_95070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48637, c_48385, c_95063])).
% 27.06/19.15  tff(c_95072, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_48390])).
% 27.06/19.15  tff(c_95098, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_95072, c_109])).
% 27.06/19.15  tff(c_95113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_95098])).
% 27.06/19.15  tff(c_95114, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_120])).
% 27.06/19.15  tff(c_95121, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_95114, c_109])).
% 27.06/19.15  tff(c_95130, plain, ('#skF_6'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_95121, c_50])).
% 27.06/19.15  tff(c_95129, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_95121, c_48])).
% 27.06/19.15  tff(c_95128, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_95121, c_46])).
% 27.06/19.15  tff(c_95115, plain, (v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_120])).
% 27.06/19.15  tff(c_95123, plain, (![A_59]: (A_59='#skF_6' | ~v1_xboole_0(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_95121, c_109])).
% 27.06/19.15  tff(c_95157, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_95115, c_95123])).
% 27.06/19.15  tff(c_28, plain, (![A_22, B_23, C_24]: (k3_zfmisc_1(A_22, B_23, C_24)!=k1_xboole_0 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_79])).
% 27.06/19.15  tff(c_95323, plain, (![A_2148, B_2149, C_2150]: (k3_zfmisc_1(A_2148, B_2149, C_2150)!='#skF_6' | C_2150='#skF_6' | B_2149='#skF_6' | A_2148='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_95121, c_95121, c_95121, c_95121, c_28])).
% 27.06/19.15  tff(c_95326, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3' | '#skF_6'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_95157, c_95323])).
% 27.06/19.15  tff(c_95339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95130, c_95129, c_95128, c_95326])).
% 27.06/19.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.06/19.15  
% 27.06/19.15  Inference rules
% 27.06/19.15  ----------------------
% 27.06/19.15  #Ref     : 0
% 27.06/19.15  #Sup     : 26343
% 27.06/19.15  #Fact    : 0
% 27.06/19.15  #Define  : 0
% 27.06/19.15  #Split   : 11
% 27.06/19.15  #Chain   : 0
% 27.06/19.15  #Close   : 0
% 27.06/19.15  
% 27.06/19.15  Ordering : KBO
% 27.06/19.15  
% 27.06/19.15  Simplification rules
% 27.06/19.15  ----------------------
% 27.06/19.15  #Subsume      : 4274
% 27.06/19.15  #Demod        : 25773
% 27.06/19.15  #Tautology    : 15479
% 27.06/19.15  #SimpNegUnit  : 138
% 27.06/19.15  #BackRed      : 11
% 27.06/19.15  
% 27.06/19.15  #Partial instantiations: 0
% 27.06/19.15  #Strategies tried      : 1
% 27.06/19.15  
% 27.06/19.15  Timing (in seconds)
% 27.06/19.15  ----------------------
% 27.06/19.16  Preprocessing        : 0.33
% 27.06/19.16  Parsing              : 0.17
% 27.06/19.16  CNF conversion       : 0.02
% 27.06/19.16  Main loop            : 18.05
% 27.06/19.16  Inferencing          : 2.30
% 27.06/19.16  Reduction            : 5.09
% 27.06/19.16  Demodulation         : 3.89
% 27.06/19.16  BG Simplification    : 0.25
% 27.06/19.16  Subsumption          : 9.96
% 27.06/19.16  Abstraction          : 0.58
% 27.06/19.16  MUC search           : 0.00
% 27.06/19.16  Cooper               : 0.00
% 27.06/19.16  Total                : 18.42
% 27.06/19.16  Index Insertion      : 0.00
% 27.06/19.16  Index Deletion       : 0.00
% 27.06/19.16  Index Matching       : 0.00
% 27.06/19.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
