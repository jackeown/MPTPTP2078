%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:59 EST 2020

% Result     : Theorem 32.72s
% Output     : CNFRefutation 32.72s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 597 expanded)
%              Number of leaves         :   33 ( 224 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 (2257 expanded)
%              Number of equality atoms :   96 (1205 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = G ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k6_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(B_10,A_9)
      | ~ v1_xboole_0(B_10)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_481,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k7_mcart_1(A_112,B_113,C_114,D_115) = k2_mcart_1(D_115)
      | ~ m1_subset_1(D_115,k3_zfmisc_1(A_112,B_113,C_114))
      | k1_xboole_0 = C_114
      | k1_xboole_0 = B_113
      | k1_xboole_0 = A_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_509,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_481])).

tff(c_519,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_509])).

tff(c_26,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( m1_subset_1(k7_mcart_1(A_17,B_18,C_19,D_20),C_19)
      | ~ m1_subset_1(D_20,k3_zfmisc_1(A_17,B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_547,plain,
    ( m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_26])).

tff(c_551,plain,(
    m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_547])).

tff(c_1072,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k3_mcart_1(k5_mcart_1(A_154,B_155,C_156,D_157),k6_mcart_1(A_154,B_155,C_156,D_157),k7_mcart_1(A_154,B_155,C_156,D_157)) = D_157
      | ~ m1_subset_1(D_157,k3_zfmisc_1(A_154,B_155,C_156))
      | k1_xboole_0 = C_156
      | k1_xboole_0 = B_155
      | k1_xboole_0 = A_154 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1083,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_1072])).

tff(c_1087,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1083])).

tff(c_1088,plain,(
    k3_mcart_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_1087])).

tff(c_48,plain,(
    ! [G_45,F_41,H_47] :
      ( G_45 = '#skF_6'
      | k3_mcart_1(F_41,G_45,H_47) != '#skF_7'
      | ~ m1_subset_1(H_47,'#skF_5')
      | ~ m1_subset_1(G_45,'#skF_4')
      | ~ m1_subset_1(F_41,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1180,plain,
    ( k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = '#skF_6'
    | ~ m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5')
    | ~ m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4')
    | ~ m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_48])).

tff(c_1185,plain,
    ( k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = '#skF_6'
    | ~ m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4')
    | ~ m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_1180])).

tff(c_1186,plain,
    ( ~ m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4')
    | ~ m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1185])).

tff(c_1517,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1186])).

tff(c_1521,plain,
    ( ~ v1_xboole_0(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1517])).

tff(c_1522,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1521])).

tff(c_678,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k5_mcart_1(A_130,B_131,C_132,D_133) = k1_mcart_1(k1_mcart_1(D_133))
      | ~ m1_subset_1(D_133,k3_zfmisc_1(A_130,B_131,C_132))
      | k1_xboole_0 = C_132
      | k1_xboole_0 = B_131
      | k1_xboole_0 = A_130 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_706,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_678])).

tff(c_716,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_706])).

tff(c_86,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_90,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_96,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( r2_hidden(B_10,A_9)
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_184,plain,(
    ! [A_76,B_77,C_78] : k2_zfmisc_1(k2_zfmisc_1(A_76,B_77),C_78) = k3_zfmisc_1(A_76,B_77,C_78) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k1_mcart_1(A_21),B_22)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3204,plain,(
    ! [A_239,A_240,B_241,C_242] :
      ( r2_hidden(k1_mcart_1(A_239),k2_zfmisc_1(A_240,B_241))
      | ~ r2_hidden(A_239,k3_zfmisc_1(A_240,B_241,C_242)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_30])).

tff(c_74494,plain,(
    ! [B_1189,A_1190,B_1191,C_1192] :
      ( r2_hidden(k1_mcart_1(B_1189),k2_zfmisc_1(A_1190,B_1191))
      | ~ m1_subset_1(B_1189,k3_zfmisc_1(A_1190,B_1191,C_1192))
      | v1_xboole_0(k3_zfmisc_1(A_1190,B_1191,C_1192)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3204])).

tff(c_74616,plain,
    ( r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_74494])).

tff(c_74635,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_74616])).

tff(c_74639,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_74635,c_30])).

tff(c_74649,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_74639])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( m1_subset_1(B_10,A_9)
      | ~ r2_hidden(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_74680,plain,
    ( m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74649,c_14])).

tff(c_74687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1522,c_1517,c_74680])).

tff(c_74689,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1521])).

tff(c_74,plain,(
    ! [A_52] :
      ( r2_hidden('#skF_2'(A_52),A_52)
      | k1_xboole_0 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(A_52)
      | k1_xboole_0 = A_52 ) ),
    inference(resolution,[status(thm)],[c_74,c_2])).

tff(c_74702,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_74689,c_78])).

tff(c_74711,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_74702])).

tff(c_74712,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1186])).

tff(c_74717,plain,
    ( ~ v1_xboole_0(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_74712])).

tff(c_74722,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_74717])).

tff(c_853,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( k6_mcart_1(A_142,B_143,C_144,D_145) = k2_mcart_1(k1_mcart_1(D_145))
      | ~ m1_subset_1(D_145,k3_zfmisc_1(A_142,B_143,C_144))
      | k1_xboole_0 = C_144
      | k1_xboole_0 = B_143
      | k1_xboole_0 = A_142 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_884,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_853])).

tff(c_894,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_44,c_42,c_884])).

tff(c_24,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_136,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden(k1_mcart_1(A_70),B_71)
      | ~ r2_hidden(A_70,k2_zfmisc_1(B_71,C_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_78741,plain,(
    ! [B_1314,B_1315,C_1316] :
      ( r2_hidden(k1_mcart_1(B_1314),B_1315)
      | ~ m1_subset_1(B_1314,k2_zfmisc_1(B_1315,C_1316))
      | v1_xboole_0(k2_zfmisc_1(B_1315,C_1316)) ) ),
    inference(resolution,[status(thm)],[c_16,c_136])).

tff(c_78770,plain,(
    ! [B_1314,A_14,B_15,C_16] :
      ( r2_hidden(k1_mcart_1(B_1314),k2_zfmisc_1(A_14,B_15))
      | ~ m1_subset_1(B_1314,k3_zfmisc_1(A_14,B_15,C_16))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_78741])).

tff(c_150594,plain,(
    ! [B_2223,A_2224,B_2225,C_2226] :
      ( r2_hidden(k1_mcart_1(B_2223),k2_zfmisc_1(A_2224,B_2225))
      | ~ m1_subset_1(B_2223,k3_zfmisc_1(A_2224,B_2225,C_2226))
      | v1_xboole_0(k3_zfmisc_1(A_2224,B_2225,C_2226)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_78770])).

tff(c_150720,plain,
    ( r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_50,c_150594])).

tff(c_150739,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_150720])).

tff(c_28,plain,(
    ! [A_21,C_23,B_22] :
      ( r2_hidden(k2_mcart_1(A_21),C_23)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_150741,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_150739,c_28])).

tff(c_150751,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_150741])).

tff(c_150774,plain,
    ( m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_150751,c_14])).

tff(c_150781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74722,c_74712,c_150774])).

tff(c_150783,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_74717])).

tff(c_150815,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_150783,c_78])).

tff(c_150824,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_150815])).

tff(c_150825,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_150830,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_150825,c_78])).

tff(c_150837,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150830,c_46])).

tff(c_150836,plain,(
    '#skF_7' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150830,c_44])).

tff(c_150835,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150830,c_42])).

tff(c_150826,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_150831,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(A_52)
      | A_52 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150830,c_78])).

tff(c_150863,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_150826,c_150831])).

tff(c_150932,plain,(
    ! [A_2243,B_2244,C_2245] : k2_zfmisc_1(k2_zfmisc_1(A_2243,B_2244),C_2245) = k3_zfmisc_1(A_2243,B_2244,C_2245) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_150910,plain,(
    ! [B_8,A_7] :
      ( B_8 = '#skF_7'
      | A_7 = '#skF_7'
      | k2_zfmisc_1(A_7,B_8) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150830,c_150830,c_150830,c_8])).

tff(c_153984,plain,(
    ! [C_2413,A_2414,B_2415] :
      ( C_2413 = '#skF_7'
      | k2_zfmisc_1(A_2414,B_2415) = '#skF_7'
      | k3_zfmisc_1(A_2414,B_2415,C_2413) != '#skF_7' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150932,c_150910])).

tff(c_154026,plain,
    ( '#skF_7' = '#skF_5'
    | k2_zfmisc_1('#skF_3','#skF_4') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_150863,c_153984])).

tff(c_154045,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_150835,c_154026])).

tff(c_154092,plain,
    ( '#skF_7' = '#skF_4'
    | '#skF_7' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_154045,c_150910])).

tff(c_154112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_150837,c_150836,c_154092])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:30:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.72/24.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.72/24.02  
% 32.72/24.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.72/24.03  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 32.72/24.03  
% 32.72/24.03  %Foreground sorts:
% 32.72/24.03  
% 32.72/24.03  
% 32.72/24.03  %Background operators:
% 32.72/24.03  
% 32.72/24.03  
% 32.72/24.03  %Foreground operators:
% 32.72/24.03  tff('#skF_2', type, '#skF_2': $i > $i).
% 32.72/24.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.72/24.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 32.72/24.03  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 32.72/24.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 32.72/24.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 32.72/24.03  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 32.72/24.03  tff('#skF_7', type, '#skF_7': $i).
% 32.72/24.03  tff('#skF_5', type, '#skF_5': $i).
% 32.72/24.03  tff('#skF_6', type, '#skF_6': $i).
% 32.72/24.03  tff('#skF_3', type, '#skF_3': $i).
% 32.72/24.03  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 32.72/24.03  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 32.72/24.03  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 32.72/24.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.72/24.03  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 32.72/24.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 32.72/24.03  tff('#skF_4', type, '#skF_4': $i).
% 32.72/24.03  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 32.72/24.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.72/24.03  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 32.72/24.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 32.72/24.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 32.72/24.03  
% 32.72/24.04  tff(f_132, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 32.72/24.04  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 32.72/24.04  tff(f_108, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 32.72/24.04  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 32.72/24.04  tff(f_88, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 32.72/24.04  tff(f_62, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 32.72/24.04  tff(f_72, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 32.72/24.04  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 32.72/24.04  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 32.72/24.04  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 32.72/24.04  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_132])).
% 32.72/24.04  tff(c_18, plain, (![B_10, A_9]: (m1_subset_1(B_10, A_9) | ~v1_xboole_0(B_10) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 32.72/24.04  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_132])).
% 32.72/24.04  tff(c_40, plain, (k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_132])).
% 32.72/24.04  tff(c_50, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 32.72/24.04  tff(c_42, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_132])).
% 32.72/24.04  tff(c_481, plain, (![A_112, B_113, C_114, D_115]: (k7_mcart_1(A_112, B_113, C_114, D_115)=k2_mcart_1(D_115) | ~m1_subset_1(D_115, k3_zfmisc_1(A_112, B_113, C_114)) | k1_xboole_0=C_114 | k1_xboole_0=B_113 | k1_xboole_0=A_112)), inference(cnfTransformation, [status(thm)], [f_108])).
% 32.72/24.04  tff(c_509, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_50, c_481])).
% 32.72/24.04  tff(c_519, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_509])).
% 32.72/24.04  tff(c_26, plain, (![A_17, B_18, C_19, D_20]: (m1_subset_1(k7_mcart_1(A_17, B_18, C_19, D_20), C_19) | ~m1_subset_1(D_20, k3_zfmisc_1(A_17, B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 32.72/24.04  tff(c_547, plain, (m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5') | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_519, c_26])).
% 32.72/24.04  tff(c_551, plain, (m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_547])).
% 32.72/24.04  tff(c_1072, plain, (![A_154, B_155, C_156, D_157]: (k3_mcart_1(k5_mcart_1(A_154, B_155, C_156, D_157), k6_mcart_1(A_154, B_155, C_156, D_157), k7_mcart_1(A_154, B_155, C_156, D_157))=D_157 | ~m1_subset_1(D_157, k3_zfmisc_1(A_154, B_155, C_156)) | k1_xboole_0=C_156 | k1_xboole_0=B_155 | k1_xboole_0=A_154)), inference(cnfTransformation, [status(thm)], [f_88])).
% 32.72/24.04  tff(c_1083, plain, (k3_mcart_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')) | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_519, c_1072])).
% 32.72/24.04  tff(c_1087, plain, (k3_mcart_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1083])).
% 32.72/24.04  tff(c_1088, plain, (k3_mcart_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_1087])).
% 32.72/24.04  tff(c_48, plain, (![G_45, F_41, H_47]: (G_45='#skF_6' | k3_mcart_1(F_41, G_45, H_47)!='#skF_7' | ~m1_subset_1(H_47, '#skF_5') | ~m1_subset_1(G_45, '#skF_4') | ~m1_subset_1(F_41, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 32.72/24.04  tff(c_1180, plain, (k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')='#skF_6' | ~m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5') | ~m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1088, c_48])).
% 32.72/24.04  tff(c_1185, plain, (k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')='#skF_6' | ~m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_551, c_1180])).
% 32.72/24.04  tff(c_1186, plain, (~m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_1185])).
% 32.72/24.04  tff(c_1517, plain, (~m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1186])).
% 32.72/24.04  tff(c_1521, plain, (~v1_xboole_0(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1517])).
% 32.72/24.04  tff(c_1522, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1521])).
% 32.72/24.04  tff(c_678, plain, (![A_130, B_131, C_132, D_133]: (k5_mcart_1(A_130, B_131, C_132, D_133)=k1_mcart_1(k1_mcart_1(D_133)) | ~m1_subset_1(D_133, k3_zfmisc_1(A_130, B_131, C_132)) | k1_xboole_0=C_132 | k1_xboole_0=B_131 | k1_xboole_0=A_130)), inference(cnfTransformation, [status(thm)], [f_108])).
% 32.72/24.04  tff(c_706, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_50, c_678])).
% 32.72/24.04  tff(c_716, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_706])).
% 32.72/24.04  tff(c_86, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, A_59) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 32.72/24.04  tff(c_90, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_86])).
% 32.72/24.04  tff(c_96, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_90])).
% 32.72/24.04  tff(c_16, plain, (![B_10, A_9]: (r2_hidden(B_10, A_9) | ~m1_subset_1(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 32.72/24.04  tff(c_184, plain, (![A_76, B_77, C_78]: (k2_zfmisc_1(k2_zfmisc_1(A_76, B_77), C_78)=k3_zfmisc_1(A_76, B_77, C_78))), inference(cnfTransformation, [status(thm)], [f_62])).
% 32.72/24.04  tff(c_30, plain, (![A_21, B_22, C_23]: (r2_hidden(k1_mcart_1(A_21), B_22) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 32.72/24.04  tff(c_3204, plain, (![A_239, A_240, B_241, C_242]: (r2_hidden(k1_mcart_1(A_239), k2_zfmisc_1(A_240, B_241)) | ~r2_hidden(A_239, k3_zfmisc_1(A_240, B_241, C_242)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_30])).
% 32.72/24.04  tff(c_74494, plain, (![B_1189, A_1190, B_1191, C_1192]: (r2_hidden(k1_mcart_1(B_1189), k2_zfmisc_1(A_1190, B_1191)) | ~m1_subset_1(B_1189, k3_zfmisc_1(A_1190, B_1191, C_1192)) | v1_xboole_0(k3_zfmisc_1(A_1190, B_1191, C_1192)))), inference(resolution, [status(thm)], [c_16, c_3204])).
% 32.72/24.04  tff(c_74616, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_74494])).
% 32.72/24.04  tff(c_74635, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_96, c_74616])).
% 32.72/24.04  tff(c_74639, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')), '#skF_3')), inference(resolution, [status(thm)], [c_74635, c_30])).
% 32.72/24.04  tff(c_74649, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_716, c_74639])).
% 32.72/24.04  tff(c_14, plain, (![B_10, A_9]: (m1_subset_1(B_10, A_9) | ~r2_hidden(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 32.72/24.04  tff(c_74680, plain, (m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74649, c_14])).
% 32.72/24.04  tff(c_74687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1522, c_1517, c_74680])).
% 32.72/24.04  tff(c_74689, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1521])).
% 32.72/24.04  tff(c_74, plain, (![A_52]: (r2_hidden('#skF_2'(A_52), A_52) | k1_xboole_0=A_52)), inference(cnfTransformation, [status(thm)], [f_39])).
% 32.72/24.04  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 32.72/24.04  tff(c_78, plain, (![A_52]: (~v1_xboole_0(A_52) | k1_xboole_0=A_52)), inference(resolution, [status(thm)], [c_74, c_2])).
% 32.72/24.04  tff(c_74702, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_74689, c_78])).
% 32.72/24.04  tff(c_74711, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_74702])).
% 32.72/24.04  tff(c_74712, plain, (~m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(splitRight, [status(thm)], [c_1186])).
% 32.72/24.04  tff(c_74717, plain, (~v1_xboole_0(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_18, c_74712])).
% 32.72/24.04  tff(c_74722, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_74717])).
% 32.72/24.04  tff(c_853, plain, (![A_142, B_143, C_144, D_145]: (k6_mcart_1(A_142, B_143, C_144, D_145)=k2_mcart_1(k1_mcart_1(D_145)) | ~m1_subset_1(D_145, k3_zfmisc_1(A_142, B_143, C_144)) | k1_xboole_0=C_144 | k1_xboole_0=B_143 | k1_xboole_0=A_142)), inference(cnfTransformation, [status(thm)], [f_108])).
% 32.72/24.04  tff(c_884, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_50, c_853])).
% 32.72/24.04  tff(c_894, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_46, c_44, c_42, c_884])).
% 32.72/24.04  tff(c_24, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 32.72/24.04  tff(c_136, plain, (![A_70, B_71, C_72]: (r2_hidden(k1_mcart_1(A_70), B_71) | ~r2_hidden(A_70, k2_zfmisc_1(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 32.72/24.04  tff(c_78741, plain, (![B_1314, B_1315, C_1316]: (r2_hidden(k1_mcart_1(B_1314), B_1315) | ~m1_subset_1(B_1314, k2_zfmisc_1(B_1315, C_1316)) | v1_xboole_0(k2_zfmisc_1(B_1315, C_1316)))), inference(resolution, [status(thm)], [c_16, c_136])).
% 32.72/24.04  tff(c_78770, plain, (![B_1314, A_14, B_15, C_16]: (r2_hidden(k1_mcart_1(B_1314), k2_zfmisc_1(A_14, B_15)) | ~m1_subset_1(B_1314, k3_zfmisc_1(A_14, B_15, C_16)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_78741])).
% 32.72/24.04  tff(c_150594, plain, (![B_2223, A_2224, B_2225, C_2226]: (r2_hidden(k1_mcart_1(B_2223), k2_zfmisc_1(A_2224, B_2225)) | ~m1_subset_1(B_2223, k3_zfmisc_1(A_2224, B_2225, C_2226)) | v1_xboole_0(k3_zfmisc_1(A_2224, B_2225, C_2226)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_78770])).
% 32.72/24.04  tff(c_150720, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_50, c_150594])).
% 32.72/24.04  tff(c_150739, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_96, c_150720])).
% 32.72/24.04  tff(c_28, plain, (![A_21, C_23, B_22]: (r2_hidden(k2_mcart_1(A_21), C_23) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 32.72/24.04  tff(c_150741, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_4')), inference(resolution, [status(thm)], [c_150739, c_28])).
% 32.72/24.04  tff(c_150751, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_150741])).
% 32.72/24.04  tff(c_150774, plain, (m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_150751, c_14])).
% 32.72/24.04  tff(c_150781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74722, c_74712, c_150774])).
% 32.72/24.04  tff(c_150783, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_74717])).
% 32.72/24.04  tff(c_150815, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_150783, c_78])).
% 32.72/24.04  tff(c_150824, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_150815])).
% 32.72/24.04  tff(c_150825, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_90])).
% 32.72/24.04  tff(c_150830, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_150825, c_78])).
% 32.72/24.04  tff(c_150837, plain, ('#skF_7'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_150830, c_46])).
% 32.72/24.04  tff(c_150836, plain, ('#skF_7'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_150830, c_44])).
% 32.72/24.04  tff(c_150835, plain, ('#skF_7'!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_150830, c_42])).
% 32.72/24.04  tff(c_150826, plain, (v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_90])).
% 32.72/24.04  tff(c_150831, plain, (![A_52]: (~v1_xboole_0(A_52) | A_52='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_150830, c_78])).
% 32.72/24.04  tff(c_150863, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_150826, c_150831])).
% 32.72/24.04  tff(c_150932, plain, (![A_2243, B_2244, C_2245]: (k2_zfmisc_1(k2_zfmisc_1(A_2243, B_2244), C_2245)=k3_zfmisc_1(A_2243, B_2244, C_2245))), inference(cnfTransformation, [status(thm)], [f_62])).
% 32.72/24.04  tff(c_8, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 32.72/24.04  tff(c_150910, plain, (![B_8, A_7]: (B_8='#skF_7' | A_7='#skF_7' | k2_zfmisc_1(A_7, B_8)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_150830, c_150830, c_150830, c_8])).
% 32.72/24.04  tff(c_153984, plain, (![C_2413, A_2414, B_2415]: (C_2413='#skF_7' | k2_zfmisc_1(A_2414, B_2415)='#skF_7' | k3_zfmisc_1(A_2414, B_2415, C_2413)!='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_150932, c_150910])).
% 32.72/24.04  tff(c_154026, plain, ('#skF_7'='#skF_5' | k2_zfmisc_1('#skF_3', '#skF_4')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_150863, c_153984])).
% 32.72/24.04  tff(c_154045, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_150835, c_154026])).
% 32.72/24.04  tff(c_154092, plain, ('#skF_7'='#skF_4' | '#skF_7'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_154045, c_150910])).
% 32.72/24.04  tff(c_154112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_150837, c_150836, c_154092])).
% 32.72/24.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.72/24.04  
% 32.72/24.04  Inference rules
% 32.72/24.04  ----------------------
% 32.72/24.04  #Ref     : 0
% 32.72/24.04  #Sup     : 40101
% 32.72/24.04  #Fact    : 0
% 32.72/24.04  #Define  : 0
% 32.72/24.04  #Split   : 21
% 32.72/24.04  #Chain   : 0
% 32.72/24.04  #Close   : 0
% 32.72/24.04  
% 32.72/24.04  Ordering : KBO
% 32.72/24.04  
% 32.72/24.04  Simplification rules
% 32.72/24.04  ----------------------
% 32.72/24.04  #Subsume      : 7227
% 32.72/24.04  #Demod        : 40189
% 32.72/24.04  #Tautology    : 28478
% 32.72/24.04  #SimpNegUnit  : 286
% 32.72/24.04  #BackRed      : 13
% 32.72/24.04  
% 32.72/24.04  #Partial instantiations: 0
% 32.72/24.04  #Strategies tried      : 1
% 32.72/24.04  
% 32.72/24.04  Timing (in seconds)
% 32.72/24.04  ----------------------
% 32.72/24.05  Preprocessing        : 0.36
% 32.72/24.05  Parsing              : 0.19
% 32.72/24.05  CNF conversion       : 0.03
% 32.72/24.05  Main loop            : 22.85
% 32.72/24.05  Inferencing          : 4.80
% 32.72/24.05  Reduction            : 6.51
% 32.72/24.05  Demodulation         : 5.04
% 32.72/24.05  BG Simplification    : 0.29
% 32.72/24.05  Subsumption          : 10.75
% 32.72/24.05  Abstraction          : 0.66
% 32.72/24.05  MUC search           : 0.00
% 32.72/24.05  Cooper               : 0.00
% 32.72/24.05  Total                : 23.26
% 32.72/24.05  Index Insertion      : 0.00
% 32.72/24.05  Index Deletion       : 0.00
% 32.72/24.05  Index Matching       : 0.00
% 32.72/24.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
