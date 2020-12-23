%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:05 EST 2020

% Result     : Theorem 9.37s
% Output     : CNFRefutation 9.59s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 482 expanded)
%              Number of leaves         :   35 ( 180 expanded)
%              Depth                    :   15
%              Number of atoms          :  186 (1309 expanded)
%              Number of equality atoms :  105 ( 719 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_88,axiom,(
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

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_346,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k7_mcart_1(A_135,B_136,C_137,D_138) = k2_mcart_1(D_138)
      | ~ m1_subset_1(D_138,k3_zfmisc_1(A_135,B_136,C_137))
      | k1_xboole_0 = C_137
      | k1_xboole_0 = B_136
      | k1_xboole_0 = A_135 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_349,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_346])).

tff(c_352,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_349])).

tff(c_46,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_353,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_46])).

tff(c_40,plain,(
    ! [B_34,C_35,D_36] : k4_zfmisc_1(k1_xboole_0,B_34,C_35,D_36) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    ! [A_33,C_35,D_36] : k4_zfmisc_1(A_33,k1_xboole_0,C_35,D_36) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_168,plain,(
    ! [A_83,B_84,C_85] : k2_zfmisc_1(k2_zfmisc_1(A_83,B_84),C_85) = k3_zfmisc_1(A_83,B_84,C_85) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_178,plain,(
    ! [A_83,B_84,C_85] : v1_relat_1(k3_zfmisc_1(A_83,B_84,C_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_8])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_233,plain,(
    ! [A_104,B_105] :
      ( k4_tarski(k1_mcart_1(A_104),k2_mcart_1(A_104)) = A_104
      | ~ r2_hidden(A_104,B_105)
      | ~ v1_relat_1(B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7447,plain,(
    ! [A_5341,B_5342] :
      ( k4_tarski(k1_mcart_1(A_5341),k2_mcart_1(A_5341)) = A_5341
      | ~ v1_relat_1(B_5342)
      | v1_xboole_0(B_5342)
      | ~ m1_subset_1(A_5341,B_5342) ) ),
    inference(resolution,[status(thm)],[c_6,c_233])).

tff(c_7473,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_7447])).

tff(c_7490,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_7473])).

tff(c_7587,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7490])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7591,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7587,c_2])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_zfmisc_1(k3_zfmisc_1(A_14,B_15,C_16),D_17) = k4_zfmisc_1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7626,plain,(
    ! [D_5349] : k4_zfmisc_1('#skF_1','#skF_2','#skF_3',D_5349) = k2_zfmisc_1(k1_xboole_0,D_5349) ),
    inference(superposition,[status(thm),theory(equality)],[c_7591,c_14])).

tff(c_34,plain,(
    ! [A_33,B_34,C_35] : k4_zfmisc_1(A_33,B_34,C_35,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7640,plain,(
    k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7626,c_34])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13) = k3_zfmisc_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_181,plain,(
    ! [A_11,B_12,C_13,C_85] : k3_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13,C_85) = k2_zfmisc_1(k3_zfmisc_1(A_11,B_12,C_13),C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_168])).

tff(c_6997,plain,(
    ! [A_11,B_12,C_13,C_85] : k3_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13,C_85) = k4_zfmisc_1(A_11,B_12,C_13,C_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_181])).

tff(c_7657,plain,(
    ! [C_13,C_85] : k4_zfmisc_1(k1_xboole_0,k1_xboole_0,C_13,C_85) = k3_zfmisc_1(k1_xboole_0,C_13,C_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_7640,c_6997])).

tff(c_7740,plain,(
    ! [C_5353,C_5354] : k3_zfmisc_1(k1_xboole_0,C_5353,C_5354) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_7657])).

tff(c_7756,plain,(
    ! [C_5353,C_5354,D_17] : k4_zfmisc_1(k1_xboole_0,C_5353,C_5354,D_17) = k2_zfmisc_1(k1_xboole_0,D_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_7740,c_14])).

tff(c_7767,plain,(
    ! [D_17] : k2_zfmisc_1(k1_xboole_0,D_17) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7756])).

tff(c_32,plain,(
    ! [A_33,B_34,C_35,D_36] :
      ( k4_zfmisc_1(A_33,B_34,C_35,D_36) != k1_xboole_0
      | k1_xboole_0 = D_36
      | k1_xboole_0 = C_35
      | k1_xboole_0 = B_34
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_7634,plain,(
    ! [D_5349] :
      ( k2_zfmisc_1(k1_xboole_0,D_5349) != k1_xboole_0
      | k1_xboole_0 = D_5349
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7626,c_32])).

tff(c_7649,plain,(
    ! [D_5349] :
      ( k2_zfmisc_1(k1_xboole_0,D_5349) != k1_xboole_0
      | k1_xboole_0 = D_5349 ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_7634])).

tff(c_7815,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7767,c_7649])).

tff(c_7801,plain,(
    ! [D_5349] : k1_xboole_0 = D_5349 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7767,c_7649])).

tff(c_8796,plain,(
    ! [D_10795] : D_10795 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7815,c_7801])).

tff(c_7802,plain,(
    ! [D_5356] : k1_xboole_0 = D_5356 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7767,c_7649])).

tff(c_8135,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7802,c_353])).

tff(c_9190,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_8796,c_8135])).

tff(c_9192,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7490])).

tff(c_16,plain,(
    ! [A_18,C_20,B_19] :
      ( r2_hidden(k2_mcart_1(A_18),C_20)
      | ~ r2_hidden(A_18,k2_zfmisc_1(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_247,plain,(
    ! [A_112,C_113,A_114,B_115] :
      ( r2_hidden(k2_mcart_1(A_112),C_113)
      | ~ r2_hidden(A_112,k3_zfmisc_1(A_114,B_115,C_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_16])).

tff(c_11443,plain,(
    ! [A_13721,C_13722,A_13723,B_13724] :
      ( r2_hidden(k2_mcart_1(A_13721),C_13722)
      | v1_xboole_0(k3_zfmisc_1(A_13723,B_13724,C_13722))
      | ~ m1_subset_1(A_13721,k3_zfmisc_1(A_13723,B_13724,C_13722)) ) ),
    inference(resolution,[status(thm)],[c_6,c_247])).

tff(c_11517,plain,
    ( r2_hidden(k2_mcart_1('#skF_5'),'#skF_3')
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_11443])).

tff(c_11546,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_9192,c_11517])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_11553,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_11546,c_4])).

tff(c_9191,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_7490])).

tff(c_6428,plain,(
    ! [A_5215,B_5216,C_5217,D_5218] :
      ( k5_mcart_1(A_5215,B_5216,C_5217,D_5218) = k1_mcart_1(k1_mcart_1(D_5218))
      | ~ m1_subset_1(D_5218,k3_zfmisc_1(A_5215,B_5216,C_5217))
      | k1_xboole_0 = C_5217
      | k1_xboole_0 = B_5216
      | k1_xboole_0 = A_5215 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6435,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_6428])).

tff(c_6439,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_6435])).

tff(c_189,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden(k1_mcart_1(A_92),B_93)
      | ~ r2_hidden(A_92,k2_zfmisc_1(B_93,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6800,plain,(
    ! [A_5268,A_5269,B_5270,C_5271] :
      ( r2_hidden(k1_mcart_1(A_5268),k2_zfmisc_1(A_5269,B_5270))
      | ~ r2_hidden(A_5268,k3_zfmisc_1(A_5269,B_5270,C_5271)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_189])).

tff(c_12145,plain,(
    ! [A_13794,A_13795,B_13796,C_13797] :
      ( r2_hidden(k1_mcart_1(A_13794),k2_zfmisc_1(A_13795,B_13796))
      | v1_xboole_0(k3_zfmisc_1(A_13795,B_13796,C_13797))
      | ~ m1_subset_1(A_13794,k3_zfmisc_1(A_13795,B_13796,C_13797)) ) ),
    inference(resolution,[status(thm)],[c_6,c_6800])).

tff(c_12231,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_12145])).

tff(c_12264,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_9192,c_12231])).

tff(c_18,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden(k1_mcart_1(A_18),B_19)
      | ~ r2_hidden(A_18,k2_zfmisc_1(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12268,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12264,c_18])).

tff(c_12278,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6439,c_12268])).

tff(c_12301,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12278,c_4])).

tff(c_370,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( k6_mcart_1(A_141,B_142,C_143,D_144) = k2_mcart_1(k1_mcart_1(D_144))
      | ~ m1_subset_1(D_144,k3_zfmisc_1(A_141,B_142,C_143))
      | k1_xboole_0 = C_143
      | k1_xboole_0 = B_142
      | k1_xboole_0 = A_141 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_377,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_370])).

tff(c_381,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_377])).

tff(c_12270,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12264,c_16])).

tff(c_12280,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_12270])).

tff(c_12308,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12280,c_4])).

tff(c_24,plain,(
    ! [A_26,B_27] :
      ( k4_tarski(k1_mcart_1(A_26),k2_mcart_1(A_26)) = A_26
      | ~ r2_hidden(A_26,B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12266,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12264,c_24])).

tff(c_12276,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_381,c_6439,c_12266])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k4_tarski(k4_tarski(A_8,B_9),C_10) = k3_mcart_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12991,plain,(
    ! [C_13859] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_13859) = k4_tarski(k1_mcart_1('#skF_5'),C_13859) ),
    inference(superposition,[status(thm),theory(equality)],[c_12276,c_10])).

tff(c_54,plain,(
    ! [H_52,F_46,G_50] :
      ( H_52 = '#skF_4'
      | k3_mcart_1(F_46,G_50,H_52) != '#skF_5'
      | ~ m1_subset_1(H_52,'#skF_3')
      | ~ m1_subset_1(G_50,'#skF_2')
      | ~ m1_subset_1(F_46,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_13061,plain,(
    ! [C_13859] :
      ( C_13859 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_13859) != '#skF_5'
      | ~ m1_subset_1(C_13859,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12991,c_54])).

tff(c_13083,plain,(
    ! [C_13861] :
      ( C_13861 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_13861) != '#skF_5'
      | ~ m1_subset_1(C_13861,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12301,c_12308,c_13061])).

tff(c_13086,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9191,c_13083])).

tff(c_13089,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11553,c_13086])).

tff(c_13091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_13089])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:59:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.37/3.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.37/3.38  
% 9.37/3.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.37/3.39  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.37/3.39  
% 9.37/3.39  %Foreground sorts:
% 9.37/3.39  
% 9.37/3.39  
% 9.37/3.39  %Background operators:
% 9.37/3.39  
% 9.37/3.39  
% 9.37/3.39  %Foreground operators:
% 9.37/3.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.37/3.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.37/3.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.37/3.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.37/3.39  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 9.37/3.39  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 9.37/3.39  tff('#skF_5', type, '#skF_5': $i).
% 9.37/3.39  tff('#skF_2', type, '#skF_2': $i).
% 9.37/3.39  tff('#skF_3', type, '#skF_3': $i).
% 9.37/3.39  tff('#skF_1', type, '#skF_1': $i).
% 9.37/3.39  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 9.37/3.39  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 9.37/3.39  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 9.37/3.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.37/3.39  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 9.37/3.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.37/3.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.37/3.39  tff('#skF_4', type, '#skF_4': $i).
% 9.37/3.39  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 9.37/3.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.37/3.39  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 9.37/3.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.37/3.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.37/3.39  
% 9.59/3.40  tff(f_131, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 9.59/3.40  tff(f_88, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 9.59/3.40  tff(f_103, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 9.59/3.40  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 9.59/3.40  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.59/3.40  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 9.59/3.40  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 9.59/3.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.59/3.40  tff(f_47, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 9.59/3.40  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 9.59/3.41  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 9.59/3.41  tff(f_43, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 9.59/3.41  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.59/3.41  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.59/3.41  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.59/3.41  tff(c_56, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.59/3.41  tff(c_346, plain, (![A_135, B_136, C_137, D_138]: (k7_mcart_1(A_135, B_136, C_137, D_138)=k2_mcart_1(D_138) | ~m1_subset_1(D_138, k3_zfmisc_1(A_135, B_136, C_137)) | k1_xboole_0=C_137 | k1_xboole_0=B_136 | k1_xboole_0=A_135)), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.59/3.41  tff(c_349, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_56, c_346])).
% 9.59/3.41  tff(c_352, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_349])).
% 9.59/3.41  tff(c_46, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.59/3.41  tff(c_353, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_352, c_46])).
% 9.59/3.41  tff(c_40, plain, (![B_34, C_35, D_36]: (k4_zfmisc_1(k1_xboole_0, B_34, C_35, D_36)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.59/3.41  tff(c_38, plain, (![A_33, C_35, D_36]: (k4_zfmisc_1(A_33, k1_xboole_0, C_35, D_36)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.59/3.41  tff(c_168, plain, (![A_83, B_84, C_85]: (k2_zfmisc_1(k2_zfmisc_1(A_83, B_84), C_85)=k3_zfmisc_1(A_83, B_84, C_85))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.59/3.41  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.59/3.41  tff(c_178, plain, (![A_83, B_84, C_85]: (v1_relat_1(k3_zfmisc_1(A_83, B_84, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_8])).
% 9.59/3.41  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.59/3.41  tff(c_233, plain, (![A_104, B_105]: (k4_tarski(k1_mcart_1(A_104), k2_mcart_1(A_104))=A_104 | ~r2_hidden(A_104, B_105) | ~v1_relat_1(B_105))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.59/3.41  tff(c_7447, plain, (![A_5341, B_5342]: (k4_tarski(k1_mcart_1(A_5341), k2_mcart_1(A_5341))=A_5341 | ~v1_relat_1(B_5342) | v1_xboole_0(B_5342) | ~m1_subset_1(A_5341, B_5342))), inference(resolution, [status(thm)], [c_6, c_233])).
% 9.59/3.41  tff(c_7473, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_7447])).
% 9.59/3.41  tff(c_7490, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_7473])).
% 9.59/3.41  tff(c_7587, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_7490])).
% 9.59/3.41  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.59/3.41  tff(c_7591, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_7587, c_2])).
% 9.59/3.41  tff(c_14, plain, (![A_14, B_15, C_16, D_17]: (k2_zfmisc_1(k3_zfmisc_1(A_14, B_15, C_16), D_17)=k4_zfmisc_1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.59/3.41  tff(c_7626, plain, (![D_5349]: (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', D_5349)=k2_zfmisc_1(k1_xboole_0, D_5349))), inference(superposition, [status(thm), theory('equality')], [c_7591, c_14])).
% 9.59/3.41  tff(c_34, plain, (![A_33, B_34, C_35]: (k4_zfmisc_1(A_33, B_34, C_35, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.59/3.41  tff(c_7640, plain, (k2_zfmisc_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7626, c_34])).
% 9.59/3.41  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.59/3.41  tff(c_181, plain, (![A_11, B_12, C_13, C_85]: (k3_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13, C_85)=k2_zfmisc_1(k3_zfmisc_1(A_11, B_12, C_13), C_85))), inference(superposition, [status(thm), theory('equality')], [c_12, c_168])).
% 9.59/3.41  tff(c_6997, plain, (![A_11, B_12, C_13, C_85]: (k3_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13, C_85)=k4_zfmisc_1(A_11, B_12, C_13, C_85))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_181])).
% 9.59/3.41  tff(c_7657, plain, (![C_13, C_85]: (k4_zfmisc_1(k1_xboole_0, k1_xboole_0, C_13, C_85)=k3_zfmisc_1(k1_xboole_0, C_13, C_85))), inference(superposition, [status(thm), theory('equality')], [c_7640, c_6997])).
% 9.59/3.41  tff(c_7740, plain, (![C_5353, C_5354]: (k3_zfmisc_1(k1_xboole_0, C_5353, C_5354)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_7657])).
% 9.59/3.41  tff(c_7756, plain, (![C_5353, C_5354, D_17]: (k4_zfmisc_1(k1_xboole_0, C_5353, C_5354, D_17)=k2_zfmisc_1(k1_xboole_0, D_17))), inference(superposition, [status(thm), theory('equality')], [c_7740, c_14])).
% 9.59/3.41  tff(c_7767, plain, (![D_17]: (k2_zfmisc_1(k1_xboole_0, D_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7756])).
% 9.59/3.41  tff(c_32, plain, (![A_33, B_34, C_35, D_36]: (k4_zfmisc_1(A_33, B_34, C_35, D_36)!=k1_xboole_0 | k1_xboole_0=D_36 | k1_xboole_0=C_35 | k1_xboole_0=B_34 | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.59/3.41  tff(c_7634, plain, (![D_5349]: (k2_zfmisc_1(k1_xboole_0, D_5349)!=k1_xboole_0 | k1_xboole_0=D_5349 | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7626, c_32])).
% 9.59/3.41  tff(c_7649, plain, (![D_5349]: (k2_zfmisc_1(k1_xboole_0, D_5349)!=k1_xboole_0 | k1_xboole_0=D_5349)), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_7634])).
% 9.59/3.41  tff(c_7815, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7767, c_7649])).
% 9.59/3.41  tff(c_7801, plain, (![D_5349]: (k1_xboole_0=D_5349)), inference(demodulation, [status(thm), theory('equality')], [c_7767, c_7649])).
% 9.59/3.41  tff(c_8796, plain, (![D_10795]: (D_10795='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7815, c_7801])).
% 9.59/3.41  tff(c_7802, plain, (![D_5356]: (k1_xboole_0=D_5356)), inference(demodulation, [status(thm), theory('equality')], [c_7767, c_7649])).
% 9.59/3.41  tff(c_8135, plain, (k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_7802, c_353])).
% 9.59/3.41  tff(c_9190, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_8796, c_8135])).
% 9.59/3.41  tff(c_9192, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_7490])).
% 9.59/3.41  tff(c_16, plain, (![A_18, C_20, B_19]: (r2_hidden(k2_mcart_1(A_18), C_20) | ~r2_hidden(A_18, k2_zfmisc_1(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.59/3.41  tff(c_247, plain, (![A_112, C_113, A_114, B_115]: (r2_hidden(k2_mcart_1(A_112), C_113) | ~r2_hidden(A_112, k3_zfmisc_1(A_114, B_115, C_113)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_16])).
% 9.59/3.41  tff(c_11443, plain, (![A_13721, C_13722, A_13723, B_13724]: (r2_hidden(k2_mcart_1(A_13721), C_13722) | v1_xboole_0(k3_zfmisc_1(A_13723, B_13724, C_13722)) | ~m1_subset_1(A_13721, k3_zfmisc_1(A_13723, B_13724, C_13722)))), inference(resolution, [status(thm)], [c_6, c_247])).
% 9.59/3.41  tff(c_11517, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3') | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_11443])).
% 9.59/3.41  tff(c_11546, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_9192, c_11517])).
% 9.59/3.41  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.59/3.41  tff(c_11553, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_11546, c_4])).
% 9.59/3.41  tff(c_9191, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_7490])).
% 9.59/3.41  tff(c_6428, plain, (![A_5215, B_5216, C_5217, D_5218]: (k5_mcart_1(A_5215, B_5216, C_5217, D_5218)=k1_mcart_1(k1_mcart_1(D_5218)) | ~m1_subset_1(D_5218, k3_zfmisc_1(A_5215, B_5216, C_5217)) | k1_xboole_0=C_5217 | k1_xboole_0=B_5216 | k1_xboole_0=A_5215)), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.59/3.41  tff(c_6435, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_56, c_6428])).
% 9.59/3.41  tff(c_6439, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_6435])).
% 9.59/3.41  tff(c_189, plain, (![A_92, B_93, C_94]: (r2_hidden(k1_mcart_1(A_92), B_93) | ~r2_hidden(A_92, k2_zfmisc_1(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.59/3.41  tff(c_6800, plain, (![A_5268, A_5269, B_5270, C_5271]: (r2_hidden(k1_mcart_1(A_5268), k2_zfmisc_1(A_5269, B_5270)) | ~r2_hidden(A_5268, k3_zfmisc_1(A_5269, B_5270, C_5271)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_189])).
% 9.59/3.41  tff(c_12145, plain, (![A_13794, A_13795, B_13796, C_13797]: (r2_hidden(k1_mcart_1(A_13794), k2_zfmisc_1(A_13795, B_13796)) | v1_xboole_0(k3_zfmisc_1(A_13795, B_13796, C_13797)) | ~m1_subset_1(A_13794, k3_zfmisc_1(A_13795, B_13796, C_13797)))), inference(resolution, [status(thm)], [c_6, c_6800])).
% 9.59/3.41  tff(c_12231, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_12145])).
% 9.59/3.41  tff(c_12264, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_9192, c_12231])).
% 9.59/3.41  tff(c_18, plain, (![A_18, B_19, C_20]: (r2_hidden(k1_mcart_1(A_18), B_19) | ~r2_hidden(A_18, k2_zfmisc_1(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.59/3.41  tff(c_12268, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_12264, c_18])).
% 9.59/3.41  tff(c_12278, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6439, c_12268])).
% 9.59/3.41  tff(c_12301, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_12278, c_4])).
% 9.59/3.41  tff(c_370, plain, (![A_141, B_142, C_143, D_144]: (k6_mcart_1(A_141, B_142, C_143, D_144)=k2_mcart_1(k1_mcart_1(D_144)) | ~m1_subset_1(D_144, k3_zfmisc_1(A_141, B_142, C_143)) | k1_xboole_0=C_143 | k1_xboole_0=B_142 | k1_xboole_0=A_141)), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.59/3.41  tff(c_377, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_56, c_370])).
% 9.59/3.41  tff(c_381, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_377])).
% 9.59/3.41  tff(c_12270, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_12264, c_16])).
% 9.59/3.41  tff(c_12280, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_12270])).
% 9.59/3.41  tff(c_12308, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_12280, c_4])).
% 9.59/3.41  tff(c_24, plain, (![A_26, B_27]: (k4_tarski(k1_mcart_1(A_26), k2_mcart_1(A_26))=A_26 | ~r2_hidden(A_26, B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.59/3.41  tff(c_12266, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12264, c_24])).
% 9.59/3.41  tff(c_12276, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_381, c_6439, c_12266])).
% 9.59/3.41  tff(c_10, plain, (![A_8, B_9, C_10]: (k4_tarski(k4_tarski(A_8, B_9), C_10)=k3_mcart_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.59/3.41  tff(c_12991, plain, (![C_13859]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_13859)=k4_tarski(k1_mcart_1('#skF_5'), C_13859))), inference(superposition, [status(thm), theory('equality')], [c_12276, c_10])).
% 9.59/3.41  tff(c_54, plain, (![H_52, F_46, G_50]: (H_52='#skF_4' | k3_mcart_1(F_46, G_50, H_52)!='#skF_5' | ~m1_subset_1(H_52, '#skF_3') | ~m1_subset_1(G_50, '#skF_2') | ~m1_subset_1(F_46, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.59/3.41  tff(c_13061, plain, (![C_13859]: (C_13859='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_13859)!='#skF_5' | ~m1_subset_1(C_13859, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12991, c_54])).
% 9.59/3.41  tff(c_13083, plain, (![C_13861]: (C_13861='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_13861)!='#skF_5' | ~m1_subset_1(C_13861, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12301, c_12308, c_13061])).
% 9.59/3.41  tff(c_13086, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9191, c_13083])).
% 9.59/3.41  tff(c_13089, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11553, c_13086])).
% 9.59/3.41  tff(c_13091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_13089])).
% 9.59/3.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.59/3.41  
% 9.59/3.41  Inference rules
% 9.59/3.41  ----------------------
% 9.59/3.41  #Ref     : 0
% 9.59/3.41  #Sup     : 3979
% 9.59/3.41  #Fact    : 0
% 9.59/3.41  #Define  : 0
% 9.59/3.41  #Split   : 8
% 9.59/3.41  #Chain   : 0
% 9.59/3.41  #Close   : 0
% 9.59/3.41  
% 9.59/3.41  Ordering : KBO
% 9.59/3.41  
% 9.59/3.41  Simplification rules
% 9.59/3.41  ----------------------
% 9.59/3.41  #Subsume      : 1034
% 9.59/3.41  #Demod        : 954
% 9.59/3.41  #Tautology    : 563
% 9.59/3.41  #SimpNegUnit  : 28
% 9.59/3.41  #BackRed      : 11
% 9.59/3.41  
% 9.59/3.41  #Partial instantiations: 1611
% 9.59/3.41  #Strategies tried      : 1
% 9.59/3.41  
% 9.59/3.41  Timing (in seconds)
% 9.59/3.41  ----------------------
% 9.59/3.41  Preprocessing        : 0.34
% 9.59/3.41  Parsing              : 0.18
% 9.59/3.41  CNF conversion       : 0.02
% 9.59/3.41  Main loop            : 2.25
% 9.59/3.41  Inferencing          : 0.72
% 9.59/3.41  Reduction            : 0.69
% 9.59/3.41  Demodulation         : 0.46
% 9.59/3.41  BG Simplification    : 0.08
% 9.59/3.41  Subsumption          : 0.58
% 9.59/3.41  Abstraction          : 0.11
% 9.59/3.41  MUC search           : 0.00
% 9.59/3.41  Cooper               : 0.00
% 9.59/3.41  Total                : 2.63
% 9.59/3.41  Index Insertion      : 0.00
% 9.59/3.41  Index Deletion       : 0.00
% 9.59/3.41  Index Matching       : 0.00
% 9.59/3.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
