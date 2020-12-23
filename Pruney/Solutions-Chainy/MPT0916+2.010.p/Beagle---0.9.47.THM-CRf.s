%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:11 EST 2020

% Result     : Theorem 8.17s
% Output     : CNFRefutation 8.41s
% Verified   : 
% Statistics : Number of formulae       :  234 ( 699 expanded)
%              Number of leaves         :   39 ( 241 expanded)
%              Depth                    :   12
%              Number of atoms          :  376 (1850 expanded)
%              Number of equality atoms :  104 ( 474 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_51,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_90,axiom,(
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

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_28,plain,(
    ! [A_16] : ~ v1_xboole_0(k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_108,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_112,plain,(
    ! [A_58,A_11] :
      ( r1_tarski(A_58,A_11)
      | v1_xboole_0(k1_zfmisc_1(A_11))
      | ~ m1_subset_1(A_58,k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_108,c_16])).

tff(c_6869,plain,(
    ! [A_572,A_573] :
      ( r1_tarski(A_572,A_573)
      | ~ m1_subset_1(A_572,k1_zfmisc_1(A_573)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_112])).

tff(c_6879,plain,(
    r1_tarski('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_6869])).

tff(c_54,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6881,plain,(
    r1_tarski('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_6869])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7036,plain,(
    ! [C_596,B_597,A_598] :
      ( r2_hidden(C_596,B_597)
      | ~ r2_hidden(C_596,A_598)
      | ~ r1_tarski(A_598,B_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7067,plain,(
    ! [A_600,B_601] :
      ( r2_hidden('#skF_1'(A_600),B_601)
      | ~ r1_tarski(A_600,B_601)
      | v1_xboole_0(A_600) ) ),
    inference(resolution,[status(thm)],[c_4,c_7036])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7092,plain,(
    ! [B_602,A_603] :
      ( ~ v1_xboole_0(B_602)
      | ~ r1_tarski(A_603,B_602)
      | v1_xboole_0(A_603) ) ),
    inference(resolution,[status(thm)],[c_7067,c_2])).

tff(c_7116,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_6881,c_7092])).

tff(c_7124,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7116])).

tff(c_48,plain,(
    r2_hidden('#skF_11',k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7017,plain,(
    ! [A_593,B_594,C_595] : k2_zfmisc_1(k2_zfmisc_1(A_593,B_594),C_595) = k3_zfmisc_1(A_593,B_594,C_595) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [A_24,C_26,B_25] :
      ( r2_hidden(k2_mcart_1(A_24),C_26)
      | ~ r2_hidden(A_24,k2_zfmisc_1(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7303,plain,(
    ! [A_619,C_620,A_621,B_622] :
      ( r2_hidden(k2_mcart_1(A_619),C_620)
      | ~ r2_hidden(A_619,k3_zfmisc_1(A_621,B_622,C_620)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7017,c_36])).

tff(c_7329,plain,(
    r2_hidden(k2_mcart_1('#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_7303])).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6880,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_6869])).

tff(c_50,plain,(
    m1_subset_1('#skF_11',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7647,plain,(
    ! [A_647,B_648,C_649,D_650] :
      ( k7_mcart_1(A_647,B_648,C_649,D_650) = k2_mcart_1(D_650)
      | ~ m1_subset_1(D_650,k3_zfmisc_1(A_647,B_648,C_649))
      | k1_xboole_0 = C_649
      | k1_xboole_0 = B_648
      | k1_xboole_0 = A_647 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_7651,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_7647])).

tff(c_7743,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_7651])).

tff(c_14,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_10')
    | ~ r2_hidden(k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_9')
    | ~ r2_hidden(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_124,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_153,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_168,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(resolution,[status(thm)],[c_153,c_8])).

tff(c_129,plain,(
    ! [A_60,A_61] :
      ( r1_tarski(A_60,A_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(A_61)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_112])).

tff(c_141,plain,(
    r1_tarski('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_129])).

tff(c_243,plain,(
    ! [C_75,B_76,A_77] :
      ( r2_hidden(C_75,B_76)
      | ~ r2_hidden(C_75,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_319,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_1'(A_88),B_89)
      | ~ r1_tarski(A_88,B_89)
      | v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_4,c_243])).

tff(c_344,plain,(
    ! [B_90,A_91] :
      ( ~ v1_xboole_0(B_90)
      | ~ r1_tarski(A_91,B_90)
      | v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_319,c_2])).

tff(c_368,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_141,c_344])).

tff(c_374,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_140,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_129])).

tff(c_369,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_140,c_344])).

tff(c_376,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_749,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k7_mcart_1(A_122,B_123,C_124,D_125) = k2_mcart_1(D_125)
      | ~ m1_subset_1(D_125,k3_zfmisc_1(A_122,B_123,C_124))
      | k1_xboole_0 = C_124
      | k1_xboole_0 = B_123
      | k1_xboole_0 = A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_753,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_749])).

tff(c_788,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_795,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_12])).

tff(c_797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_795])).

tff(c_799,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_929,plain,(
    ! [A_135,B_136,C_137,D_138] :
      ( k6_mcart_1(A_135,B_136,C_137,D_138) = k2_mcart_1(k1_mcart_1(D_138))
      | ~ m1_subset_1(D_138,k3_zfmisc_1(A_135,B_136,C_137))
      | k1_xboole_0 = C_137
      | k1_xboole_0 = B_136
      | k1_xboole_0 = A_135 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_932,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_929])).

tff(c_935,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_799,c_932])).

tff(c_943,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_935])).

tff(c_955,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_943,c_12])).

tff(c_957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_955])).

tff(c_959,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_935])).

tff(c_851,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k5_mcart_1(A_129,B_130,C_131,D_132) = k1_mcart_1(k1_mcart_1(D_132))
      | ~ m1_subset_1(D_132,k3_zfmisc_1(A_129,B_130,C_131))
      | k1_xboole_0 = C_131
      | k1_xboole_0 = B_130
      | k1_xboole_0 = A_129 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_854,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_11')) = k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_851])).

tff(c_857,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_11')) = k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_799,c_854])).

tff(c_1048,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_11')) = k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11')
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_959,c_857])).

tff(c_1049,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1048])).

tff(c_139,plain,(
    r1_tarski('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_129])).

tff(c_300,plain,(
    ! [A_85,B_86,C_87] : k2_zfmisc_1(k2_zfmisc_1(A_85,B_86),C_87) = k3_zfmisc_1(A_85,B_86,C_87) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_473,plain,(
    ! [A_107,C_108,A_109,B_110] :
      ( r2_hidden(k2_mcart_1(A_107),C_108)
      | ~ r2_hidden(A_107,k3_zfmisc_1(A_109,B_110,C_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_36])).

tff(c_491,plain,(
    r2_hidden(k2_mcart_1('#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_473])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_519,plain,(
    ! [B_113] :
      ( r2_hidden(k2_mcart_1('#skF_11'),B_113)
      | ~ r1_tarski('#skF_10',B_113) ) ),
    inference(resolution,[status(thm)],[c_491,c_6])).

tff(c_691,plain,(
    ! [B_119,B_120] :
      ( r2_hidden(k2_mcart_1('#skF_11'),B_119)
      | ~ r1_tarski(B_120,B_119)
      | ~ r1_tarski('#skF_10',B_120) ) ),
    inference(resolution,[status(thm)],[c_519,c_6])).

tff(c_707,plain,
    ( r2_hidden(k2_mcart_1('#skF_11'),'#skF_7')
    | ~ r1_tarski('#skF_10','#skF_10') ),
    inference(resolution,[status(thm)],[c_139,c_691])).

tff(c_721,plain,(
    r2_hidden(k2_mcart_1('#skF_11'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_707])).

tff(c_759,plain,(
    ! [B_126] :
      ( r2_hidden(k2_mcart_1('#skF_11'),B_126)
      | ~ r1_tarski('#skF_7',B_126) ) ),
    inference(resolution,[status(thm)],[c_721,c_6])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_811,plain,(
    ! [B_128] :
      ( ~ r1_tarski(B_128,k2_mcart_1('#skF_11'))
      | ~ r1_tarski('#skF_7',B_128) ) ),
    inference(resolution,[status(thm)],[c_759,c_32])).

tff(c_846,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_811])).

tff(c_1056,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_846])).

tff(c_1067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_1056])).

tff(c_1068,plain,(
    k1_mcart_1(k1_mcart_1('#skF_11')) = k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11') ),
    inference(splitRight,[status(thm)],[c_1048])).

tff(c_38,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden(k1_mcart_1(A_24),B_25)
      | ~ r2_hidden(A_24,k2_zfmisc_1(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3203,plain,(
    ! [A_315,A_316,B_317,C_318] :
      ( r2_hidden(k1_mcart_1(A_315),k2_zfmisc_1(A_316,B_317))
      | ~ r2_hidden(A_315,k3_zfmisc_1(A_316,B_317,C_318)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_38])).

tff(c_3252,plain,(
    r2_hidden(k1_mcart_1('#skF_11'),k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_48,c_3203])).

tff(c_3257,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_11')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_3252,c_38])).

tff(c_3269,plain,(
    r2_hidden(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1068,c_3257])).

tff(c_3271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_3269])).

tff(c_3272,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_274,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden(k1_mcart_1(A_79),B_80)
      | ~ r2_hidden(A_79,k2_zfmisc_1(B_80,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5022,plain,(
    ! [B_440,C_441] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_440,C_441))),B_440)
      | v1_xboole_0(k2_zfmisc_1(B_440,C_441)) ) ),
    inference(resolution,[status(thm)],[c_4,c_274])).

tff(c_5055,plain,(
    ! [B_440,C_441] :
      ( ~ v1_xboole_0(B_440)
      | v1_xboole_0(k2_zfmisc_1(B_440,C_441)) ) ),
    inference(resolution,[status(thm)],[c_5022,c_2])).

tff(c_34,plain,(
    ! [A_21,B_22,C_23] : k2_zfmisc_1(k2_zfmisc_1(A_21,B_22),C_23) = k3_zfmisc_1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5057,plain,(
    ! [B_442,C_443] :
      ( ~ v1_xboole_0(B_442)
      | v1_xboole_0(k2_zfmisc_1(B_442,C_443)) ) ),
    inference(resolution,[status(thm)],[c_5022,c_2])).

tff(c_5061,plain,(
    ! [A_444,B_445,C_446] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_444,B_445))
      | v1_xboole_0(k3_zfmisc_1(A_444,B_445,C_446)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_5057])).

tff(c_77,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_5065,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_5061,c_77])).

tff(c_5068,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_5055,c_5065])).

tff(c_5075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_5068])).

tff(c_5076,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_287,plain,(
    ! [A_82,C_83,B_84] :
      ( r2_hidden(k2_mcart_1(A_82),C_83)
      | ~ r2_hidden(A_82,k2_zfmisc_1(B_84,C_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6290,plain,(
    ! [B_531,C_532] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_531,C_532))),C_532)
      | v1_xboole_0(k2_zfmisc_1(B_531,C_532)) ) ),
    inference(resolution,[status(thm)],[c_4,c_287])).

tff(c_6321,plain,(
    ! [C_532,B_531] :
      ( ~ v1_xboole_0(C_532)
      | v1_xboole_0(k2_zfmisc_1(B_531,C_532)) ) ),
    inference(resolution,[status(thm)],[c_6290,c_2])).

tff(c_6780,plain,(
    ! [A_568,A_569,B_570,C_571] :
      ( r2_hidden(k1_mcart_1(A_568),k2_zfmisc_1(A_569,B_570))
      | ~ r2_hidden(A_568,k3_zfmisc_1(A_569,B_570,C_571)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_38])).

tff(c_6825,plain,(
    r2_hidden(k1_mcart_1('#skF_11'),k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_48,c_6780])).

tff(c_6843,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_6825,c_2])).

tff(c_6846,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_6321,c_6843])).

tff(c_6853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5076,c_6846])).

tff(c_6855,plain,(
    r2_hidden(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_7190,plain,(
    ! [B_610] :
      ( r2_hidden(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),B_610)
      | ~ r1_tarski('#skF_8',B_610) ) ),
    inference(resolution,[status(thm)],[c_6855,c_7036])).

tff(c_7489,plain,(
    ! [B_629] :
      ( ~ r1_tarski(B_629,k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'))
      | ~ r1_tarski('#skF_8',B_629) ) ),
    inference(resolution,[status(thm)],[c_7190,c_32])).

tff(c_7529,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_7489])).

tff(c_7752,plain,(
    ~ r1_tarski('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7743,c_7529])).

tff(c_7762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6880,c_7752])).

tff(c_7763,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7'
    | k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11') = k2_mcart_1('#skF_11') ),
    inference(splitRight,[status(thm)],[c_7651])).

tff(c_7845,plain,(
    k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11') = k2_mcart_1('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_7763])).

tff(c_6854,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_9')
    | ~ r2_hidden(k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6864,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_6854])).

tff(c_7847,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_11'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7845,c_6864])).

tff(c_7850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7329,c_7847])).

tff(c_7851,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7763])).

tff(c_7853,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7851])).

tff(c_7876,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7853,c_12])).

tff(c_7878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7124,c_7876])).

tff(c_7879,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7851])).

tff(c_7346,plain,(
    ! [B_623] :
      ( r2_hidden(k2_mcart_1('#skF_11'),B_623)
      | ~ r1_tarski('#skF_10',B_623) ) ),
    inference(resolution,[status(thm)],[c_7329,c_6])).

tff(c_7390,plain,(
    ! [B_625] :
      ( ~ r1_tarski(B_625,k2_mcart_1('#skF_11'))
      | ~ r1_tarski('#skF_10',B_625) ) ),
    inference(resolution,[status(thm)],[c_7346,c_32])).

tff(c_7425,plain,(
    ~ r1_tarski('#skF_10',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_7390])).

tff(c_7899,plain,(
    ~ r1_tarski('#skF_10','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7879,c_7425])).

tff(c_7907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6879,c_7899])).

tff(c_7908,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_7116])).

tff(c_7004,plain,(
    ! [A_590,C_591,B_592] :
      ( r2_hidden(k2_mcart_1(A_590),C_591)
      | ~ r2_hidden(A_590,k2_zfmisc_1(B_592,C_591)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_9174,plain,(
    ! [B_746,C_747] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_746,C_747))),C_747)
      | v1_xboole_0(k2_zfmisc_1(B_746,C_747)) ) ),
    inference(resolution,[status(thm)],[c_4,c_7004])).

tff(c_9205,plain,(
    ! [C_747,B_746] :
      ( ~ v1_xboole_0(C_747)
      | v1_xboole_0(k2_zfmisc_1(B_746,C_747)) ) ),
    inference(resolution,[status(thm)],[c_9174,c_2])).

tff(c_9577,plain,(
    ! [A_773,A_774,B_775,C_776] :
      ( r2_hidden(k1_mcart_1(A_773),k2_zfmisc_1(A_774,B_775))
      | ~ r2_hidden(A_773,k3_zfmisc_1(A_774,B_775,C_776)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7017,c_38])).

tff(c_9623,plain,(
    r2_hidden(k1_mcart_1('#skF_11'),k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_48,c_9577])).

tff(c_9641,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_9623,c_2])).

tff(c_9644,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_9205,c_9641])).

tff(c_9651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7908,c_9644])).

tff(c_9652,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_6854])).

tff(c_9691,plain,(
    ! [A_781,B_782] :
      ( r2_hidden('#skF_2'(A_781,B_782),A_781)
      | r1_tarski(A_781,B_782) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9706,plain,(
    ! [A_781] : r1_tarski(A_781,A_781) ),
    inference(resolution,[status(thm)],[c_9691,c_8])).

tff(c_9666,plain,(
    ! [A_777,A_778] :
      ( r1_tarski(A_777,A_778)
      | ~ m1_subset_1(A_777,k1_zfmisc_1(A_778)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_112])).

tff(c_9678,plain,(
    r1_tarski('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_9666])).

tff(c_9745,plain,(
    ! [C_787,B_788,A_789] :
      ( r2_hidden(C_787,B_788)
      | ~ r2_hidden(C_787,A_789)
      | ~ r1_tarski(A_789,B_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9872,plain,(
    ! [A_805,B_806] :
      ( r2_hidden('#skF_1'(A_805),B_806)
      | ~ r1_tarski(A_805,B_806)
      | v1_xboole_0(A_805) ) ),
    inference(resolution,[status(thm)],[c_4,c_9745])).

tff(c_9897,plain,(
    ! [B_807,A_808] :
      ( ~ v1_xboole_0(B_807)
      | ~ r1_tarski(A_808,B_807)
      | v1_xboole_0(A_808) ) ),
    inference(resolution,[status(thm)],[c_9872,c_2])).

tff(c_9921,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_9678,c_9897])).

tff(c_9931,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9921])).

tff(c_9677,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_9666])).

tff(c_10559,plain,(
    ! [A_856,B_857,C_858,D_859] :
      ( k7_mcart_1(A_856,B_857,C_858,D_859) = k2_mcart_1(D_859)
      | ~ m1_subset_1(D_859,k3_zfmisc_1(A_856,B_857,C_858))
      | k1_xboole_0 = C_858
      | k1_xboole_0 = B_857
      | k1_xboole_0 = A_856 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10563,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_10559])).

tff(c_10587,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_10563])).

tff(c_10008,plain,(
    ! [B_816] :
      ( r2_hidden(k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),B_816)
      | ~ r1_tarski('#skF_8',B_816) ) ),
    inference(resolution,[status(thm)],[c_6855,c_9745])).

tff(c_10396,plain,(
    ! [B_849] :
      ( ~ r1_tarski(B_849,k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'))
      | ~ r1_tarski('#skF_8',B_849) ) ),
    inference(resolution,[status(thm)],[c_10008,c_32])).

tff(c_10436,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_10396])).

tff(c_10596,plain,(
    ~ r1_tarski('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10587,c_10436])).

tff(c_10608,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9677,c_10596])).

tff(c_10610,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10563])).

tff(c_10664,plain,(
    ! [A_863,B_864,C_865,D_866] :
      ( k5_mcart_1(A_863,B_864,C_865,D_866) = k1_mcart_1(k1_mcart_1(D_866))
      | ~ m1_subset_1(D_866,k3_zfmisc_1(A_863,B_864,C_865))
      | k1_xboole_0 = C_865
      | k1_xboole_0 = B_864
      | k1_xboole_0 = A_863 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10667,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_11')) = k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_10664])).

tff(c_10670,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_11')) = k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_10610,c_10667])).

tff(c_11064,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10670])).

tff(c_11091,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11064,c_12])).

tff(c_11093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9931,c_11091])).

tff(c_11095,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10670])).

tff(c_10845,plain,(
    ! [A_873,B_874,C_875,D_876] :
      ( k6_mcart_1(A_873,B_874,C_875,D_876) = k2_mcart_1(k1_mcart_1(D_876))
      | ~ m1_subset_1(D_876,k3_zfmisc_1(A_873,B_874,C_875))
      | k1_xboole_0 = C_875
      | k1_xboole_0 = B_874
      | k1_xboole_0 = A_873 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10848,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_10845])).

tff(c_10851,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_10610,c_10848])).

tff(c_11180,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11')
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_11095,c_10851])).

tff(c_11181,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_11180])).

tff(c_9676,plain,(
    r1_tarski('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_9666])).

tff(c_9857,plain,(
    ! [A_802,C_803,B_804] :
      ( r2_hidden(k2_mcart_1(A_802),C_803)
      | ~ r2_hidden(A_802,k2_zfmisc_1(B_804,C_803)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10069,plain,(
    ! [A_822,C_823,A_824,B_825] :
      ( r2_hidden(k2_mcart_1(A_822),C_823)
      | ~ r2_hidden(A_822,k3_zfmisc_1(A_824,B_825,C_823)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9857])).

tff(c_10091,plain,(
    r2_hidden(k2_mcart_1('#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_48,c_10069])).

tff(c_10117,plain,(
    ! [B_828] :
      ( r2_hidden(k2_mcart_1('#skF_11'),B_828)
      | ~ r1_tarski('#skF_10',B_828) ) ),
    inference(resolution,[status(thm)],[c_10091,c_6])).

tff(c_10852,plain,(
    ! [B_877,B_878] :
      ( r2_hidden(k2_mcart_1('#skF_11'),B_877)
      | ~ r1_tarski(B_878,B_877)
      | ~ r1_tarski('#skF_10',B_878) ) ),
    inference(resolution,[status(thm)],[c_10117,c_6])).

tff(c_10878,plain,
    ( r2_hidden(k2_mcart_1('#skF_11'),'#skF_7')
    | ~ r1_tarski('#skF_10','#skF_10') ),
    inference(resolution,[status(thm)],[c_9676,c_10852])).

tff(c_10897,plain,(
    r2_hidden(k2_mcart_1('#skF_11'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9706,c_10878])).

tff(c_10925,plain,(
    ! [B_879] :
      ( r2_hidden(k2_mcart_1('#skF_11'),B_879)
      | ~ r1_tarski('#skF_7',B_879) ) ),
    inference(resolution,[status(thm)],[c_10897,c_6])).

tff(c_11004,plain,(
    ! [B_885] :
      ( ~ r1_tarski(B_885,k2_mcart_1('#skF_11'))
      | ~ r1_tarski('#skF_7',B_885) ) ),
    inference(resolution,[status(thm)],[c_10925,c_32])).

tff(c_11059,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_11004])).

tff(c_11185,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11181,c_11059])).

tff(c_11214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9706,c_11185])).

tff(c_11215,plain,(
    k2_mcart_1(k1_mcart_1('#skF_11')) = k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11') ),
    inference(splitRight,[status(thm)],[c_11180])).

tff(c_9842,plain,(
    ! [A_799,B_800,C_801] :
      ( r2_hidden(k1_mcart_1(A_799),B_800)
      | ~ r2_hidden(A_799,k2_zfmisc_1(B_800,C_801)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12084,plain,(
    ! [A_953,A_954,B_955,C_956] :
      ( r2_hidden(k1_mcart_1(A_953),k2_zfmisc_1(A_954,B_955))
      | ~ r2_hidden(A_953,k3_zfmisc_1(A_954,B_955,C_956)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9842])).

tff(c_12137,plain,(
    r2_hidden(k1_mcart_1('#skF_11'),k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_48,c_12084])).

tff(c_12140,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_11')),'#skF_9') ),
    inference(resolution,[status(thm)],[c_12137,c_36])).

tff(c_12152,plain,(
    r2_hidden(k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_11'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11215,c_12140])).

tff(c_12154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9652,c_12152])).

tff(c_12155,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_9921])).

tff(c_13561,plain,(
    ! [B_1039,C_1040] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1039,C_1040))),C_1040)
      | v1_xboole_0(k2_zfmisc_1(B_1039,C_1040)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9857])).

tff(c_13592,plain,(
    ! [C_1040,B_1039] :
      ( ~ v1_xboole_0(C_1040)
      | v1_xboole_0(k2_zfmisc_1(B_1039,C_1040)) ) ),
    inference(resolution,[status(thm)],[c_13561,c_2])).

tff(c_14185,plain,(
    ! [A_1075,A_1076,B_1077,C_1078] :
      ( r2_hidden(k1_mcart_1(A_1075),k2_zfmisc_1(A_1076,B_1077))
      | ~ r2_hidden(A_1075,k3_zfmisc_1(A_1076,B_1077,C_1078)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9842])).

tff(c_14234,plain,(
    r2_hidden(k1_mcart_1('#skF_11'),k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_48,c_14185])).

tff(c_14252,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_14234,c_2])).

tff(c_14258,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_13592,c_14252])).

tff(c_14263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12155,c_14258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:40:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.17/3.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/3.03  
% 8.41/3.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/3.04  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 8.41/3.04  
% 8.41/3.04  %Foreground sorts:
% 8.41/3.04  
% 8.41/3.04  
% 8.41/3.04  %Background operators:
% 8.41/3.04  
% 8.41/3.04  
% 8.41/3.04  %Foreground operators:
% 8.41/3.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.41/3.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.41/3.04  tff('#skF_11', type, '#skF_11': $i).
% 8.41/3.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.41/3.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.41/3.04  tff('#skF_7', type, '#skF_7': $i).
% 8.41/3.04  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.41/3.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.41/3.04  tff('#skF_10', type, '#skF_10': $i).
% 8.41/3.04  tff('#skF_5', type, '#skF_5': $i).
% 8.41/3.04  tff('#skF_6', type, '#skF_6': $i).
% 8.41/3.04  tff('#skF_9', type, '#skF_9': $i).
% 8.41/3.04  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 8.41/3.04  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 8.41/3.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.41/3.04  tff('#skF_8', type, '#skF_8': $i).
% 8.41/3.04  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 8.41/3.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.41/3.04  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 8.41/3.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.41/3.04  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 8.41/3.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.41/3.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.41/3.04  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 8.41/3.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.41/3.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.41/3.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.41/3.04  
% 8.41/3.06  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 8.41/3.06  tff(f_51, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.41/3.06  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 8.41/3.06  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.41/3.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.41/3.06  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.41/3.06  tff(f_64, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 8.41/3.06  tff(f_70, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 8.41/3.06  tff(f_90, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 8.41/3.06  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.41/3.06  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.41/3.06  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.41/3.06  tff(c_52, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.41/3.06  tff(c_28, plain, (![A_16]: (~v1_xboole_0(k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.41/3.06  tff(c_108, plain, (![A_58, B_59]: (r2_hidden(A_58, B_59) | v1_xboole_0(B_59) | ~m1_subset_1(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.41/3.06  tff(c_16, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.41/3.06  tff(c_112, plain, (![A_58, A_11]: (r1_tarski(A_58, A_11) | v1_xboole_0(k1_zfmisc_1(A_11)) | ~m1_subset_1(A_58, k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_108, c_16])).
% 8.41/3.06  tff(c_6869, plain, (![A_572, A_573]: (r1_tarski(A_572, A_573) | ~m1_subset_1(A_572, k1_zfmisc_1(A_573)))), inference(negUnitSimplification, [status(thm)], [c_28, c_112])).
% 8.41/3.06  tff(c_6879, plain, (r1_tarski('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_6869])).
% 8.41/3.06  tff(c_54, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.41/3.06  tff(c_6881, plain, (r1_tarski('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_6869])).
% 8.41/3.06  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.41/3.06  tff(c_7036, plain, (![C_596, B_597, A_598]: (r2_hidden(C_596, B_597) | ~r2_hidden(C_596, A_598) | ~r1_tarski(A_598, B_597))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/3.06  tff(c_7067, plain, (![A_600, B_601]: (r2_hidden('#skF_1'(A_600), B_601) | ~r1_tarski(A_600, B_601) | v1_xboole_0(A_600))), inference(resolution, [status(thm)], [c_4, c_7036])).
% 8.41/3.06  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.41/3.06  tff(c_7092, plain, (![B_602, A_603]: (~v1_xboole_0(B_602) | ~r1_tarski(A_603, B_602) | v1_xboole_0(A_603))), inference(resolution, [status(thm)], [c_7067, c_2])).
% 8.41/3.06  tff(c_7116, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_6881, c_7092])).
% 8.41/3.06  tff(c_7124, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_7116])).
% 8.41/3.06  tff(c_48, plain, (r2_hidden('#skF_11', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.41/3.06  tff(c_7017, plain, (![A_593, B_594, C_595]: (k2_zfmisc_1(k2_zfmisc_1(A_593, B_594), C_595)=k3_zfmisc_1(A_593, B_594, C_595))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.41/3.06  tff(c_36, plain, (![A_24, C_26, B_25]: (r2_hidden(k2_mcart_1(A_24), C_26) | ~r2_hidden(A_24, k2_zfmisc_1(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.41/3.06  tff(c_7303, plain, (![A_619, C_620, A_621, B_622]: (r2_hidden(k2_mcart_1(A_619), C_620) | ~r2_hidden(A_619, k3_zfmisc_1(A_621, B_622, C_620)))), inference(superposition, [status(thm), theory('equality')], [c_7017, c_36])).
% 8.41/3.06  tff(c_7329, plain, (r2_hidden(k2_mcart_1('#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_48, c_7303])).
% 8.41/3.06  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.41/3.06  tff(c_6880, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_6869])).
% 8.41/3.06  tff(c_50, plain, (m1_subset_1('#skF_11', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.41/3.06  tff(c_7647, plain, (![A_647, B_648, C_649, D_650]: (k7_mcart_1(A_647, B_648, C_649, D_650)=k2_mcart_1(D_650) | ~m1_subset_1(D_650, k3_zfmisc_1(A_647, B_648, C_649)) | k1_xboole_0=C_649 | k1_xboole_0=B_648 | k1_xboole_0=A_647)), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.41/3.06  tff(c_7651, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_7647])).
% 8.41/3.06  tff(c_7743, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_7651])).
% 8.41/3.06  tff(c_14, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.41/3.06  tff(c_46, plain, (~r2_hidden(k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_10') | ~r2_hidden(k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_9') | ~r2_hidden(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.41/3.06  tff(c_124, plain, (~r2_hidden(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_8')), inference(splitLeft, [status(thm)], [c_46])).
% 8.41/3.06  tff(c_153, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/3.06  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/3.06  tff(c_168, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(resolution, [status(thm)], [c_153, c_8])).
% 8.41/3.06  tff(c_129, plain, (![A_60, A_61]: (r1_tarski(A_60, A_61) | ~m1_subset_1(A_60, k1_zfmisc_1(A_61)))), inference(negUnitSimplification, [status(thm)], [c_28, c_112])).
% 8.41/3.06  tff(c_141, plain, (r1_tarski('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_129])).
% 8.41/3.06  tff(c_243, plain, (![C_75, B_76, A_77]: (r2_hidden(C_75, B_76) | ~r2_hidden(C_75, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/3.06  tff(c_319, plain, (![A_88, B_89]: (r2_hidden('#skF_1'(A_88), B_89) | ~r1_tarski(A_88, B_89) | v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_4, c_243])).
% 8.41/3.06  tff(c_344, plain, (![B_90, A_91]: (~v1_xboole_0(B_90) | ~r1_tarski(A_91, B_90) | v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_319, c_2])).
% 8.41/3.06  tff(c_368, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_141, c_344])).
% 8.41/3.06  tff(c_374, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_368])).
% 8.41/3.06  tff(c_140, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_129])).
% 8.41/3.06  tff(c_369, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_140, c_344])).
% 8.41/3.06  tff(c_376, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_369])).
% 8.41/3.06  tff(c_749, plain, (![A_122, B_123, C_124, D_125]: (k7_mcart_1(A_122, B_123, C_124, D_125)=k2_mcart_1(D_125) | ~m1_subset_1(D_125, k3_zfmisc_1(A_122, B_123, C_124)) | k1_xboole_0=C_124 | k1_xboole_0=B_123 | k1_xboole_0=A_122)), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.41/3.06  tff(c_753, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_749])).
% 8.41/3.06  tff(c_788, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_753])).
% 8.41/3.06  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.41/3.06  tff(c_795, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_12])).
% 8.41/3.06  tff(c_797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_795])).
% 8.41/3.06  tff(c_799, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_753])).
% 8.41/3.06  tff(c_929, plain, (![A_135, B_136, C_137, D_138]: (k6_mcart_1(A_135, B_136, C_137, D_138)=k2_mcart_1(k1_mcart_1(D_138)) | ~m1_subset_1(D_138, k3_zfmisc_1(A_135, B_136, C_137)) | k1_xboole_0=C_137 | k1_xboole_0=B_136 | k1_xboole_0=A_135)), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.41/3.06  tff(c_932, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_929])).
% 8.41/3.06  tff(c_935, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_799, c_932])).
% 8.41/3.06  tff(c_943, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_935])).
% 8.41/3.06  tff(c_955, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_943, c_12])).
% 8.41/3.06  tff(c_957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_374, c_955])).
% 8.41/3.06  tff(c_959, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_935])).
% 8.41/3.06  tff(c_851, plain, (![A_129, B_130, C_131, D_132]: (k5_mcart_1(A_129, B_130, C_131, D_132)=k1_mcart_1(k1_mcart_1(D_132)) | ~m1_subset_1(D_132, k3_zfmisc_1(A_129, B_130, C_131)) | k1_xboole_0=C_131 | k1_xboole_0=B_130 | k1_xboole_0=A_129)), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.41/3.06  tff(c_854, plain, (k1_mcart_1(k1_mcart_1('#skF_11'))=k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_851])).
% 8.41/3.06  tff(c_857, plain, (k1_mcart_1(k1_mcart_1('#skF_11'))=k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_799, c_854])).
% 8.41/3.06  tff(c_1048, plain, (k1_mcart_1(k1_mcart_1('#skF_11'))=k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11') | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_959, c_857])).
% 8.41/3.06  tff(c_1049, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_1048])).
% 8.41/3.06  tff(c_139, plain, (r1_tarski('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_129])).
% 8.41/3.06  tff(c_300, plain, (![A_85, B_86, C_87]: (k2_zfmisc_1(k2_zfmisc_1(A_85, B_86), C_87)=k3_zfmisc_1(A_85, B_86, C_87))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.41/3.06  tff(c_473, plain, (![A_107, C_108, A_109, B_110]: (r2_hidden(k2_mcart_1(A_107), C_108) | ~r2_hidden(A_107, k3_zfmisc_1(A_109, B_110, C_108)))), inference(superposition, [status(thm), theory('equality')], [c_300, c_36])).
% 8.41/3.06  tff(c_491, plain, (r2_hidden(k2_mcart_1('#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_48, c_473])).
% 8.41/3.06  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/3.06  tff(c_519, plain, (![B_113]: (r2_hidden(k2_mcart_1('#skF_11'), B_113) | ~r1_tarski('#skF_10', B_113))), inference(resolution, [status(thm)], [c_491, c_6])).
% 8.41/3.06  tff(c_691, plain, (![B_119, B_120]: (r2_hidden(k2_mcart_1('#skF_11'), B_119) | ~r1_tarski(B_120, B_119) | ~r1_tarski('#skF_10', B_120))), inference(resolution, [status(thm)], [c_519, c_6])).
% 8.41/3.06  tff(c_707, plain, (r2_hidden(k2_mcart_1('#skF_11'), '#skF_7') | ~r1_tarski('#skF_10', '#skF_10')), inference(resolution, [status(thm)], [c_139, c_691])).
% 8.41/3.06  tff(c_721, plain, (r2_hidden(k2_mcart_1('#skF_11'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_707])).
% 8.41/3.06  tff(c_759, plain, (![B_126]: (r2_hidden(k2_mcart_1('#skF_11'), B_126) | ~r1_tarski('#skF_7', B_126))), inference(resolution, [status(thm)], [c_721, c_6])).
% 8.41/3.06  tff(c_32, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.41/3.06  tff(c_811, plain, (![B_128]: (~r1_tarski(B_128, k2_mcart_1('#skF_11')) | ~r1_tarski('#skF_7', B_128))), inference(resolution, [status(thm)], [c_759, c_32])).
% 8.41/3.06  tff(c_846, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_811])).
% 8.41/3.06  tff(c_1056, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_846])).
% 8.41/3.06  tff(c_1067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_1056])).
% 8.41/3.06  tff(c_1068, plain, (k1_mcart_1(k1_mcart_1('#skF_11'))=k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11')), inference(splitRight, [status(thm)], [c_1048])).
% 8.41/3.06  tff(c_38, plain, (![A_24, B_25, C_26]: (r2_hidden(k1_mcart_1(A_24), B_25) | ~r2_hidden(A_24, k2_zfmisc_1(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.41/3.06  tff(c_3203, plain, (![A_315, A_316, B_317, C_318]: (r2_hidden(k1_mcart_1(A_315), k2_zfmisc_1(A_316, B_317)) | ~r2_hidden(A_315, k3_zfmisc_1(A_316, B_317, C_318)))), inference(superposition, [status(thm), theory('equality')], [c_300, c_38])).
% 8.41/3.06  tff(c_3252, plain, (r2_hidden(k1_mcart_1('#skF_11'), k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_48, c_3203])).
% 8.41/3.06  tff(c_3257, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_11')), '#skF_8')), inference(resolution, [status(thm)], [c_3252, c_38])).
% 8.41/3.06  tff(c_3269, plain, (r2_hidden(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1068, c_3257])).
% 8.41/3.06  tff(c_3271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_3269])).
% 8.41/3.06  tff(c_3272, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_369])).
% 8.41/3.06  tff(c_274, plain, (![A_79, B_80, C_81]: (r2_hidden(k1_mcart_1(A_79), B_80) | ~r2_hidden(A_79, k2_zfmisc_1(B_80, C_81)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.41/3.06  tff(c_5022, plain, (![B_440, C_441]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_440, C_441))), B_440) | v1_xboole_0(k2_zfmisc_1(B_440, C_441)))), inference(resolution, [status(thm)], [c_4, c_274])).
% 8.41/3.06  tff(c_5055, plain, (![B_440, C_441]: (~v1_xboole_0(B_440) | v1_xboole_0(k2_zfmisc_1(B_440, C_441)))), inference(resolution, [status(thm)], [c_5022, c_2])).
% 8.41/3.06  tff(c_34, plain, (![A_21, B_22, C_23]: (k2_zfmisc_1(k2_zfmisc_1(A_21, B_22), C_23)=k3_zfmisc_1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.41/3.06  tff(c_5057, plain, (![B_442, C_443]: (~v1_xboole_0(B_442) | v1_xboole_0(k2_zfmisc_1(B_442, C_443)))), inference(resolution, [status(thm)], [c_5022, c_2])).
% 8.41/3.06  tff(c_5061, plain, (![A_444, B_445, C_446]: (~v1_xboole_0(k2_zfmisc_1(A_444, B_445)) | v1_xboole_0(k3_zfmisc_1(A_444, B_445, C_446)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_5057])).
% 8.41/3.06  tff(c_77, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_48, c_2])).
% 8.41/3.06  tff(c_5065, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_5061, c_77])).
% 8.41/3.06  tff(c_5068, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_5055, c_5065])).
% 8.41/3.06  tff(c_5075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3272, c_5068])).
% 8.41/3.06  tff(c_5076, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_368])).
% 8.41/3.06  tff(c_287, plain, (![A_82, C_83, B_84]: (r2_hidden(k2_mcart_1(A_82), C_83) | ~r2_hidden(A_82, k2_zfmisc_1(B_84, C_83)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.41/3.06  tff(c_6290, plain, (![B_531, C_532]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_531, C_532))), C_532) | v1_xboole_0(k2_zfmisc_1(B_531, C_532)))), inference(resolution, [status(thm)], [c_4, c_287])).
% 8.41/3.06  tff(c_6321, plain, (![C_532, B_531]: (~v1_xboole_0(C_532) | v1_xboole_0(k2_zfmisc_1(B_531, C_532)))), inference(resolution, [status(thm)], [c_6290, c_2])).
% 8.41/3.06  tff(c_6780, plain, (![A_568, A_569, B_570, C_571]: (r2_hidden(k1_mcart_1(A_568), k2_zfmisc_1(A_569, B_570)) | ~r2_hidden(A_568, k3_zfmisc_1(A_569, B_570, C_571)))), inference(superposition, [status(thm), theory('equality')], [c_300, c_38])).
% 8.41/3.06  tff(c_6825, plain, (r2_hidden(k1_mcart_1('#skF_11'), k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_48, c_6780])).
% 8.41/3.06  tff(c_6843, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_6825, c_2])).
% 8.41/3.06  tff(c_6846, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_6321, c_6843])).
% 8.41/3.06  tff(c_6853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5076, c_6846])).
% 8.41/3.06  tff(c_6855, plain, (r2_hidden(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_8')), inference(splitRight, [status(thm)], [c_46])).
% 8.41/3.06  tff(c_7190, plain, (![B_610]: (r2_hidden(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), B_610) | ~r1_tarski('#skF_8', B_610))), inference(resolution, [status(thm)], [c_6855, c_7036])).
% 8.41/3.06  tff(c_7489, plain, (![B_629]: (~r1_tarski(B_629, k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11')) | ~r1_tarski('#skF_8', B_629))), inference(resolution, [status(thm)], [c_7190, c_32])).
% 8.41/3.06  tff(c_7529, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_7489])).
% 8.41/3.06  tff(c_7752, plain, (~r1_tarski('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7743, c_7529])).
% 8.41/3.06  tff(c_7762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6880, c_7752])).
% 8.41/3.06  tff(c_7763, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7' | k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11')=k2_mcart_1('#skF_11')), inference(splitRight, [status(thm)], [c_7651])).
% 8.41/3.06  tff(c_7845, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11')=k2_mcart_1('#skF_11')), inference(splitLeft, [status(thm)], [c_7763])).
% 8.41/3.06  tff(c_6854, plain, (~r2_hidden(k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_9') | ~r2_hidden(k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_10')), inference(splitRight, [status(thm)], [c_46])).
% 8.41/3.06  tff(c_6864, plain, (~r2_hidden(k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_10')), inference(splitLeft, [status(thm)], [c_6854])).
% 8.41/3.06  tff(c_7847, plain, (~r2_hidden(k2_mcart_1('#skF_11'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_7845, c_6864])).
% 8.41/3.06  tff(c_7850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7329, c_7847])).
% 8.41/3.06  tff(c_7851, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_7763])).
% 8.41/3.06  tff(c_7853, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_7851])).
% 8.41/3.06  tff(c_7876, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7853, c_12])).
% 8.41/3.06  tff(c_7878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7124, c_7876])).
% 8.41/3.06  tff(c_7879, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_7851])).
% 8.41/3.06  tff(c_7346, plain, (![B_623]: (r2_hidden(k2_mcart_1('#skF_11'), B_623) | ~r1_tarski('#skF_10', B_623))), inference(resolution, [status(thm)], [c_7329, c_6])).
% 8.41/3.06  tff(c_7390, plain, (![B_625]: (~r1_tarski(B_625, k2_mcart_1('#skF_11')) | ~r1_tarski('#skF_10', B_625))), inference(resolution, [status(thm)], [c_7346, c_32])).
% 8.41/3.06  tff(c_7425, plain, (~r1_tarski('#skF_10', k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_7390])).
% 8.41/3.06  tff(c_7899, plain, (~r1_tarski('#skF_10', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7879, c_7425])).
% 8.41/3.06  tff(c_7907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6879, c_7899])).
% 8.41/3.06  tff(c_7908, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_7116])).
% 8.41/3.06  tff(c_7004, plain, (![A_590, C_591, B_592]: (r2_hidden(k2_mcart_1(A_590), C_591) | ~r2_hidden(A_590, k2_zfmisc_1(B_592, C_591)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.41/3.06  tff(c_9174, plain, (![B_746, C_747]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_746, C_747))), C_747) | v1_xboole_0(k2_zfmisc_1(B_746, C_747)))), inference(resolution, [status(thm)], [c_4, c_7004])).
% 8.41/3.06  tff(c_9205, plain, (![C_747, B_746]: (~v1_xboole_0(C_747) | v1_xboole_0(k2_zfmisc_1(B_746, C_747)))), inference(resolution, [status(thm)], [c_9174, c_2])).
% 8.41/3.06  tff(c_9577, plain, (![A_773, A_774, B_775, C_776]: (r2_hidden(k1_mcart_1(A_773), k2_zfmisc_1(A_774, B_775)) | ~r2_hidden(A_773, k3_zfmisc_1(A_774, B_775, C_776)))), inference(superposition, [status(thm), theory('equality')], [c_7017, c_38])).
% 8.41/3.06  tff(c_9623, plain, (r2_hidden(k1_mcart_1('#skF_11'), k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_48, c_9577])).
% 8.41/3.06  tff(c_9641, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_9623, c_2])).
% 8.41/3.06  tff(c_9644, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_9205, c_9641])).
% 8.41/3.06  tff(c_9651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7908, c_9644])).
% 8.41/3.06  tff(c_9652, plain, (~r2_hidden(k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_6854])).
% 8.41/3.06  tff(c_9691, plain, (![A_781, B_782]: (r2_hidden('#skF_2'(A_781, B_782), A_781) | r1_tarski(A_781, B_782))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/3.06  tff(c_9706, plain, (![A_781]: (r1_tarski(A_781, A_781))), inference(resolution, [status(thm)], [c_9691, c_8])).
% 8.41/3.06  tff(c_9666, plain, (![A_777, A_778]: (r1_tarski(A_777, A_778) | ~m1_subset_1(A_777, k1_zfmisc_1(A_778)))), inference(negUnitSimplification, [status(thm)], [c_28, c_112])).
% 8.41/3.06  tff(c_9678, plain, (r1_tarski('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_54, c_9666])).
% 8.41/3.06  tff(c_9745, plain, (![C_787, B_788, A_789]: (r2_hidden(C_787, B_788) | ~r2_hidden(C_787, A_789) | ~r1_tarski(A_789, B_788))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/3.06  tff(c_9872, plain, (![A_805, B_806]: (r2_hidden('#skF_1'(A_805), B_806) | ~r1_tarski(A_805, B_806) | v1_xboole_0(A_805))), inference(resolution, [status(thm)], [c_4, c_9745])).
% 8.41/3.06  tff(c_9897, plain, (![B_807, A_808]: (~v1_xboole_0(B_807) | ~r1_tarski(A_808, B_807) | v1_xboole_0(A_808))), inference(resolution, [status(thm)], [c_9872, c_2])).
% 8.41/3.06  tff(c_9921, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_9678, c_9897])).
% 8.41/3.06  tff(c_9931, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_9921])).
% 8.41/3.06  tff(c_9677, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_9666])).
% 8.41/3.06  tff(c_10559, plain, (![A_856, B_857, C_858, D_859]: (k7_mcart_1(A_856, B_857, C_858, D_859)=k2_mcart_1(D_859) | ~m1_subset_1(D_859, k3_zfmisc_1(A_856, B_857, C_858)) | k1_xboole_0=C_858 | k1_xboole_0=B_857 | k1_xboole_0=A_856)), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.41/3.06  tff(c_10563, plain, (k7_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_10559])).
% 8.41/3.06  tff(c_10587, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_10563])).
% 8.41/3.06  tff(c_10008, plain, (![B_816]: (r2_hidden(k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), B_816) | ~r1_tarski('#skF_8', B_816))), inference(resolution, [status(thm)], [c_6855, c_9745])).
% 8.41/3.06  tff(c_10396, plain, (![B_849]: (~r1_tarski(B_849, k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11')) | ~r1_tarski('#skF_8', B_849))), inference(resolution, [status(thm)], [c_10008, c_32])).
% 8.41/3.06  tff(c_10436, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_10396])).
% 8.41/3.06  tff(c_10596, plain, (~r1_tarski('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10587, c_10436])).
% 8.41/3.06  tff(c_10608, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9677, c_10596])).
% 8.41/3.06  tff(c_10610, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_10563])).
% 8.41/3.06  tff(c_10664, plain, (![A_863, B_864, C_865, D_866]: (k5_mcart_1(A_863, B_864, C_865, D_866)=k1_mcart_1(k1_mcart_1(D_866)) | ~m1_subset_1(D_866, k3_zfmisc_1(A_863, B_864, C_865)) | k1_xboole_0=C_865 | k1_xboole_0=B_864 | k1_xboole_0=A_863)), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.41/3.06  tff(c_10667, plain, (k1_mcart_1(k1_mcart_1('#skF_11'))=k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_10664])).
% 8.41/3.06  tff(c_10670, plain, (k1_mcart_1(k1_mcart_1('#skF_11'))=k5_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_10610, c_10667])).
% 8.41/3.06  tff(c_11064, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_10670])).
% 8.41/3.06  tff(c_11091, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11064, c_12])).
% 8.41/3.06  tff(c_11093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9931, c_11091])).
% 8.41/3.06  tff(c_11095, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_10670])).
% 8.41/3.06  tff(c_10845, plain, (![A_873, B_874, C_875, D_876]: (k6_mcart_1(A_873, B_874, C_875, D_876)=k2_mcart_1(k1_mcart_1(D_876)) | ~m1_subset_1(D_876, k3_zfmisc_1(A_873, B_874, C_875)) | k1_xboole_0=C_875 | k1_xboole_0=B_874 | k1_xboole_0=A_873)), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.41/3.06  tff(c_10848, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_10845])).
% 8.41/3.06  tff(c_10851, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11') | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_10610, c_10848])).
% 8.41/3.06  tff(c_11180, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11') | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_11095, c_10851])).
% 8.41/3.06  tff(c_11181, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_11180])).
% 8.41/3.06  tff(c_9676, plain, (r1_tarski('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_9666])).
% 8.41/3.06  tff(c_9857, plain, (![A_802, C_803, B_804]: (r2_hidden(k2_mcart_1(A_802), C_803) | ~r2_hidden(A_802, k2_zfmisc_1(B_804, C_803)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.41/3.06  tff(c_10069, plain, (![A_822, C_823, A_824, B_825]: (r2_hidden(k2_mcart_1(A_822), C_823) | ~r2_hidden(A_822, k3_zfmisc_1(A_824, B_825, C_823)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_9857])).
% 8.41/3.06  tff(c_10091, plain, (r2_hidden(k2_mcart_1('#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_48, c_10069])).
% 8.41/3.06  tff(c_10117, plain, (![B_828]: (r2_hidden(k2_mcart_1('#skF_11'), B_828) | ~r1_tarski('#skF_10', B_828))), inference(resolution, [status(thm)], [c_10091, c_6])).
% 8.41/3.06  tff(c_10852, plain, (![B_877, B_878]: (r2_hidden(k2_mcart_1('#skF_11'), B_877) | ~r1_tarski(B_878, B_877) | ~r1_tarski('#skF_10', B_878))), inference(resolution, [status(thm)], [c_10117, c_6])).
% 8.41/3.06  tff(c_10878, plain, (r2_hidden(k2_mcart_1('#skF_11'), '#skF_7') | ~r1_tarski('#skF_10', '#skF_10')), inference(resolution, [status(thm)], [c_9676, c_10852])).
% 8.41/3.06  tff(c_10897, plain, (r2_hidden(k2_mcart_1('#skF_11'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_9706, c_10878])).
% 8.41/3.06  tff(c_10925, plain, (![B_879]: (r2_hidden(k2_mcart_1('#skF_11'), B_879) | ~r1_tarski('#skF_7', B_879))), inference(resolution, [status(thm)], [c_10897, c_6])).
% 8.41/3.06  tff(c_11004, plain, (![B_885]: (~r1_tarski(B_885, k2_mcart_1('#skF_11')) | ~r1_tarski('#skF_7', B_885))), inference(resolution, [status(thm)], [c_10925, c_32])).
% 8.41/3.06  tff(c_11059, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_11004])).
% 8.41/3.06  tff(c_11185, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11181, c_11059])).
% 8.41/3.06  tff(c_11214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9706, c_11185])).
% 8.41/3.06  tff(c_11215, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11')), inference(splitRight, [status(thm)], [c_11180])).
% 8.41/3.06  tff(c_9842, plain, (![A_799, B_800, C_801]: (r2_hidden(k1_mcart_1(A_799), B_800) | ~r2_hidden(A_799, k2_zfmisc_1(B_800, C_801)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.41/3.06  tff(c_12084, plain, (![A_953, A_954, B_955, C_956]: (r2_hidden(k1_mcart_1(A_953), k2_zfmisc_1(A_954, B_955)) | ~r2_hidden(A_953, k3_zfmisc_1(A_954, B_955, C_956)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_9842])).
% 8.41/3.06  tff(c_12137, plain, (r2_hidden(k1_mcart_1('#skF_11'), k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_48, c_12084])).
% 8.41/3.06  tff(c_12140, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_11')), '#skF_9')), inference(resolution, [status(thm)], [c_12137, c_36])).
% 8.41/3.06  tff(c_12152, plain, (r2_hidden(k6_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_11'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11215, c_12140])).
% 8.41/3.06  tff(c_12154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9652, c_12152])).
% 8.41/3.06  tff(c_12155, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_9921])).
% 8.41/3.06  tff(c_13561, plain, (![B_1039, C_1040]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1039, C_1040))), C_1040) | v1_xboole_0(k2_zfmisc_1(B_1039, C_1040)))), inference(resolution, [status(thm)], [c_4, c_9857])).
% 8.41/3.06  tff(c_13592, plain, (![C_1040, B_1039]: (~v1_xboole_0(C_1040) | v1_xboole_0(k2_zfmisc_1(B_1039, C_1040)))), inference(resolution, [status(thm)], [c_13561, c_2])).
% 8.41/3.06  tff(c_14185, plain, (![A_1075, A_1076, B_1077, C_1078]: (r2_hidden(k1_mcart_1(A_1075), k2_zfmisc_1(A_1076, B_1077)) | ~r2_hidden(A_1075, k3_zfmisc_1(A_1076, B_1077, C_1078)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_9842])).
% 8.41/3.06  tff(c_14234, plain, (r2_hidden(k1_mcart_1('#skF_11'), k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_48, c_14185])).
% 8.41/3.06  tff(c_14252, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_14234, c_2])).
% 8.41/3.07  tff(c_14258, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_13592, c_14252])).
% 8.41/3.07  tff(c_14263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12155, c_14258])).
% 8.41/3.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/3.07  
% 8.41/3.07  Inference rules
% 8.41/3.07  ----------------------
% 8.41/3.07  #Ref     : 0
% 8.41/3.07  #Sup     : 3030
% 8.41/3.07  #Fact    : 0
% 8.41/3.07  #Define  : 0
% 8.41/3.07  #Split   : 108
% 8.41/3.07  #Chain   : 0
% 8.41/3.07  #Close   : 0
% 8.41/3.07  
% 8.41/3.07  Ordering : KBO
% 8.41/3.07  
% 8.41/3.07  Simplification rules
% 8.41/3.07  ----------------------
% 8.41/3.07  #Subsume      : 807
% 8.41/3.07  #Demod        : 830
% 8.41/3.07  #Tautology    : 446
% 8.41/3.07  #SimpNegUnit  : 73
% 8.41/3.07  #BackRed      : 307
% 8.41/3.07  
% 8.41/3.07  #Partial instantiations: 0
% 8.41/3.07  #Strategies tried      : 1
% 8.41/3.07  
% 8.41/3.07  Timing (in seconds)
% 8.41/3.07  ----------------------
% 8.41/3.07  Preprocessing        : 0.32
% 8.41/3.07  Parsing              : 0.16
% 8.41/3.07  CNF conversion       : 0.03
% 8.41/3.07  Main loop            : 1.91
% 8.41/3.07  Inferencing          : 0.59
% 8.41/3.07  Reduction            : 0.62
% 8.41/3.07  Demodulation         : 0.39
% 8.41/3.07  BG Simplification    : 0.06
% 8.41/3.07  Subsumption          : 0.46
% 8.41/3.07  Abstraction          : 0.07
% 8.41/3.07  MUC search           : 0.00
% 8.41/3.07  Cooper               : 0.00
% 8.41/3.07  Total                : 2.29
% 8.41/3.07  Index Insertion      : 0.00
% 8.41/3.07  Index Deletion       : 0.00
% 8.41/3.07  Index Matching       : 0.00
% 8.41/3.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
