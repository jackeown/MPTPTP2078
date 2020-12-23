%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:04 EST 2020

% Result     : Theorem 14.73s
% Output     : CNFRefutation 14.73s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 435 expanded)
%              Number of leaves         :   34 ( 160 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 (1437 expanded)
%              Number of equality atoms :  115 ( 677 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_133,negated_conjecture,(
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

tff(f_109,axiom,(
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

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_543,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( k7_mcart_1(A_140,B_141,C_142,D_143) = k2_mcart_1(D_143)
      | ~ m1_subset_1(D_143,k3_zfmisc_1(A_140,B_141,C_142))
      | k1_xboole_0 = C_142
      | k1_xboole_0 = B_141
      | k1_xboole_0 = A_140 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_583,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_543])).

tff(c_596,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_44,c_583])).

tff(c_42,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_597,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_42])).

tff(c_28,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( m1_subset_1(k7_mcart_1(A_22,B_23,C_24,D_25),C_24)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_601,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_28])).

tff(c_605,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_601])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13) = k3_zfmisc_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_421,plain,(
    ! [C_129,A_130,B_131] :
      ( k4_tarski(k1_mcart_1(C_129),k2_mcart_1(C_129)) = C_129
      | ~ m1_subset_1(C_129,k2_zfmisc_1(A_130,B_131))
      | k1_xboole_0 = B_131
      | k1_xboole_0 = A_130 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12993,plain,(
    ! [C_790,A_791,B_792,C_793] :
      ( k4_tarski(k1_mcart_1(C_790),k2_mcart_1(C_790)) = C_790
      | ~ m1_subset_1(C_790,k3_zfmisc_1(A_791,B_792,C_793))
      | k1_xboole_0 = C_793
      | k2_zfmisc_1(A_791,B_792) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_421])).

tff(c_13075,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_12993])).

tff(c_13106,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_13075])).

tff(c_13107,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_13106])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_13127,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_13107,c_4])).

tff(c_13140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_13127])).

tff(c_13141,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13106])).

tff(c_351,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( m1_subset_1(k5_mcart_1(A_115,B_116,C_117,D_118),A_115)
      | ~ m1_subset_1(D_118,k3_zfmisc_1(A_115,B_116,C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [B_5,A_4] :
      ( v1_xboole_0(B_5)
      | ~ m1_subset_1(B_5,A_4)
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3097,plain,(
    ! [A_309,B_310,C_311,D_312] :
      ( v1_xboole_0(k5_mcart_1(A_309,B_310,C_311,D_312))
      | ~ v1_xboole_0(A_309)
      | ~ m1_subset_1(D_312,k3_zfmisc_1(A_309,B_310,C_311)) ) ),
    inference(resolution,[status(thm)],[c_351,c_16])).

tff(c_3228,plain,
    ( v1_xboole_0(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_3097])).

tff(c_3229,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3228])).

tff(c_612,plain,(
    ! [A_144,B_145,C_146,D_147] :
      ( k5_mcart_1(A_144,B_145,C_146,D_147) = k1_mcart_1(k1_mcart_1(D_147))
      | ~ m1_subset_1(D_147,k3_zfmisc_1(A_144,B_145,C_146))
      | k1_xboole_0 = C_146
      | k1_xboole_0 = B_145
      | k1_xboole_0 = A_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_652,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_612])).

tff(c_665,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_44,c_652])).

tff(c_78,plain,(
    ! [B_60,A_61] :
      ( v1_xboole_0(B_60)
      | ~ m1_subset_1(B_60,A_61)
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_86,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_78])).

tff(c_87,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_147,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden(k1_mcart_1(A_73),B_74)
      | ~ r2_hidden(A_73,k2_zfmisc_1(B_74,C_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1102,plain,(
    ! [A_177,A_178,B_179,C_180] :
      ( r2_hidden(k1_mcart_1(A_177),k2_zfmisc_1(A_178,B_179))
      | ~ r2_hidden(A_177,k3_zfmisc_1(A_178,B_179,C_180)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_147])).

tff(c_21991,plain,(
    ! [A_1176,A_1177,B_1178,C_1179] :
      ( r2_hidden(k1_mcart_1(A_1176),k2_zfmisc_1(A_1177,B_1178))
      | v1_xboole_0(k3_zfmisc_1(A_1177,B_1178,C_1179))
      | ~ m1_subset_1(A_1176,k3_zfmisc_1(A_1177,B_1178,C_1179)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1102])).

tff(c_22145,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_21991])).

tff(c_22203,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_22145])).

tff(c_32,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden(k1_mcart_1(A_26),B_27)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22207,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_22203,c_32])).

tff(c_22214,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_22207])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( m1_subset_1(B_5,A_4)
      | ~ r2_hidden(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22224,plain,
    ( m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22214,c_10])).

tff(c_22227,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3229,c_22224])).

tff(c_315,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( m1_subset_1(k6_mcart_1(A_105,B_106,C_107,D_108),B_106)
      | ~ m1_subset_1(D_108,k3_zfmisc_1(A_105,B_106,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2838,plain,(
    ! [A_299,B_300,C_301,D_302] :
      ( v1_xboole_0(k6_mcart_1(A_299,B_300,C_301,D_302))
      | ~ v1_xboole_0(B_300)
      | ~ m1_subset_1(D_302,k3_zfmisc_1(A_299,B_300,C_301)) ) ),
    inference(resolution,[status(thm)],[c_315,c_16])).

tff(c_2954,plain,
    ( v1_xboole_0(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_2838])).

tff(c_2955,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2954])).

tff(c_748,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k6_mcart_1(A_150,B_151,C_152,D_153) = k2_mcart_1(k1_mcart_1(D_153))
      | ~ m1_subset_1(D_153,k3_zfmisc_1(A_150,B_151,C_152))
      | k1_xboole_0 = C_152
      | k1_xboole_0 = B_151
      | k1_xboole_0 = A_150 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_792,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_52,c_748])).

tff(c_806,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_44,c_792])).

tff(c_30,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(k2_mcart_1(A_26),C_28)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22205,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22203,c_30])).

tff(c_22212,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_22205])).

tff(c_22218,plain,
    ( m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22212,c_10])).

tff(c_22221,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_2955,c_22218])).

tff(c_13142,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_13106])).

tff(c_22215,plain,
    ( m1_subset_1(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22203,c_10])).

tff(c_22236,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_22215])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22253,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22236,c_2])).

tff(c_22264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13142,c_22253])).

tff(c_22265,plain,(
    m1_subset_1(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_22215])).

tff(c_34,plain,(
    ! [C_32,A_29,B_30] :
      ( k4_tarski(k1_mcart_1(C_32),k2_mcart_1(C_32)) = C_32
      | ~ m1_subset_1(C_32,k2_zfmisc_1(A_29,B_30))
      | k1_xboole_0 = B_30
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22272,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22265,c_34])).

tff(c_22283,plain,
    ( k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_806,c_22272])).

tff(c_22284,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46,c_22283])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] : k4_tarski(k4_tarski(A_8,B_9),C_10) = k3_mcart_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22861,plain,(
    ! [C_1201] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_1201) = k4_tarski(k1_mcart_1('#skF_5'),C_1201) ),
    inference(superposition,[status(thm),theory(equality)],[c_22284,c_20])).

tff(c_50,plain,(
    ! [H_51,F_45,G_49] :
      ( H_51 = '#skF_4'
      | k3_mcart_1(F_45,G_49,H_51) != '#skF_5'
      | ~ m1_subset_1(H_51,'#skF_3')
      | ~ m1_subset_1(G_49,'#skF_2')
      | ~ m1_subset_1(F_45,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_22874,plain,(
    ! [C_1201] :
      ( C_1201 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_1201) != '#skF_5'
      | ~ m1_subset_1(C_1201,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22861,c_50])).

tff(c_22887,plain,(
    ! [C_1202] :
      ( C_1202 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_1202) != '#skF_5'
      | ~ m1_subset_1(C_1202,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22227,c_22221,c_22874])).

tff(c_22890,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13141,c_22887])).

tff(c_22897,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_22890])).

tff(c_22899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_597,c_22897])).

tff(c_22901,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3228])).

tff(c_22904,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22901,c_2])).

tff(c_22908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_22904])).

tff(c_22910,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2954])).

tff(c_22913,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22910,c_2])).

tff(c_22917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_22913])).

tff(c_22918,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_22923,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22918,c_2])).

tff(c_22929,plain,(
    '#skF_5' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22923,c_48])).

tff(c_22928,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22923,c_46])).

tff(c_22927,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22923,c_44])).

tff(c_22919,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_22942,plain,(
    ! [A_1206] :
      ( A_1206 = '#skF_5'
      | ~ v1_xboole_0(A_1206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22923,c_2])).

tff(c_22949,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_22919,c_22942])).

tff(c_23075,plain,(
    ! [A_1228,B_1229,C_1230] : k2_zfmisc_1(k2_zfmisc_1(A_1228,B_1229),C_1230) = k3_zfmisc_1(A_1228,B_1229,C_1230) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22980,plain,(
    ! [B_3,A_2] :
      ( B_3 = '#skF_5'
      | A_2 = '#skF_5'
      | k2_zfmisc_1(A_2,B_3) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22923,c_22923,c_22923,c_4])).

tff(c_24360,plain,(
    ! [C_1352,A_1353,B_1354] :
      ( C_1352 = '#skF_5'
      | k2_zfmisc_1(A_1353,B_1354) = '#skF_5'
      | k3_zfmisc_1(A_1353,B_1354,C_1352) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23075,c_22980])).

tff(c_24375,plain,
    ( '#skF_5' = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_22949,c_24360])).

tff(c_24385,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_22927,c_24375])).

tff(c_24401,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_24385,c_22980])).

tff(c_24410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22929,c_22928,c_24401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.73/7.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.73/7.13  
% 14.73/7.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.73/7.13  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 14.73/7.13  
% 14.73/7.13  %Foreground sorts:
% 14.73/7.13  
% 14.73/7.13  
% 14.73/7.13  %Background operators:
% 14.73/7.13  
% 14.73/7.13  
% 14.73/7.13  %Foreground operators:
% 14.73/7.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.73/7.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.73/7.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.73/7.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.73/7.13  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 14.73/7.13  tff('#skF_5', type, '#skF_5': $i).
% 14.73/7.13  tff('#skF_2', type, '#skF_2': $i).
% 14.73/7.13  tff('#skF_3', type, '#skF_3': $i).
% 14.73/7.13  tff('#skF_1', type, '#skF_1': $i).
% 14.73/7.13  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 14.73/7.13  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 14.73/7.13  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 14.73/7.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.73/7.13  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 14.73/7.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.73/7.13  tff('#skF_4', type, '#skF_4': $i).
% 14.73/7.13  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 14.73/7.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.73/7.13  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 14.73/7.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.73/7.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.73/7.13  
% 14.73/7.15  tff(f_133, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 14.73/7.15  tff(f_109, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 14.73/7.15  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 14.73/7.15  tff(f_58, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 14.73/7.15  tff(f_89, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_mcart_1)).
% 14.73/7.15  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.73/7.15  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 14.73/7.15  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 14.73/7.15  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 14.73/7.15  tff(f_76, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 14.73/7.15  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 14.73/7.15  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 14.73/7.15  tff(f_56, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 14.73/7.15  tff(c_46, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.73/7.15  tff(c_48, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.73/7.15  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.73/7.15  tff(c_52, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.73/7.15  tff(c_543, plain, (![A_140, B_141, C_142, D_143]: (k7_mcart_1(A_140, B_141, C_142, D_143)=k2_mcart_1(D_143) | ~m1_subset_1(D_143, k3_zfmisc_1(A_140, B_141, C_142)) | k1_xboole_0=C_142 | k1_xboole_0=B_141 | k1_xboole_0=A_140)), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.73/7.15  tff(c_583, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_52, c_543])).
% 14.73/7.15  tff(c_596, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_46, c_44, c_583])).
% 14.73/7.15  tff(c_42, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.73/7.15  tff(c_597, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_596, c_42])).
% 14.73/7.15  tff(c_28, plain, (![A_22, B_23, C_24, D_25]: (m1_subset_1(k7_mcart_1(A_22, B_23, C_24, D_25), C_24) | ~m1_subset_1(D_25, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.73/7.15  tff(c_601, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_596, c_28])).
% 14.73/7.15  tff(c_605, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_601])).
% 14.73/7.15  tff(c_22, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.73/7.15  tff(c_421, plain, (![C_129, A_130, B_131]: (k4_tarski(k1_mcart_1(C_129), k2_mcart_1(C_129))=C_129 | ~m1_subset_1(C_129, k2_zfmisc_1(A_130, B_131)) | k1_xboole_0=B_131 | k1_xboole_0=A_130)), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.73/7.15  tff(c_12993, plain, (![C_790, A_791, B_792, C_793]: (k4_tarski(k1_mcart_1(C_790), k2_mcart_1(C_790))=C_790 | ~m1_subset_1(C_790, k3_zfmisc_1(A_791, B_792, C_793)) | k1_xboole_0=C_793 | k2_zfmisc_1(A_791, B_792)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_421])).
% 14.73/7.15  tff(c_13075, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_12993])).
% 14.73/7.15  tff(c_13106, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_13075])).
% 14.73/7.15  tff(c_13107, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_13106])).
% 14.73/7.15  tff(c_4, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.73/7.15  tff(c_13127, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_13107, c_4])).
% 14.73/7.15  tff(c_13140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_46, c_13127])).
% 14.73/7.15  tff(c_13141, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_13106])).
% 14.73/7.15  tff(c_351, plain, (![A_115, B_116, C_117, D_118]: (m1_subset_1(k5_mcart_1(A_115, B_116, C_117, D_118), A_115) | ~m1_subset_1(D_118, k3_zfmisc_1(A_115, B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.73/7.15  tff(c_16, plain, (![B_5, A_4]: (v1_xboole_0(B_5) | ~m1_subset_1(B_5, A_4) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.73/7.15  tff(c_3097, plain, (![A_309, B_310, C_311, D_312]: (v1_xboole_0(k5_mcart_1(A_309, B_310, C_311, D_312)) | ~v1_xboole_0(A_309) | ~m1_subset_1(D_312, k3_zfmisc_1(A_309, B_310, C_311)))), inference(resolution, [status(thm)], [c_351, c_16])).
% 14.73/7.15  tff(c_3228, plain, (v1_xboole_0(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_3097])).
% 14.73/7.15  tff(c_3229, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_3228])).
% 14.73/7.15  tff(c_612, plain, (![A_144, B_145, C_146, D_147]: (k5_mcart_1(A_144, B_145, C_146, D_147)=k1_mcart_1(k1_mcart_1(D_147)) | ~m1_subset_1(D_147, k3_zfmisc_1(A_144, B_145, C_146)) | k1_xboole_0=C_146 | k1_xboole_0=B_145 | k1_xboole_0=A_144)), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.73/7.15  tff(c_652, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_52, c_612])).
% 14.73/7.15  tff(c_665, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_46, c_44, c_652])).
% 14.73/7.15  tff(c_78, plain, (![B_60, A_61]: (v1_xboole_0(B_60) | ~m1_subset_1(B_60, A_61) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.73/7.15  tff(c_86, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_78])).
% 14.73/7.15  tff(c_87, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_86])).
% 14.73/7.15  tff(c_18, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.73/7.15  tff(c_147, plain, (![A_73, B_74, C_75]: (r2_hidden(k1_mcart_1(A_73), B_74) | ~r2_hidden(A_73, k2_zfmisc_1(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.73/7.15  tff(c_1102, plain, (![A_177, A_178, B_179, C_180]: (r2_hidden(k1_mcart_1(A_177), k2_zfmisc_1(A_178, B_179)) | ~r2_hidden(A_177, k3_zfmisc_1(A_178, B_179, C_180)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_147])).
% 14.73/7.15  tff(c_21991, plain, (![A_1176, A_1177, B_1178, C_1179]: (r2_hidden(k1_mcart_1(A_1176), k2_zfmisc_1(A_1177, B_1178)) | v1_xboole_0(k3_zfmisc_1(A_1177, B_1178, C_1179)) | ~m1_subset_1(A_1176, k3_zfmisc_1(A_1177, B_1178, C_1179)))), inference(resolution, [status(thm)], [c_18, c_1102])).
% 14.73/7.15  tff(c_22145, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_21991])).
% 14.73/7.15  tff(c_22203, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_87, c_22145])).
% 14.73/7.15  tff(c_32, plain, (![A_26, B_27, C_28]: (r2_hidden(k1_mcart_1(A_26), B_27) | ~r2_hidden(A_26, k2_zfmisc_1(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.73/7.15  tff(c_22207, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_22203, c_32])).
% 14.73/7.15  tff(c_22214, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_665, c_22207])).
% 14.73/7.15  tff(c_10, plain, (![B_5, A_4]: (m1_subset_1(B_5, A_4) | ~r2_hidden(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.73/7.15  tff(c_22224, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22214, c_10])).
% 14.73/7.15  tff(c_22227, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3229, c_22224])).
% 14.73/7.15  tff(c_315, plain, (![A_105, B_106, C_107, D_108]: (m1_subset_1(k6_mcart_1(A_105, B_106, C_107, D_108), B_106) | ~m1_subset_1(D_108, k3_zfmisc_1(A_105, B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.73/7.15  tff(c_2838, plain, (![A_299, B_300, C_301, D_302]: (v1_xboole_0(k6_mcart_1(A_299, B_300, C_301, D_302)) | ~v1_xboole_0(B_300) | ~m1_subset_1(D_302, k3_zfmisc_1(A_299, B_300, C_301)))), inference(resolution, [status(thm)], [c_315, c_16])).
% 14.73/7.15  tff(c_2954, plain, (v1_xboole_0(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_2838])).
% 14.73/7.15  tff(c_2955, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2954])).
% 14.73/7.15  tff(c_748, plain, (![A_150, B_151, C_152, D_153]: (k6_mcart_1(A_150, B_151, C_152, D_153)=k2_mcart_1(k1_mcart_1(D_153)) | ~m1_subset_1(D_153, k3_zfmisc_1(A_150, B_151, C_152)) | k1_xboole_0=C_152 | k1_xboole_0=B_151 | k1_xboole_0=A_150)), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.73/7.15  tff(c_792, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_52, c_748])).
% 14.73/7.15  tff(c_806, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_46, c_44, c_792])).
% 14.73/7.15  tff(c_30, plain, (![A_26, C_28, B_27]: (r2_hidden(k2_mcart_1(A_26), C_28) | ~r2_hidden(A_26, k2_zfmisc_1(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.73/7.15  tff(c_22205, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_22203, c_30])).
% 14.73/7.15  tff(c_22212, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_806, c_22205])).
% 14.73/7.15  tff(c_22218, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_22212, c_10])).
% 14.73/7.15  tff(c_22221, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_2955, c_22218])).
% 14.73/7.15  tff(c_13142, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_13106])).
% 14.73/7.15  tff(c_22215, plain, (m1_subset_1(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22203, c_10])).
% 14.73/7.15  tff(c_22236, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_22215])).
% 14.73/7.15  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.73/7.15  tff(c_22253, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22236, c_2])).
% 14.73/7.15  tff(c_22264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13142, c_22253])).
% 14.73/7.15  tff(c_22265, plain, (m1_subset_1(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_22215])).
% 14.73/7.15  tff(c_34, plain, (![C_32, A_29, B_30]: (k4_tarski(k1_mcart_1(C_32), k2_mcart_1(C_32))=C_32 | ~m1_subset_1(C_32, k2_zfmisc_1(A_29, B_30)) | k1_xboole_0=B_30 | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.73/7.15  tff(c_22272, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22265, c_34])).
% 14.73/7.15  tff(c_22283, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_665, c_806, c_22272])).
% 14.73/7.15  tff(c_22284, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_46, c_22283])).
% 14.73/7.15  tff(c_20, plain, (![A_8, B_9, C_10]: (k4_tarski(k4_tarski(A_8, B_9), C_10)=k3_mcart_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.73/7.15  tff(c_22861, plain, (![C_1201]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_1201)=k4_tarski(k1_mcart_1('#skF_5'), C_1201))), inference(superposition, [status(thm), theory('equality')], [c_22284, c_20])).
% 14.73/7.15  tff(c_50, plain, (![H_51, F_45, G_49]: (H_51='#skF_4' | k3_mcart_1(F_45, G_49, H_51)!='#skF_5' | ~m1_subset_1(H_51, '#skF_3') | ~m1_subset_1(G_49, '#skF_2') | ~m1_subset_1(F_45, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 14.73/7.15  tff(c_22874, plain, (![C_1201]: (C_1201='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_1201)!='#skF_5' | ~m1_subset_1(C_1201, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22861, c_50])).
% 14.73/7.15  tff(c_22887, plain, (![C_1202]: (C_1202='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_1202)!='#skF_5' | ~m1_subset_1(C_1202, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22227, c_22221, c_22874])).
% 14.73/7.15  tff(c_22890, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13141, c_22887])).
% 14.73/7.15  tff(c_22897, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_605, c_22890])).
% 14.73/7.15  tff(c_22899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_597, c_22897])).
% 14.73/7.15  tff(c_22901, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_3228])).
% 14.73/7.15  tff(c_22904, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22901, c_2])).
% 14.73/7.15  tff(c_22908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_22904])).
% 14.73/7.15  tff(c_22910, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_2954])).
% 14.73/7.15  tff(c_22913, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_22910, c_2])).
% 14.73/7.15  tff(c_22917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_22913])).
% 14.73/7.15  tff(c_22918, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 14.73/7.15  tff(c_22923, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_22918, c_2])).
% 14.73/7.15  tff(c_22929, plain, ('#skF_5'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22923, c_48])).
% 14.73/7.15  tff(c_22928, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22923, c_46])).
% 14.73/7.15  tff(c_22927, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22923, c_44])).
% 14.73/7.15  tff(c_22919, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_86])).
% 14.73/7.15  tff(c_22942, plain, (![A_1206]: (A_1206='#skF_5' | ~v1_xboole_0(A_1206))), inference(demodulation, [status(thm), theory('equality')], [c_22923, c_2])).
% 14.73/7.15  tff(c_22949, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_22919, c_22942])).
% 14.73/7.15  tff(c_23075, plain, (![A_1228, B_1229, C_1230]: (k2_zfmisc_1(k2_zfmisc_1(A_1228, B_1229), C_1230)=k3_zfmisc_1(A_1228, B_1229, C_1230))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.73/7.15  tff(c_22980, plain, (![B_3, A_2]: (B_3='#skF_5' | A_2='#skF_5' | k2_zfmisc_1(A_2, B_3)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22923, c_22923, c_22923, c_4])).
% 14.73/7.15  tff(c_24360, plain, (![C_1352, A_1353, B_1354]: (C_1352='#skF_5' | k2_zfmisc_1(A_1353, B_1354)='#skF_5' | k3_zfmisc_1(A_1353, B_1354, C_1352)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_23075, c_22980])).
% 14.73/7.15  tff(c_24375, plain, ('#skF_5'='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_22949, c_24360])).
% 14.73/7.15  tff(c_24385, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_22927, c_24375])).
% 14.73/7.15  tff(c_24401, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_24385, c_22980])).
% 14.73/7.15  tff(c_24410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22929, c_22928, c_24401])).
% 14.73/7.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.73/7.15  
% 14.73/7.15  Inference rules
% 14.73/7.15  ----------------------
% 14.73/7.15  #Ref     : 0
% 14.73/7.15  #Sup     : 6392
% 14.73/7.15  #Fact    : 0
% 14.73/7.15  #Define  : 0
% 14.73/7.15  #Split   : 19
% 14.73/7.15  #Chain   : 0
% 14.73/7.15  #Close   : 0
% 14.73/7.15  
% 14.73/7.15  Ordering : KBO
% 14.73/7.15  
% 14.73/7.15  Simplification rules
% 14.73/7.15  ----------------------
% 14.73/7.15  #Subsume      : 1146
% 14.73/7.15  #Demod        : 1059
% 14.73/7.15  #Tautology    : 476
% 14.73/7.15  #SimpNegUnit  : 161
% 14.73/7.15  #BackRed      : 10
% 14.73/7.15  
% 14.73/7.15  #Partial instantiations: 0
% 14.73/7.15  #Strategies tried      : 1
% 14.73/7.15  
% 14.73/7.15  Timing (in seconds)
% 14.73/7.15  ----------------------
% 14.73/7.15  Preprocessing        : 0.32
% 14.73/7.15  Parsing              : 0.17
% 14.73/7.15  CNF conversion       : 0.02
% 14.73/7.15  Main loop            : 5.98
% 14.73/7.15  Inferencing          : 1.37
% 14.73/7.15  Reduction            : 1.10
% 14.73/7.15  Demodulation         : 0.70
% 14.73/7.15  BG Simplification    : 0.17
% 14.73/7.15  Subsumption          : 2.96
% 14.73/7.15  Abstraction          : 0.23
% 14.73/7.15  MUC search           : 0.00
% 14.73/7.15  Cooper               : 0.00
% 14.73/7.15  Total                : 6.35
% 14.73/7.15  Index Insertion      : 0.00
% 14.73/7.15  Index Deletion       : 0.00
% 14.73/7.15  Index Matching       : 0.00
% 14.73/7.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
