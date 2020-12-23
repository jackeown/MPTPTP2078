%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:59 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 251 expanded)
%              Number of leaves         :   35 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          :  196 ( 842 expanded)
%              Number of equality atoms :   97 ( 403 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
                       => D = G ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k6_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_28,axiom,(
    ! [A,B] : ~ v1_xboole_0(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_zfmisc_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_575,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k7_mcart_1(A_145,B_146,C_147,D_148) = k2_mcart_1(D_148)
      | ~ m1_subset_1(D_148,k3_zfmisc_1(A_145,B_146,C_147))
      | k1_xboole_0 = C_147
      | k1_xboole_0 = B_146
      | k1_xboole_0 = A_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_598,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_575])).

tff(c_603,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_598])).

tff(c_28,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( m1_subset_1(k7_mcart_1(A_19,B_20,C_21,D_22),C_21)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_19,B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_607,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_28])).

tff(c_611,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_607])).

tff(c_93,plain,(
    ! [B_62,A_63] :
      ( v1_xboole_0(B_62)
      | ~ m1_subset_1(B_62,A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_103,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_177,plain,(
    ! [A_86,B_87,C_88] : k2_zfmisc_1(k2_zfmisc_1(A_86,B_87),C_88) = k3_zfmisc_1(A_86,B_87,C_88) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_199,plain,(
    ! [A_86,B_87,C_88] : v1_relat_1(k3_zfmisc_1(A_86,B_87,C_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_22])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r2_hidden(B_8,A_7)
      | ~ m1_subset_1(B_8,A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_250,plain,(
    ! [A_96,B_97] :
      ( k4_tarski(k1_mcart_1(A_96),k2_mcart_1(A_96)) = A_96
      | ~ r2_hidden(A_96,B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_534,plain,(
    ! [B_142,A_143] :
      ( k4_tarski(k1_mcart_1(B_142),k2_mcart_1(B_142)) = B_142
      | ~ v1_relat_1(A_143)
      | ~ m1_subset_1(B_142,A_143)
      | v1_xboole_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_14,c_250])).

tff(c_540,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_534])).

tff(c_545,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_540])).

tff(c_546,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_545])).

tff(c_44,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_628,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( k5_mcart_1(A_149,B_150,C_151,D_152) = k1_mcart_1(k1_mcart_1(D_152))
      | ~ m1_subset_1(D_152,k3_zfmisc_1(A_149,B_150,C_151))
      | k1_xboole_0 = C_151
      | k1_xboole_0 = B_150
      | k1_xboole_0 = A_149 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_651,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_628])).

tff(c_656,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_651])).

tff(c_32,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden(k1_mcart_1(A_23),B_24)
      | ~ r2_hidden(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_492,plain,(
    ! [A_131,A_132,B_133,C_134] :
      ( r2_hidden(k1_mcart_1(A_131),k2_zfmisc_1(A_132,B_133))
      | ~ r2_hidden(A_131,k3_zfmisc_1(A_132,B_133,C_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_32])).

tff(c_851,plain,(
    ! [B_180,A_181,B_182,C_183] :
      ( r2_hidden(k1_mcart_1(B_180),k2_zfmisc_1(A_181,B_182))
      | ~ m1_subset_1(B_180,k3_zfmisc_1(A_181,B_182,C_183))
      | v1_xboole_0(k3_zfmisc_1(A_181,B_182,C_183)) ) ),
    inference(resolution,[status(thm)],[c_14,c_492])).

tff(c_867,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_851])).

tff(c_879,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_867])).

tff(c_883,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_879,c_32])).

tff(c_893,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_883])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_950,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_893,c_20])).

tff(c_779,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k6_mcart_1(A_167,B_168,C_169,D_170) = k2_mcart_1(k1_mcart_1(D_170))
      | ~ m1_subset_1(D_170,k3_zfmisc_1(A_167,B_168,C_169))
      | k1_xboole_0 = C_169
      | k1_xboole_0 = B_168
      | k1_xboole_0 = A_167 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_802,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_779])).

tff(c_807,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_46,c_802])).

tff(c_30,plain,(
    ! [A_23,C_25,B_24] :
      ( r2_hidden(k2_mcart_1(A_23),C_25)
      | ~ r2_hidden(A_23,k2_zfmisc_1(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_885,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_879,c_30])).

tff(c_895,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_885])).

tff(c_957,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_895,c_20])).

tff(c_896,plain,(
    m1_subset_1(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_879,c_20])).

tff(c_36,plain,(
    ! [C_31,A_28,B_29] :
      ( k4_tarski(k1_mcart_1(C_31),k2_mcart_1(C_31)) = C_31
      | ~ m1_subset_1(C_31,k2_zfmisc_1(A_28,B_29))
      | k1_xboole_0 = B_29
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_929,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_896,c_36])).

tff(c_941,plain,
    ( k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_656,c_929])).

tff(c_942,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_941])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] : k4_tarski(k4_tarski(A_13,B_14),C_15) = k3_mcart_1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_996,plain,(
    ! [C_192] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_192) = k4_tarski(k1_mcart_1('#skF_5'),C_192) ),
    inference(superposition,[status(thm),theory(equality)],[c_942,c_24])).

tff(c_52,plain,(
    ! [G_48,F_44,H_50] :
      ( G_48 = '#skF_4'
      | k3_mcart_1(F_44,G_48,H_50) != '#skF_5'
      | ~ m1_subset_1(H_50,'#skF_3')
      | ~ m1_subset_1(G_48,'#skF_2')
      | ~ m1_subset_1(F_44,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1005,plain,(
    ! [C_192] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_192) != '#skF_5'
      | ~ m1_subset_1(C_192,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_52])).

tff(c_1012,plain,(
    ! [C_192] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_192) != '#skF_5'
      | ~ m1_subset_1(C_192,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_957,c_1005])).

tff(c_1015,plain,(
    ! [C_193] :
      ( k4_tarski(k1_mcart_1('#skF_5'),C_193) != '#skF_5'
      | ~ m1_subset_1(C_193,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1012])).

tff(c_1018,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_1015])).

tff(c_1022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_1018])).

tff(c_1024,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_26,plain,(
    ! [A_16,B_17,C_18] : k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18) = k3_zfmisc_1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(B_8,A_7)
      | ~ v1_xboole_0(B_8)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1452,plain,(
    ! [C_269,A_270,B_271] :
      ( k4_tarski(k1_mcart_1(C_269),k2_mcart_1(C_269)) = C_269
      | ~ m1_subset_1(C_269,k2_zfmisc_1(A_270,B_271))
      | k1_xboole_0 = B_271
      | k1_xboole_0 = A_270 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1466,plain,(
    ! [B_8,B_271,A_270] :
      ( k4_tarski(k1_mcart_1(B_8),k2_mcart_1(B_8)) = B_8
      | k1_xboole_0 = B_271
      | k1_xboole_0 = A_270
      | ~ v1_xboole_0(B_8)
      | ~ v1_xboole_0(k2_zfmisc_1(A_270,B_271)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1452])).

tff(c_1703,plain,(
    ! [A_302,B_303] :
      ( k1_xboole_0 = A_302
      | k1_xboole_0 = B_303
      | ~ v1_xboole_0(k2_zfmisc_1(A_302,B_303)) ) ),
    inference(splitLeft,[status(thm)],[c_1466])).

tff(c_1713,plain,(
    ! [A_304,B_305,C_306] :
      ( k2_zfmisc_1(A_304,B_305) = k1_xboole_0
      | k1_xboole_0 = C_306
      | ~ v1_xboole_0(k3_zfmisc_1(A_304,B_305,C_306)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1703])).

tff(c_1728,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1024,c_1713])).

tff(c_1734,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1728])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1766,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1734,c_4])).

tff(c_1787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48,c_1766])).

tff(c_1817,plain,(
    ! [B_311] :
      ( k4_tarski(k1_mcart_1(B_311),k2_mcart_1(B_311)) = B_311
      | ~ v1_xboole_0(B_311) ) ),
    inference(splitRight,[status(thm)],[c_1466])).

tff(c_2,plain,(
    ! [A_1,B_2] : ~ v1_xboole_0(k4_tarski(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1842,plain,(
    ! [B_312] :
      ( ~ v1_xboole_0(B_312)
      | ~ v1_xboole_0(B_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1817,c_2])).

tff(c_1846,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1024,c_1842])).

tff(c_1853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_1846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.62  
% 3.51/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.51/1.62  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.51/1.62  
% 3.51/1.62  %Foreground sorts:
% 3.51/1.62  
% 3.51/1.62  
% 3.51/1.62  %Background operators:
% 3.51/1.62  
% 3.51/1.62  
% 3.51/1.62  %Foreground operators:
% 3.51/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.51/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.51/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.62  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.51/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.51/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.51/1.62  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.51/1.62  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.51/1.62  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.51/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.62  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.51/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.51/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.51/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.51/1.62  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.51/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.62  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.51/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.51/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.62  
% 3.90/1.64  tff(f_133, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 3.90/1.64  tff(f_109, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.90/1.64  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 3.90/1.64  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.90/1.64  tff(f_60, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.90/1.64  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.90/1.64  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 3.90/1.64  tff(f_70, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.90/1.64  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.90/1.64  tff(f_89, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 3.90/1.64  tff(f_58, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.90/1.64  tff(f_34, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.90/1.64  tff(f_28, axiom, (![A, B]: ~v1_xboole_0(k4_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_zfmisc_1)).
% 3.90/1.64  tff(c_54, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.90/1.64  tff(c_50, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.90/1.64  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.90/1.64  tff(c_46, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.90/1.64  tff(c_575, plain, (![A_145, B_146, C_147, D_148]: (k7_mcart_1(A_145, B_146, C_147, D_148)=k2_mcart_1(D_148) | ~m1_subset_1(D_148, k3_zfmisc_1(A_145, B_146, C_147)) | k1_xboole_0=C_147 | k1_xboole_0=B_146 | k1_xboole_0=A_145)), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.90/1.64  tff(c_598, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_54, c_575])).
% 3.90/1.64  tff(c_603, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_46, c_598])).
% 3.90/1.64  tff(c_28, plain, (![A_19, B_20, C_21, D_22]: (m1_subset_1(k7_mcart_1(A_19, B_20, C_21, D_22), C_21) | ~m1_subset_1(D_22, k3_zfmisc_1(A_19, B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.90/1.64  tff(c_607, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_603, c_28])).
% 3.90/1.64  tff(c_611, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_607])).
% 3.90/1.64  tff(c_93, plain, (![B_62, A_63]: (v1_xboole_0(B_62) | ~m1_subset_1(B_62, A_63) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.90/1.64  tff(c_97, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_93])).
% 3.90/1.64  tff(c_103, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_97])).
% 3.90/1.64  tff(c_177, plain, (![A_86, B_87, C_88]: (k2_zfmisc_1(k2_zfmisc_1(A_86, B_87), C_88)=k3_zfmisc_1(A_86, B_87, C_88))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.90/1.64  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.90/1.64  tff(c_199, plain, (![A_86, B_87, C_88]: (v1_relat_1(k3_zfmisc_1(A_86, B_87, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_177, c_22])).
% 3.90/1.64  tff(c_14, plain, (![B_8, A_7]: (r2_hidden(B_8, A_7) | ~m1_subset_1(B_8, A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.90/1.64  tff(c_250, plain, (![A_96, B_97]: (k4_tarski(k1_mcart_1(A_96), k2_mcart_1(A_96))=A_96 | ~r2_hidden(A_96, B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.90/1.64  tff(c_534, plain, (![B_142, A_143]: (k4_tarski(k1_mcart_1(B_142), k2_mcart_1(B_142))=B_142 | ~v1_relat_1(A_143) | ~m1_subset_1(B_142, A_143) | v1_xboole_0(A_143))), inference(resolution, [status(thm)], [c_14, c_250])).
% 3.90/1.64  tff(c_540, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_534])).
% 3.90/1.64  tff(c_545, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_540])).
% 3.90/1.64  tff(c_546, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_103, c_545])).
% 3.90/1.64  tff(c_44, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.90/1.64  tff(c_628, plain, (![A_149, B_150, C_151, D_152]: (k5_mcart_1(A_149, B_150, C_151, D_152)=k1_mcart_1(k1_mcart_1(D_152)) | ~m1_subset_1(D_152, k3_zfmisc_1(A_149, B_150, C_151)) | k1_xboole_0=C_151 | k1_xboole_0=B_150 | k1_xboole_0=A_149)), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.90/1.64  tff(c_651, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_54, c_628])).
% 3.90/1.64  tff(c_656, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_46, c_651])).
% 3.90/1.64  tff(c_32, plain, (![A_23, B_24, C_25]: (r2_hidden(k1_mcart_1(A_23), B_24) | ~r2_hidden(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.90/1.64  tff(c_492, plain, (![A_131, A_132, B_133, C_134]: (r2_hidden(k1_mcart_1(A_131), k2_zfmisc_1(A_132, B_133)) | ~r2_hidden(A_131, k3_zfmisc_1(A_132, B_133, C_134)))), inference(superposition, [status(thm), theory('equality')], [c_177, c_32])).
% 3.90/1.64  tff(c_851, plain, (![B_180, A_181, B_182, C_183]: (r2_hidden(k1_mcart_1(B_180), k2_zfmisc_1(A_181, B_182)) | ~m1_subset_1(B_180, k3_zfmisc_1(A_181, B_182, C_183)) | v1_xboole_0(k3_zfmisc_1(A_181, B_182, C_183)))), inference(resolution, [status(thm)], [c_14, c_492])).
% 3.90/1.64  tff(c_867, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_851])).
% 3.90/1.64  tff(c_879, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_103, c_867])).
% 3.90/1.64  tff(c_883, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_879, c_32])).
% 3.90/1.64  tff(c_893, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_656, c_883])).
% 3.90/1.64  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.90/1.64  tff(c_950, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_893, c_20])).
% 3.90/1.64  tff(c_779, plain, (![A_167, B_168, C_169, D_170]: (k6_mcart_1(A_167, B_168, C_169, D_170)=k2_mcart_1(k1_mcart_1(D_170)) | ~m1_subset_1(D_170, k3_zfmisc_1(A_167, B_168, C_169)) | k1_xboole_0=C_169 | k1_xboole_0=B_168 | k1_xboole_0=A_167)), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.90/1.64  tff(c_802, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_54, c_779])).
% 3.90/1.64  tff(c_807, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_46, c_802])).
% 3.90/1.64  tff(c_30, plain, (![A_23, C_25, B_24]: (r2_hidden(k2_mcart_1(A_23), C_25) | ~r2_hidden(A_23, k2_zfmisc_1(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.90/1.64  tff(c_885, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_879, c_30])).
% 3.90/1.64  tff(c_895, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_807, c_885])).
% 3.90/1.64  tff(c_957, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_895, c_20])).
% 3.90/1.64  tff(c_896, plain, (m1_subset_1(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_879, c_20])).
% 3.90/1.64  tff(c_36, plain, (![C_31, A_28, B_29]: (k4_tarski(k1_mcart_1(C_31), k2_mcart_1(C_31))=C_31 | ~m1_subset_1(C_31, k2_zfmisc_1(A_28, B_29)) | k1_xboole_0=B_29 | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.90/1.64  tff(c_929, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_896, c_36])).
% 3.90/1.64  tff(c_941, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_807, c_656, c_929])).
% 3.90/1.64  tff(c_942, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_941])).
% 3.90/1.64  tff(c_24, plain, (![A_13, B_14, C_15]: (k4_tarski(k4_tarski(A_13, B_14), C_15)=k3_mcart_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.90/1.64  tff(c_996, plain, (![C_192]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_192)=k4_tarski(k1_mcart_1('#skF_5'), C_192))), inference(superposition, [status(thm), theory('equality')], [c_942, c_24])).
% 3.90/1.64  tff(c_52, plain, (![G_48, F_44, H_50]: (G_48='#skF_4' | k3_mcart_1(F_44, G_48, H_50)!='#skF_5' | ~m1_subset_1(H_50, '#skF_3') | ~m1_subset_1(G_48, '#skF_2') | ~m1_subset_1(F_44, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.90/1.64  tff(c_1005, plain, (![C_192]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_192)!='#skF_5' | ~m1_subset_1(C_192, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_996, c_52])).
% 3.90/1.64  tff(c_1012, plain, (![C_192]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_192)!='#skF_5' | ~m1_subset_1(C_192, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_950, c_957, c_1005])).
% 3.90/1.64  tff(c_1015, plain, (![C_193]: (k4_tarski(k1_mcart_1('#skF_5'), C_193)!='#skF_5' | ~m1_subset_1(C_193, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_1012])).
% 3.90/1.64  tff(c_1018, plain, (~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_546, c_1015])).
% 3.90/1.64  tff(c_1022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_611, c_1018])).
% 3.90/1.64  tff(c_1024, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_97])).
% 3.90/1.64  tff(c_26, plain, (![A_16, B_17, C_18]: (k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)=k3_zfmisc_1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.90/1.64  tff(c_16, plain, (![B_8, A_7]: (m1_subset_1(B_8, A_7) | ~v1_xboole_0(B_8) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.90/1.64  tff(c_1452, plain, (![C_269, A_270, B_271]: (k4_tarski(k1_mcart_1(C_269), k2_mcart_1(C_269))=C_269 | ~m1_subset_1(C_269, k2_zfmisc_1(A_270, B_271)) | k1_xboole_0=B_271 | k1_xboole_0=A_270)), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.90/1.64  tff(c_1466, plain, (![B_8, B_271, A_270]: (k4_tarski(k1_mcart_1(B_8), k2_mcart_1(B_8))=B_8 | k1_xboole_0=B_271 | k1_xboole_0=A_270 | ~v1_xboole_0(B_8) | ~v1_xboole_0(k2_zfmisc_1(A_270, B_271)))), inference(resolution, [status(thm)], [c_16, c_1452])).
% 3.90/1.64  tff(c_1703, plain, (![A_302, B_303]: (k1_xboole_0=A_302 | k1_xboole_0=B_303 | ~v1_xboole_0(k2_zfmisc_1(A_302, B_303)))), inference(splitLeft, [status(thm)], [c_1466])).
% 3.90/1.64  tff(c_1713, plain, (![A_304, B_305, C_306]: (k2_zfmisc_1(A_304, B_305)=k1_xboole_0 | k1_xboole_0=C_306 | ~v1_xboole_0(k3_zfmisc_1(A_304, B_305, C_306)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1703])).
% 3.90/1.64  tff(c_1728, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1024, c_1713])).
% 3.90/1.64  tff(c_1734, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_46, c_1728])).
% 3.90/1.64  tff(c_4, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.90/1.64  tff(c_1766, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1734, c_4])).
% 3.90/1.64  tff(c_1787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_48, c_1766])).
% 3.90/1.64  tff(c_1817, plain, (![B_311]: (k4_tarski(k1_mcart_1(B_311), k2_mcart_1(B_311))=B_311 | ~v1_xboole_0(B_311))), inference(splitRight, [status(thm)], [c_1466])).
% 3.90/1.64  tff(c_2, plain, (![A_1, B_2]: (~v1_xboole_0(k4_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.90/1.64  tff(c_1842, plain, (![B_312]: (~v1_xboole_0(B_312) | ~v1_xboole_0(B_312))), inference(superposition, [status(thm), theory('equality')], [c_1817, c_2])).
% 3.90/1.64  tff(c_1846, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1024, c_1842])).
% 3.90/1.64  tff(c_1853, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1024, c_1846])).
% 3.90/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.64  
% 3.90/1.64  Inference rules
% 3.90/1.64  ----------------------
% 3.90/1.64  #Ref     : 0
% 3.90/1.64  #Sup     : 456
% 3.90/1.64  #Fact    : 0
% 3.90/1.64  #Define  : 0
% 3.90/1.64  #Split   : 14
% 3.90/1.64  #Chain   : 0
% 3.90/1.64  #Close   : 0
% 3.90/1.64  
% 3.90/1.64  Ordering : KBO
% 3.90/1.64  
% 3.90/1.64  Simplification rules
% 3.90/1.64  ----------------------
% 3.90/1.64  #Subsume      : 172
% 3.90/1.64  #Demod        : 222
% 3.90/1.64  #Tautology    : 135
% 3.90/1.64  #SimpNegUnit  : 69
% 3.90/1.64  #BackRed      : 2
% 3.90/1.64  
% 3.90/1.64  #Partial instantiations: 0
% 3.90/1.64  #Strategies tried      : 1
% 3.90/1.64  
% 3.90/1.64  Timing (in seconds)
% 3.90/1.64  ----------------------
% 3.90/1.64  Preprocessing        : 0.34
% 3.90/1.64  Parsing              : 0.18
% 3.90/1.64  CNF conversion       : 0.02
% 3.90/1.64  Main loop            : 0.53
% 3.90/1.64  Inferencing          : 0.19
% 3.90/1.64  Reduction            : 0.18
% 3.90/1.64  Demodulation         : 0.12
% 3.90/1.64  BG Simplification    : 0.03
% 3.90/1.64  Subsumption          : 0.09
% 3.90/1.64  Abstraction          : 0.03
% 3.90/1.64  MUC search           : 0.00
% 3.90/1.64  Cooper               : 0.00
% 3.90/1.64  Total                : 0.90
% 3.90/1.64  Index Insertion      : 0.00
% 3.90/1.64  Index Deletion       : 0.00
% 3.90/1.64  Index Matching       : 0.00
% 3.90/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
