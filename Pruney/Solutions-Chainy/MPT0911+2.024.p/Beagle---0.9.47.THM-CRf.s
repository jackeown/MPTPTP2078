%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:04 EST 2020

% Result     : Theorem 8.28s
% Output     : CNFRefutation 8.28s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 446 expanded)
%              Number of leaves         :   35 ( 172 expanded)
%              Depth                    :   13
%              Number of atoms          :  196 (1071 expanded)
%              Number of equality atoms :  102 ( 513 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_130,negated_conjecture,(
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

tff(f_106,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_64,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_63,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_62,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_46])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    ! [A_24,B_25,C_26,D_28] :
      ( k7_mcart_1(A_24,B_25,C_26,D_28) = k2_mcart_1(D_28)
      | ~ m1_subset_1(D_28,k3_zfmisc_1(A_24,B_25,C_26))
      | k1_xboole_0 = C_26
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_258,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k7_mcart_1(A_94,B_95,C_96,D_97) = k2_mcart_1(D_97)
      | ~ m1_subset_1(D_97,k3_zfmisc_1(A_94,B_95,C_96))
      | C_96 = '#skF_1'
      | B_95 = '#skF_1'
      | A_94 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_60,c_38])).

tff(c_269,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') = k2_mcart_1('#skF_6')
    | '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_258])).

tff(c_283,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') = k2_mcart_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_63,c_62,c_269])).

tff(c_44,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_287,plain,(
    k2_mcart_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_44])).

tff(c_128,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,A_58)
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_132,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_128])).

tff(c_139,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( r2_hidden(B_5,A_4)
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_170,plain,(
    ! [A_75,B_76,C_77] : k2_zfmisc_1(k2_zfmisc_1(A_75,B_76),C_77) = k3_zfmisc_1(A_75,B_76,C_77) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_16,C_18,B_17] :
      ( r2_hidden(k2_mcart_1(A_16),C_18)
      | ~ r2_hidden(A_16,k2_zfmisc_1(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_204,plain,(
    ! [A_83,C_84,A_85,B_86] :
      ( r2_hidden(k2_mcart_1(A_83),C_84)
      | ~ r2_hidden(A_83,k3_zfmisc_1(A_85,B_86,C_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_24])).

tff(c_3927,plain,(
    ! [B_227,C_228,A_229,B_230] :
      ( r2_hidden(k2_mcart_1(B_227),C_228)
      | ~ m1_subset_1(B_227,k3_zfmisc_1(A_229,B_230,C_228))
      | v1_xboole_0(k3_zfmisc_1(A_229,B_230,C_228)) ) ),
    inference(resolution,[status(thm)],[c_10,c_204])).

tff(c_3973,plain,
    ( r2_hidden(k2_mcart_1('#skF_6'),'#skF_4')
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_3927])).

tff(c_3997,plain,(
    r2_hidden(k2_mcart_1('#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_3973])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4007,plain,(
    m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3997,c_16])).

tff(c_18,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_182,plain,(
    ! [A_75,B_76,C_77] : v1_relat_1(k3_zfmisc_1(A_75,B_76,C_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_18])).

tff(c_198,plain,(
    ! [A_81,B_82] :
      ( k4_tarski(k1_mcart_1(A_81),k2_mcart_1(A_81)) = A_81
      | ~ r2_hidden(A_81,B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3414,plain,(
    ! [B_220,A_221] :
      ( k4_tarski(k1_mcart_1(B_220),k2_mcart_1(B_220)) = B_220
      | ~ v1_relat_1(A_221)
      | ~ m1_subset_1(B_220,A_221)
      | v1_xboole_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_10,c_198])).

tff(c_3446,plain,
    ( k4_tarski(k1_mcart_1('#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'))
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_3414])).

tff(c_3468,plain,
    ( k4_tarski(k1_mcart_1('#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_3446])).

tff(c_3469,plain,(
    k4_tarski(k1_mcart_1('#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_3468])).

tff(c_42,plain,(
    ! [A_24,B_25,C_26,D_28] :
      ( k5_mcart_1(A_24,B_25,C_26,D_28) = k1_mcart_1(k1_mcart_1(D_28))
      | ~ m1_subset_1(D_28,k3_zfmisc_1(A_24,B_25,C_26))
      | k1_xboole_0 = C_26
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_333,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k5_mcart_1(A_102,B_103,C_104,D_105) = k1_mcart_1(k1_mcart_1(D_105))
      | ~ m1_subset_1(D_105,k3_zfmisc_1(A_102,B_103,C_104))
      | C_104 = '#skF_1'
      | B_103 = '#skF_1'
      | A_102 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_60,c_42])).

tff(c_344,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_6')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6')
    | '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_333])).

tff(c_358,plain,(
    k1_mcart_1(k1_mcart_1('#skF_6')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_63,c_62,c_344])).

tff(c_26,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden(k1_mcart_1(A_16),B_17)
      | ~ r2_hidden(A_16,k2_zfmisc_1(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1006,plain,(
    ! [A_147,A_148,B_149,C_150] :
      ( r2_hidden(k1_mcart_1(A_147),k2_zfmisc_1(A_148,B_149))
      | ~ r2_hidden(A_147,k3_zfmisc_1(A_148,B_149,C_150)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_26])).

tff(c_5681,plain,(
    ! [B_257,A_258,B_259,C_260] :
      ( r2_hidden(k1_mcart_1(B_257),k2_zfmisc_1(A_258,B_259))
      | ~ m1_subset_1(B_257,k3_zfmisc_1(A_258,B_259,C_260))
      | v1_xboole_0(k3_zfmisc_1(A_258,B_259,C_260)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1006])).

tff(c_5730,plain,
    ( r2_hidden(k1_mcart_1('#skF_6'),k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_5681])).

tff(c_5755,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_5730])).

tff(c_5762,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_6')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5755,c_26])).

tff(c_5772,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_5762])).

tff(c_5799,plain,(
    m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5772,c_16])).

tff(c_40,plain,(
    ! [A_24,B_25,C_26,D_28] :
      ( k6_mcart_1(A_24,B_25,C_26,D_28) = k2_mcart_1(k1_mcart_1(D_28))
      | ~ m1_subset_1(D_28,k3_zfmisc_1(A_24,B_25,C_26))
      | k1_xboole_0 = C_26
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_397,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k6_mcart_1(A_110,B_111,C_112,D_113) = k2_mcart_1(k1_mcart_1(D_113))
      | ~ m1_subset_1(D_113,k3_zfmisc_1(A_110,B_111,C_112))
      | C_112 = '#skF_1'
      | B_111 = '#skF_1'
      | A_110 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_60,c_40])).

tff(c_416,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_6')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6')
    | '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_397])).

tff(c_432,plain,(
    k2_mcart_1(k1_mcart_1('#skF_6')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_63,c_62,c_416])).

tff(c_5764,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_6')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5755,c_24])).

tff(c_5774,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_5764])).

tff(c_5806,plain,(
    m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5774,c_16])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k4_tarski(k1_mcart_1(A_19),k2_mcart_1(A_19)) = A_19
      | ~ r2_hidden(A_19,B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5760,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_6')),k2_mcart_1(k1_mcart_1('#skF_6'))) = k1_mcart_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5755,c_28])).

tff(c_5770,plain,(
    k4_tarski(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6')) = k1_mcart_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_358,c_432,c_5760])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] : k4_tarski(k4_tarski(A_10,B_11),C_12) = k3_mcart_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10748,plain,(
    ! [C_329] : k3_mcart_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),C_329) = k4_tarski(k1_mcart_1('#skF_6'),C_329) ),
    inference(superposition,[status(thm),theory(equality)],[c_5770,c_20])).

tff(c_52,plain,(
    ! [H_42,F_36,G_40] :
      ( H_42 = '#skF_5'
      | k3_mcart_1(F_36,G_40,H_42) != '#skF_6'
      | ~ m1_subset_1(H_42,'#skF_4')
      | ~ m1_subset_1(G_40,'#skF_3')
      | ~ m1_subset_1(F_36,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10755,plain,(
    ! [C_329] :
      ( C_329 = '#skF_5'
      | k4_tarski(k1_mcart_1('#skF_6'),C_329) != '#skF_6'
      | ~ m1_subset_1(C_329,'#skF_4')
      | ~ m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3')
      | ~ m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10748,c_52])).

tff(c_11339,plain,(
    ! [C_338] :
      ( C_338 = '#skF_5'
      | k4_tarski(k1_mcart_1('#skF_6'),C_338) != '#skF_6'
      | ~ m1_subset_1(C_338,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5799,c_5806,c_10755])).

tff(c_11342,plain,
    ( k2_mcart_1('#skF_6') = '#skF_5'
    | ~ m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3469,c_11339])).

tff(c_11345,plain,(
    k2_mcart_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4007,c_11342])).

tff(c_11347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_11345])).

tff(c_11349,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2])).

tff(c_11373,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_11349,c_61])).

tff(c_30,plain,(
    ! [A_21,B_22,C_23] :
      ( k3_zfmisc_1(A_21,B_22,C_23) != k1_xboole_0
      | k1_xboole_0 = C_23
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_11495,plain,(
    ! [A_369,B_370,C_371] :
      ( k3_zfmisc_1(A_369,B_370,C_371) != '#skF_1'
      | C_371 = '#skF_1'
      | B_370 = '#skF_1'
      | A_369 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_60,c_60,c_30])).

tff(c_11498,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11373,c_11495])).

tff(c_11511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_63,c_62,c_11498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.28/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.28/2.84  
% 8.28/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.28/2.84  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.28/2.84  
% 8.28/2.84  %Foreground sorts:
% 8.28/2.84  
% 8.28/2.84  
% 8.28/2.84  %Background operators:
% 8.28/2.84  
% 8.28/2.84  
% 8.28/2.84  %Foreground operators:
% 8.28/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.28/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.28/2.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.28/2.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.28/2.84  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 8.28/2.84  tff('#skF_5', type, '#skF_5': $i).
% 8.28/2.84  tff('#skF_6', type, '#skF_6': $i).
% 8.28/2.84  tff('#skF_2', type, '#skF_2': $i).
% 8.28/2.84  tff('#skF_3', type, '#skF_3': $i).
% 8.28/2.84  tff('#skF_1', type, '#skF_1': $i).
% 8.28/2.84  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 8.28/2.84  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 8.28/2.84  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 8.28/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.28/2.84  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 8.28/2.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.28/2.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.28/2.84  tff('#skF_4', type, '#skF_4': $i).
% 8.28/2.84  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 8.28/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.28/2.84  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 8.28/2.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.28/2.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.28/2.84  
% 8.28/2.86  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 8.28/2.86  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.28/2.86  tff(f_130, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 8.28/2.86  tff(f_106, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 8.28/2.86  tff(f_52, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.28/2.86  tff(f_62, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 8.28/2.86  tff(f_68, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 8.28/2.86  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 8.28/2.86  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.28/2.86  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 8.28/2.86  tff(f_60, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 8.28/2.86  tff(f_86, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 8.28/2.86  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.28/2.86  tff(c_56, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.28/2.86  tff(c_60, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_56])).
% 8.28/2.86  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.28/2.86  tff(c_64, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50])).
% 8.28/2.86  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.28/2.86  tff(c_63, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 8.28/2.86  tff(c_46, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.28/2.86  tff(c_62, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_46])).
% 8.28/2.86  tff(c_54, plain, (m1_subset_1('#skF_6', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.28/2.86  tff(c_38, plain, (![A_24, B_25, C_26, D_28]: (k7_mcart_1(A_24, B_25, C_26, D_28)=k2_mcart_1(D_28) | ~m1_subset_1(D_28, k3_zfmisc_1(A_24, B_25, C_26)) | k1_xboole_0=C_26 | k1_xboole_0=B_25 | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.28/2.86  tff(c_258, plain, (![A_94, B_95, C_96, D_97]: (k7_mcart_1(A_94, B_95, C_96, D_97)=k2_mcart_1(D_97) | ~m1_subset_1(D_97, k3_zfmisc_1(A_94, B_95, C_96)) | C_96='#skF_1' | B_95='#skF_1' | A_94='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_60, c_38])).
% 8.28/2.86  tff(c_269, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_mcart_1('#skF_6') | '#skF_1'='#skF_4' | '#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_54, c_258])).
% 8.28/2.86  tff(c_283, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_mcart_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_63, c_62, c_269])).
% 8.28/2.86  tff(c_44, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.28/2.86  tff(c_287, plain, (k2_mcart_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_283, c_44])).
% 8.28/2.86  tff(c_128, plain, (![B_57, A_58]: (v1_xboole_0(B_57) | ~m1_subset_1(B_57, A_58) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.28/2.86  tff(c_132, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_128])).
% 8.28/2.86  tff(c_139, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_132])).
% 8.28/2.86  tff(c_10, plain, (![B_5, A_4]: (r2_hidden(B_5, A_4) | ~m1_subset_1(B_5, A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.28/2.86  tff(c_170, plain, (![A_75, B_76, C_77]: (k2_zfmisc_1(k2_zfmisc_1(A_75, B_76), C_77)=k3_zfmisc_1(A_75, B_76, C_77))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.28/2.86  tff(c_24, plain, (![A_16, C_18, B_17]: (r2_hidden(k2_mcart_1(A_16), C_18) | ~r2_hidden(A_16, k2_zfmisc_1(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.28/2.86  tff(c_204, plain, (![A_83, C_84, A_85, B_86]: (r2_hidden(k2_mcart_1(A_83), C_84) | ~r2_hidden(A_83, k3_zfmisc_1(A_85, B_86, C_84)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_24])).
% 8.28/2.86  tff(c_3927, plain, (![B_227, C_228, A_229, B_230]: (r2_hidden(k2_mcart_1(B_227), C_228) | ~m1_subset_1(B_227, k3_zfmisc_1(A_229, B_230, C_228)) | v1_xboole_0(k3_zfmisc_1(A_229, B_230, C_228)))), inference(resolution, [status(thm)], [c_10, c_204])).
% 8.28/2.86  tff(c_3973, plain, (r2_hidden(k2_mcart_1('#skF_6'), '#skF_4') | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_3927])).
% 8.28/2.86  tff(c_3997, plain, (r2_hidden(k2_mcart_1('#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_139, c_3973])).
% 8.28/2.86  tff(c_16, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.28/2.86  tff(c_4007, plain, (m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_3997, c_16])).
% 8.28/2.86  tff(c_18, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.28/2.86  tff(c_182, plain, (![A_75, B_76, C_77]: (v1_relat_1(k3_zfmisc_1(A_75, B_76, C_77)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_18])).
% 8.28/2.86  tff(c_198, plain, (![A_81, B_82]: (k4_tarski(k1_mcart_1(A_81), k2_mcart_1(A_81))=A_81 | ~r2_hidden(A_81, B_82) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.28/2.86  tff(c_3414, plain, (![B_220, A_221]: (k4_tarski(k1_mcart_1(B_220), k2_mcart_1(B_220))=B_220 | ~v1_relat_1(A_221) | ~m1_subset_1(B_220, A_221) | v1_xboole_0(A_221))), inference(resolution, [status(thm)], [c_10, c_198])).
% 8.28/2.86  tff(c_3446, plain, (k4_tarski(k1_mcart_1('#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | ~v1_relat_1(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')) | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_3414])).
% 8.28/2.86  tff(c_3468, plain, (k4_tarski(k1_mcart_1('#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_3446])).
% 8.28/2.86  tff(c_3469, plain, (k4_tarski(k1_mcart_1('#skF_6'), k2_mcart_1('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_139, c_3468])).
% 8.28/2.86  tff(c_42, plain, (![A_24, B_25, C_26, D_28]: (k5_mcart_1(A_24, B_25, C_26, D_28)=k1_mcart_1(k1_mcart_1(D_28)) | ~m1_subset_1(D_28, k3_zfmisc_1(A_24, B_25, C_26)) | k1_xboole_0=C_26 | k1_xboole_0=B_25 | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.28/2.86  tff(c_333, plain, (![A_102, B_103, C_104, D_105]: (k5_mcart_1(A_102, B_103, C_104, D_105)=k1_mcart_1(k1_mcart_1(D_105)) | ~m1_subset_1(D_105, k3_zfmisc_1(A_102, B_103, C_104)) | C_104='#skF_1' | B_103='#skF_1' | A_102='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_60, c_42])).
% 8.28/2.86  tff(c_344, plain, (k1_mcart_1(k1_mcart_1('#skF_6'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6') | '#skF_1'='#skF_4' | '#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_54, c_333])).
% 8.28/2.86  tff(c_358, plain, (k1_mcart_1(k1_mcart_1('#skF_6'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_63, c_62, c_344])).
% 8.28/2.86  tff(c_26, plain, (![A_16, B_17, C_18]: (r2_hidden(k1_mcart_1(A_16), B_17) | ~r2_hidden(A_16, k2_zfmisc_1(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.28/2.86  tff(c_1006, plain, (![A_147, A_148, B_149, C_150]: (r2_hidden(k1_mcart_1(A_147), k2_zfmisc_1(A_148, B_149)) | ~r2_hidden(A_147, k3_zfmisc_1(A_148, B_149, C_150)))), inference(superposition, [status(thm), theory('equality')], [c_170, c_26])).
% 8.28/2.86  tff(c_5681, plain, (![B_257, A_258, B_259, C_260]: (r2_hidden(k1_mcart_1(B_257), k2_zfmisc_1(A_258, B_259)) | ~m1_subset_1(B_257, k3_zfmisc_1(A_258, B_259, C_260)) | v1_xboole_0(k3_zfmisc_1(A_258, B_259, C_260)))), inference(resolution, [status(thm)], [c_10, c_1006])).
% 8.28/2.86  tff(c_5730, plain, (r2_hidden(k1_mcart_1('#skF_6'), k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_5681])).
% 8.28/2.86  tff(c_5755, plain, (r2_hidden(k1_mcart_1('#skF_6'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_139, c_5730])).
% 8.28/2.86  tff(c_5762, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_6')), '#skF_2')), inference(resolution, [status(thm)], [c_5755, c_26])).
% 8.28/2.86  tff(c_5772, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_358, c_5762])).
% 8.28/2.86  tff(c_5799, plain, (m1_subset_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(resolution, [status(thm)], [c_5772, c_16])).
% 8.28/2.86  tff(c_40, plain, (![A_24, B_25, C_26, D_28]: (k6_mcart_1(A_24, B_25, C_26, D_28)=k2_mcart_1(k1_mcart_1(D_28)) | ~m1_subset_1(D_28, k3_zfmisc_1(A_24, B_25, C_26)) | k1_xboole_0=C_26 | k1_xboole_0=B_25 | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.28/2.86  tff(c_397, plain, (![A_110, B_111, C_112, D_113]: (k6_mcart_1(A_110, B_111, C_112, D_113)=k2_mcart_1(k1_mcart_1(D_113)) | ~m1_subset_1(D_113, k3_zfmisc_1(A_110, B_111, C_112)) | C_112='#skF_1' | B_111='#skF_1' | A_110='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_60, c_40])).
% 8.28/2.86  tff(c_416, plain, (k2_mcart_1(k1_mcart_1('#skF_6'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6') | '#skF_1'='#skF_4' | '#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_54, c_397])).
% 8.28/2.86  tff(c_432, plain, (k2_mcart_1(k1_mcart_1('#skF_6'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_63, c_62, c_416])).
% 8.28/2.86  tff(c_5764, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_6')), '#skF_3')), inference(resolution, [status(thm)], [c_5755, c_24])).
% 8.28/2.86  tff(c_5774, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_432, c_5764])).
% 8.28/2.86  tff(c_5806, plain, (m1_subset_1(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_5774, c_16])).
% 8.28/2.86  tff(c_28, plain, (![A_19, B_20]: (k4_tarski(k1_mcart_1(A_19), k2_mcart_1(A_19))=A_19 | ~r2_hidden(A_19, B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.28/2.86  tff(c_5760, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_6')), k2_mcart_1(k1_mcart_1('#skF_6')))=k1_mcart_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5755, c_28])).
% 8.28/2.86  tff(c_5770, plain, (k4_tarski(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))=k1_mcart_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_358, c_432, c_5760])).
% 8.28/2.86  tff(c_20, plain, (![A_10, B_11, C_12]: (k4_tarski(k4_tarski(A_10, B_11), C_12)=k3_mcart_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.28/2.86  tff(c_10748, plain, (![C_329]: (k3_mcart_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), C_329)=k4_tarski(k1_mcart_1('#skF_6'), C_329))), inference(superposition, [status(thm), theory('equality')], [c_5770, c_20])).
% 8.28/2.86  tff(c_52, plain, (![H_42, F_36, G_40]: (H_42='#skF_5' | k3_mcart_1(F_36, G_40, H_42)!='#skF_6' | ~m1_subset_1(H_42, '#skF_4') | ~m1_subset_1(G_40, '#skF_3') | ~m1_subset_1(F_36, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.28/2.86  tff(c_10755, plain, (![C_329]: (C_329='#skF_5' | k4_tarski(k1_mcart_1('#skF_6'), C_329)!='#skF_6' | ~m1_subset_1(C_329, '#skF_4') | ~m1_subset_1(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10748, c_52])).
% 8.28/2.86  tff(c_11339, plain, (![C_338]: (C_338='#skF_5' | k4_tarski(k1_mcart_1('#skF_6'), C_338)!='#skF_6' | ~m1_subset_1(C_338, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5799, c_5806, c_10755])).
% 8.28/2.86  tff(c_11342, plain, (k2_mcart_1('#skF_6')='#skF_5' | ~m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3469, c_11339])).
% 8.28/2.86  tff(c_11345, plain, (k2_mcart_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4007, c_11342])).
% 8.28/2.86  tff(c_11347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_11345])).
% 8.28/2.86  tff(c_11349, plain, (v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_132])).
% 8.28/2.86  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.28/2.86  tff(c_61, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2])).
% 8.28/2.86  tff(c_11373, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_11349, c_61])).
% 8.28/2.86  tff(c_30, plain, (![A_21, B_22, C_23]: (k3_zfmisc_1(A_21, B_22, C_23)!=k1_xboole_0 | k1_xboole_0=C_23 | k1_xboole_0=B_22 | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.28/2.86  tff(c_11495, plain, (![A_369, B_370, C_371]: (k3_zfmisc_1(A_369, B_370, C_371)!='#skF_1' | C_371='#skF_1' | B_370='#skF_1' | A_369='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_60, c_60, c_30])).
% 8.28/2.86  tff(c_11498, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11373, c_11495])).
% 8.28/2.86  tff(c_11511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_63, c_62, c_11498])).
% 8.28/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.28/2.86  
% 8.28/2.86  Inference rules
% 8.28/2.86  ----------------------
% 8.28/2.86  #Ref     : 0
% 8.28/2.86  #Sup     : 3379
% 8.28/2.86  #Fact    : 0
% 8.28/2.86  #Define  : 0
% 8.28/2.86  #Split   : 15
% 8.28/2.86  #Chain   : 0
% 8.28/2.86  #Close   : 0
% 8.28/2.86  
% 8.28/2.86  Ordering : KBO
% 8.28/2.86  
% 8.28/2.86  Simplification rules
% 8.28/2.86  ----------------------
% 8.28/2.86  #Subsume      : 1376
% 8.28/2.86  #Demod        : 300
% 8.28/2.86  #Tautology    : 313
% 8.28/2.86  #SimpNegUnit  : 47
% 8.28/2.86  #BackRed      : 40
% 8.28/2.86  
% 8.28/2.86  #Partial instantiations: 0
% 8.28/2.86  #Strategies tried      : 1
% 8.28/2.86  
% 8.28/2.86  Timing (in seconds)
% 8.28/2.86  ----------------------
% 8.28/2.86  Preprocessing        : 0.34
% 8.28/2.86  Parsing              : 0.18
% 8.28/2.86  CNF conversion       : 0.02
% 8.28/2.86  Main loop            : 1.72
% 8.28/2.86  Inferencing          : 0.48
% 8.28/2.86  Reduction            : 0.50
% 8.28/2.86  Demodulation         : 0.34
% 8.28/2.86  BG Simplification    : 0.07
% 8.28/2.86  Subsumption          : 0.51
% 8.28/2.86  Abstraction          : 0.08
% 8.28/2.86  MUC search           : 0.00
% 8.28/2.86  Cooper               : 0.00
% 8.28/2.86  Total                : 2.10
% 8.28/2.86  Index Insertion      : 0.00
% 8.28/2.86  Index Deletion       : 0.00
% 8.28/2.86  Index Matching       : 0.00
% 8.28/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
