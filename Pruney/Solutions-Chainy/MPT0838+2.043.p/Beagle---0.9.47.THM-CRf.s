%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:15 EST 2020

% Result     : Theorem 4.38s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 463 expanded)
%              Number of leaves         :   51 ( 174 expanded)
%              Depth                    :   15
%              Number of atoms          :  186 ( 952 expanded)
%              Number of equality atoms :   44 ( 143 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_17 > #skF_15 > #skF_1 > #skF_12 > #skF_3 > #skF_16 > #skF_10 > #skF_13 > #skF_14 > #skF_2 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(c_72,plain,(
    m1_subset_1('#skF_17',k1_zfmisc_1(k2_zfmisc_1('#skF_15','#skF_16'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2769,plain,(
    ! [A_340,B_341,C_342] :
      ( k1_relset_1(A_340,B_341,C_342) = k1_relat_1(C_342)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_340,B_341))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2783,plain,(
    k1_relset_1('#skF_15','#skF_16','#skF_17') = k1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_72,c_2769])).

tff(c_54,plain,(
    ! [A_59,B_60] : v1_relat_1(k2_zfmisc_1(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_126,plain,(
    ! [B_102,A_103] :
      ( v1_relat_1(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_103))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_133,plain,
    ( v1_relat_1('#skF_17')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_15','#skF_16')) ),
    inference(resolution,[status(thm)],[c_72,c_126])).

tff(c_137,plain,(
    v1_relat_1('#skF_17') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_133])).

tff(c_2622,plain,(
    ! [A_334,B_335,C_336] :
      ( k2_relset_1(A_334,B_335,C_336) = k2_relat_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2636,plain,(
    k2_relset_1('#skF_15','#skF_16','#skF_17') = k2_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_72,c_2622])).

tff(c_220,plain,(
    ! [C_126,B_127,A_128] :
      ( v5_relat_1(C_126,B_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_128,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_234,plain,(
    v5_relat_1('#skF_17','#skF_16') ),
    inference(resolution,[status(thm)],[c_72,c_220])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [C_115,B_116,A_117] :
      ( r2_hidden(C_115,B_116)
      | ~ r2_hidden(C_115,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_272,plain,(
    ! [A_137,B_138] :
      ( r2_hidden('#skF_1'(A_137),B_138)
      | ~ r1_tarski(A_137,B_138)
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_4,c_181])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_291,plain,(
    ! [A_137,B_138] :
      ( m1_subset_1('#skF_1'(A_137),B_138)
      | ~ r1_tarski(A_137,B_138)
      | v1_xboole_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_272,c_22])).

tff(c_689,plain,(
    ! [A_190,B_191,C_192] :
      ( k2_relset_1(A_190,B_191,C_192) = k2_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_718,plain,(
    k2_relset_1('#skF_15','#skF_16','#skF_17') = k2_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_72,c_689])).

tff(c_90,plain,(
    ! [D_95] :
      ( ~ r2_hidden(D_95,k2_relset_1('#skF_15','#skF_16','#skF_17'))
      | ~ m1_subset_1(D_95,'#skF_16') ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_95,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_15','#skF_16','#skF_17')),'#skF_16')
    | v1_xboole_0(k2_relset_1('#skF_15','#skF_16','#skF_17')) ),
    inference(resolution,[status(thm)],[c_4,c_90])).

tff(c_150,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_15','#skF_16','#skF_17')),'#skF_16') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_723,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_17')),'#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_150])).

tff(c_732,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_17'),'#skF_16')
    | v1_xboole_0(k2_relat_1('#skF_17')) ),
    inference(resolution,[status(thm)],[c_291,c_723])).

tff(c_805,plain,(
    ~ r1_tarski(k2_relat_1('#skF_17'),'#skF_16') ),
    inference(splitLeft,[status(thm)],[c_732])).

tff(c_808,plain,
    ( ~ v5_relat_1('#skF_17','#skF_16')
    | ~ v1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_28,c_805])).

tff(c_815,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_234,c_808])).

tff(c_816,plain,(
    v1_xboole_0(k2_relat_1('#skF_17')) ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_237,plain,(
    ! [A_135] :
      ( k1_xboole_0 = A_135
      | r2_hidden(k4_tarski('#skF_13'(A_135),'#skF_14'(A_135)),A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    ! [C_55,A_40,D_58] :
      ( r2_hidden(C_55,k2_relat_1(A_40))
      | ~ r2_hidden(k4_tarski(D_58,C_55),A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_350,plain,(
    ! [A_144] :
      ( r2_hidden('#skF_14'(A_144),k2_relat_1(A_144))
      | k1_xboole_0 = A_144
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_237,c_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_365,plain,(
    ! [A_144] :
      ( ~ v1_xboole_0(k2_relat_1(A_144))
      | k1_xboole_0 = A_144
      | ~ v1_relat_1(A_144) ) ),
    inference(resolution,[status(thm)],[c_350,c_2])).

tff(c_825,plain,
    ( k1_xboole_0 = '#skF_17'
    | ~ v1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_816,c_365])).

tff(c_832,plain,(
    k1_xboole_0 = '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_825])).

tff(c_630,plain,(
    ! [A_179,B_180,C_181] :
      ( k1_relset_1(A_179,B_180,C_181) = k1_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_659,plain,(
    k1_relset_1('#skF_15','#skF_16','#skF_17') = k1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_72,c_630])).

tff(c_70,plain,(
    k1_relset_1('#skF_15','#skF_16','#skF_17') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_660,plain,(
    k1_relat_1('#skF_17') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_70])).

tff(c_867,plain,(
    k1_relat_1('#skF_17') != '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_660])).

tff(c_1725,plain,(
    ! [C_235,A_236] :
      ( r2_hidden(k4_tarski(C_235,'#skF_8'(A_236,k1_relat_1(A_236),C_235)),A_236)
      | ~ r2_hidden(C_235,k1_relat_1(A_236)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_96,plain,(
    ! [B_96,A_97] :
      ( ~ r1_tarski(B_96,A_97)
      | ~ r2_hidden(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_102,plain,(
    ! [A_99] :
      ( ~ r1_tarski(A_99,'#skF_1'(A_99))
      | v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_4,c_96])).

tff(c_107,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_102])).

tff(c_880,plain,(
    v1_xboole_0('#skF_17') ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_107])).

tff(c_388,plain,(
    ! [A_148,B_149] :
      ( r2_hidden('#skF_3'(A_148,B_149),B_149)
      | r2_hidden('#skF_4'(A_148,B_149),A_148)
      | B_149 = A_148 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_467,plain,(
    ! [B_156,A_157] :
      ( ~ v1_xboole_0(B_156)
      | r2_hidden('#skF_4'(A_157,B_156),A_157)
      | B_156 = A_157 ) ),
    inference(resolution,[status(thm)],[c_388,c_2])).

tff(c_488,plain,(
    ! [A_158,B_159] :
      ( ~ v1_xboole_0(A_158)
      | ~ v1_xboole_0(B_159)
      | B_159 = A_158 ) ),
    inference(resolution,[status(thm)],[c_467,c_2])).

tff(c_494,plain,(
    ! [B_159] :
      ( ~ v1_xboole_0(B_159)
      | k1_xboole_0 = B_159 ) ),
    inference(resolution,[status(thm)],[c_107,c_488])).

tff(c_828,plain,(
    k2_relat_1('#skF_17') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_816,c_494])).

tff(c_889,plain,(
    k2_relat_1('#skF_17') = '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_828])).

tff(c_1308,plain,(
    ! [A_222,C_223] :
      ( r2_hidden(k4_tarski('#skF_12'(A_222,k2_relat_1(A_222),C_223),C_223),A_222)
      | ~ r2_hidden(C_223,k2_relat_1(A_222)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1342,plain,(
    ! [A_224,C_225] :
      ( ~ v1_xboole_0(A_224)
      | ~ r2_hidden(C_225,k2_relat_1(A_224)) ) ),
    inference(resolution,[status(thm)],[c_1308,c_2])).

tff(c_1360,plain,(
    ! [C_225] :
      ( ~ v1_xboole_0('#skF_17')
      | ~ r2_hidden(C_225,'#skF_17') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_1342])).

tff(c_1398,plain,(
    ! [C_225] : ~ r2_hidden(C_225,'#skF_17') ),
    inference(demodulation,[status(thm),theory(equality)],[c_880,c_1360])).

tff(c_1764,plain,(
    ! [C_237] : ~ r2_hidden(C_237,k1_relat_1('#skF_17')) ),
    inference(resolution,[status(thm)],[c_1725,c_1398])).

tff(c_1824,plain,(
    v1_xboole_0(k1_relat_1('#skF_17')) ),
    inference(resolution,[status(thm)],[c_4,c_1764])).

tff(c_870,plain,(
    ! [B_159] :
      ( ~ v1_xboole_0(B_159)
      | B_159 = '#skF_17' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_494])).

tff(c_1833,plain,(
    k1_relat_1('#skF_17') = '#skF_17' ),
    inference(resolution,[status(thm)],[c_1824,c_870])).

tff(c_1844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_867,c_1833])).

tff(c_1845,plain,(
    v1_xboole_0(k2_relset_1('#skF_15','#skF_16','#skF_17')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_2640,plain,(
    v1_xboole_0(k2_relat_1('#skF_17')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2636,c_1845])).

tff(c_1934,plain,(
    ! [A_266] :
      ( k1_xboole_0 = A_266
      | r2_hidden(k4_tarski('#skF_13'(A_266),'#skF_14'(A_266)),A_266)
      | ~ v1_relat_1(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2036,plain,(
    ! [A_273] :
      ( r2_hidden('#skF_14'(A_273),k2_relat_1(A_273))
      | k1_xboole_0 = A_273
      | ~ v1_relat_1(A_273) ) ),
    inference(resolution,[status(thm)],[c_1934,c_44])).

tff(c_2051,plain,(
    ! [A_273] :
      ( ~ v1_xboole_0(k2_relat_1(A_273))
      | k1_xboole_0 = A_273
      | ~ v1_relat_1(A_273) ) ),
    inference(resolution,[status(thm)],[c_2036,c_2])).

tff(c_2649,plain,
    ( k1_xboole_0 = '#skF_17'
    | ~ v1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_2640,c_2051])).

tff(c_2657,plain,(
    k1_xboole_0 = '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_2649])).

tff(c_2708,plain,(
    k1_relset_1('#skF_15','#skF_16','#skF_17') != '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2657,c_70])).

tff(c_2814,plain,(
    k1_relat_1('#skF_17') != '#skF_17' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2783,c_2708])).

tff(c_2707,plain,(
    v1_xboole_0('#skF_17') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2657,c_107])).

tff(c_3266,plain,(
    ! [C_386,A_387] :
      ( r2_hidden(k4_tarski(C_386,'#skF_8'(A_387,k1_relat_1(A_387),C_386)),A_387)
      | ~ r2_hidden(C_386,k1_relat_1(A_387)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3295,plain,(
    ! [A_388,C_389] :
      ( ~ v1_xboole_0(A_388)
      | ~ r2_hidden(C_389,k1_relat_1(A_388)) ) ),
    inference(resolution,[status(thm)],[c_3266,c_2])).

tff(c_3350,plain,(
    ! [A_390] :
      ( ~ v1_xboole_0(A_390)
      | v1_xboole_0(k1_relat_1(A_390)) ) ),
    inference(resolution,[status(thm)],[c_4,c_3295])).

tff(c_2819,plain,(
    ! [A_344,B_345] :
      ( r2_hidden('#skF_3'(A_344,B_345),B_345)
      | r2_hidden('#skF_4'(A_344,B_345),A_344)
      | B_345 = A_344 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2953,plain,(
    ! [A_357,B_358] :
      ( ~ v1_xboole_0(A_357)
      | r2_hidden('#skF_3'(A_357,B_358),B_358)
      | B_358 = A_357 ) ),
    inference(resolution,[status(thm)],[c_2819,c_2])).

tff(c_2984,plain,(
    ! [B_359,A_360] :
      ( ~ v1_xboole_0(B_359)
      | ~ v1_xboole_0(A_360)
      | B_359 = A_360 ) ),
    inference(resolution,[status(thm)],[c_2953,c_2])).

tff(c_2990,plain,(
    ! [A_360] :
      ( ~ v1_xboole_0(A_360)
      | A_360 = '#skF_17' ) ),
    inference(resolution,[status(thm)],[c_2707,c_2984])).

tff(c_3362,plain,(
    ! [A_391] :
      ( k1_relat_1(A_391) = '#skF_17'
      | ~ v1_xboole_0(A_391) ) ),
    inference(resolution,[status(thm)],[c_3350,c_2990])).

tff(c_3371,plain,(
    k1_relat_1('#skF_17') = '#skF_17' ),
    inference(resolution,[status(thm)],[c_2707,c_3362])).

tff(c_3377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2814,c_3371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:32:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.38/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.84  
% 4.38/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.84  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_17 > #skF_15 > #skF_1 > #skF_12 > #skF_3 > #skF_16 > #skF_10 > #skF_13 > #skF_14 > #skF_2 > #skF_8 > #skF_7 > #skF_9 > #skF_5 > #skF_4
% 4.38/1.84  
% 4.38/1.84  %Foreground sorts:
% 4.38/1.84  
% 4.38/1.84  
% 4.38/1.84  %Background operators:
% 4.38/1.84  
% 4.38/1.84  
% 4.38/1.84  %Foreground operators:
% 4.38/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.38/1.84  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 4.38/1.84  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.38/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.84  tff('#skF_17', type, '#skF_17': $i).
% 4.38/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.38/1.84  tff('#skF_15', type, '#skF_15': $i).
% 4.38/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.38/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.38/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.38/1.84  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 4.38/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.38/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.38/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.38/1.84  tff('#skF_16', type, '#skF_16': $i).
% 4.38/1.84  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 4.38/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.38/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.38/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.38/1.84  tff('#skF_13', type, '#skF_13': $i > $i).
% 4.38/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.38/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.38/1.84  tff('#skF_14', type, '#skF_14': $i > $i).
% 4.38/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.38/1.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.38/1.84  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.38/1.84  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.38/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.38/1.84  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 4.38/1.84  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.38/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.38/1.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.38/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.38/1.84  
% 4.38/1.86  tff(f_130, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 4.38/1.86  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.38/1.86  tff(f_82, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.38/1.86  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.38/1.86  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.38/1.86  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.38/1.86  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.38/1.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.38/1.86  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.38/1.86  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.38/1.86  tff(f_90, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 4.38/1.86  tff(f_80, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 4.38/1.86  tff(f_72, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.38/1.86  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.38/1.86  tff(f_95, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.38/1.86  tff(f_45, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.38/1.86  tff(c_72, plain, (m1_subset_1('#skF_17', k1_zfmisc_1(k2_zfmisc_1('#skF_15', '#skF_16')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.38/1.86  tff(c_2769, plain, (![A_340, B_341, C_342]: (k1_relset_1(A_340, B_341, C_342)=k1_relat_1(C_342) | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_340, B_341))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.38/1.86  tff(c_2783, plain, (k1_relset_1('#skF_15', '#skF_16', '#skF_17')=k1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_72, c_2769])).
% 4.38/1.86  tff(c_54, plain, (![A_59, B_60]: (v1_relat_1(k2_zfmisc_1(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.38/1.86  tff(c_126, plain, (![B_102, A_103]: (v1_relat_1(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_103)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.38/1.86  tff(c_133, plain, (v1_relat_1('#skF_17') | ~v1_relat_1(k2_zfmisc_1('#skF_15', '#skF_16'))), inference(resolution, [status(thm)], [c_72, c_126])).
% 4.38/1.86  tff(c_137, plain, (v1_relat_1('#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_133])).
% 4.38/1.86  tff(c_2622, plain, (![A_334, B_335, C_336]: (k2_relset_1(A_334, B_335, C_336)=k2_relat_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.38/1.86  tff(c_2636, plain, (k2_relset_1('#skF_15', '#skF_16', '#skF_17')=k2_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_72, c_2622])).
% 4.38/1.86  tff(c_220, plain, (![C_126, B_127, A_128]: (v5_relat_1(C_126, B_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_128, B_127))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.38/1.86  tff(c_234, plain, (v5_relat_1('#skF_17', '#skF_16')), inference(resolution, [status(thm)], [c_72, c_220])).
% 4.38/1.86  tff(c_28, plain, (![B_20, A_19]: (r1_tarski(k2_relat_1(B_20), A_19) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.38/1.86  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.38/1.86  tff(c_181, plain, (![C_115, B_116, A_117]: (r2_hidden(C_115, B_116) | ~r2_hidden(C_115, A_117) | ~r1_tarski(A_117, B_116))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.38/1.86  tff(c_272, plain, (![A_137, B_138]: (r2_hidden('#skF_1'(A_137), B_138) | ~r1_tarski(A_137, B_138) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_4, c_181])).
% 4.38/1.86  tff(c_22, plain, (![A_14, B_15]: (m1_subset_1(A_14, B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.38/1.86  tff(c_291, plain, (![A_137, B_138]: (m1_subset_1('#skF_1'(A_137), B_138) | ~r1_tarski(A_137, B_138) | v1_xboole_0(A_137))), inference(resolution, [status(thm)], [c_272, c_22])).
% 4.38/1.86  tff(c_689, plain, (![A_190, B_191, C_192]: (k2_relset_1(A_190, B_191, C_192)=k2_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.38/1.86  tff(c_718, plain, (k2_relset_1('#skF_15', '#skF_16', '#skF_17')=k2_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_72, c_689])).
% 4.38/1.86  tff(c_90, plain, (![D_95]: (~r2_hidden(D_95, k2_relset_1('#skF_15', '#skF_16', '#skF_17')) | ~m1_subset_1(D_95, '#skF_16'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.38/1.86  tff(c_95, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_15', '#skF_16', '#skF_17')), '#skF_16') | v1_xboole_0(k2_relset_1('#skF_15', '#skF_16', '#skF_17'))), inference(resolution, [status(thm)], [c_4, c_90])).
% 4.38/1.86  tff(c_150, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_15', '#skF_16', '#skF_17')), '#skF_16')), inference(splitLeft, [status(thm)], [c_95])).
% 4.38/1.86  tff(c_723, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_17')), '#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_150])).
% 4.38/1.86  tff(c_732, plain, (~r1_tarski(k2_relat_1('#skF_17'), '#skF_16') | v1_xboole_0(k2_relat_1('#skF_17'))), inference(resolution, [status(thm)], [c_291, c_723])).
% 4.38/1.86  tff(c_805, plain, (~r1_tarski(k2_relat_1('#skF_17'), '#skF_16')), inference(splitLeft, [status(thm)], [c_732])).
% 4.38/1.86  tff(c_808, plain, (~v5_relat_1('#skF_17', '#skF_16') | ~v1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_28, c_805])).
% 4.38/1.86  tff(c_815, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_234, c_808])).
% 4.38/1.86  tff(c_816, plain, (v1_xboole_0(k2_relat_1('#skF_17'))), inference(splitRight, [status(thm)], [c_732])).
% 4.38/1.86  tff(c_237, plain, (![A_135]: (k1_xboole_0=A_135 | r2_hidden(k4_tarski('#skF_13'(A_135), '#skF_14'(A_135)), A_135) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.38/1.86  tff(c_44, plain, (![C_55, A_40, D_58]: (r2_hidden(C_55, k2_relat_1(A_40)) | ~r2_hidden(k4_tarski(D_58, C_55), A_40))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.38/1.86  tff(c_350, plain, (![A_144]: (r2_hidden('#skF_14'(A_144), k2_relat_1(A_144)) | k1_xboole_0=A_144 | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_237, c_44])).
% 4.38/1.86  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.38/1.86  tff(c_365, plain, (![A_144]: (~v1_xboole_0(k2_relat_1(A_144)) | k1_xboole_0=A_144 | ~v1_relat_1(A_144))), inference(resolution, [status(thm)], [c_350, c_2])).
% 4.38/1.86  tff(c_825, plain, (k1_xboole_0='#skF_17' | ~v1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_816, c_365])).
% 4.38/1.86  tff(c_832, plain, (k1_xboole_0='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_825])).
% 4.38/1.86  tff(c_630, plain, (![A_179, B_180, C_181]: (k1_relset_1(A_179, B_180, C_181)=k1_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.38/1.86  tff(c_659, plain, (k1_relset_1('#skF_15', '#skF_16', '#skF_17')=k1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_72, c_630])).
% 4.38/1.86  tff(c_70, plain, (k1_relset_1('#skF_15', '#skF_16', '#skF_17')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.38/1.86  tff(c_660, plain, (k1_relat_1('#skF_17')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_659, c_70])).
% 4.38/1.86  tff(c_867, plain, (k1_relat_1('#skF_17')!='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_832, c_660])).
% 4.38/1.86  tff(c_1725, plain, (![C_235, A_236]: (r2_hidden(k4_tarski(C_235, '#skF_8'(A_236, k1_relat_1(A_236), C_235)), A_236) | ~r2_hidden(C_235, k1_relat_1(A_236)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.38/1.86  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.38/1.86  tff(c_96, plain, (![B_96, A_97]: (~r1_tarski(B_96, A_97) | ~r2_hidden(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.38/1.86  tff(c_102, plain, (![A_99]: (~r1_tarski(A_99, '#skF_1'(A_99)) | v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_4, c_96])).
% 4.38/1.86  tff(c_107, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_102])).
% 4.38/1.86  tff(c_880, plain, (v1_xboole_0('#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_832, c_107])).
% 4.38/1.86  tff(c_388, plain, (![A_148, B_149]: (r2_hidden('#skF_3'(A_148, B_149), B_149) | r2_hidden('#skF_4'(A_148, B_149), A_148) | B_149=A_148)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.38/1.86  tff(c_467, plain, (![B_156, A_157]: (~v1_xboole_0(B_156) | r2_hidden('#skF_4'(A_157, B_156), A_157) | B_156=A_157)), inference(resolution, [status(thm)], [c_388, c_2])).
% 4.38/1.86  tff(c_488, plain, (![A_158, B_159]: (~v1_xboole_0(A_158) | ~v1_xboole_0(B_159) | B_159=A_158)), inference(resolution, [status(thm)], [c_467, c_2])).
% 4.38/1.86  tff(c_494, plain, (![B_159]: (~v1_xboole_0(B_159) | k1_xboole_0=B_159)), inference(resolution, [status(thm)], [c_107, c_488])).
% 4.38/1.86  tff(c_828, plain, (k2_relat_1('#skF_17')=k1_xboole_0), inference(resolution, [status(thm)], [c_816, c_494])).
% 4.38/1.86  tff(c_889, plain, (k2_relat_1('#skF_17')='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_832, c_828])).
% 4.38/1.86  tff(c_1308, plain, (![A_222, C_223]: (r2_hidden(k4_tarski('#skF_12'(A_222, k2_relat_1(A_222), C_223), C_223), A_222) | ~r2_hidden(C_223, k2_relat_1(A_222)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.38/1.86  tff(c_1342, plain, (![A_224, C_225]: (~v1_xboole_0(A_224) | ~r2_hidden(C_225, k2_relat_1(A_224)))), inference(resolution, [status(thm)], [c_1308, c_2])).
% 4.38/1.86  tff(c_1360, plain, (![C_225]: (~v1_xboole_0('#skF_17') | ~r2_hidden(C_225, '#skF_17'))), inference(superposition, [status(thm), theory('equality')], [c_889, c_1342])).
% 4.38/1.86  tff(c_1398, plain, (![C_225]: (~r2_hidden(C_225, '#skF_17'))), inference(demodulation, [status(thm), theory('equality')], [c_880, c_1360])).
% 4.38/1.86  tff(c_1764, plain, (![C_237]: (~r2_hidden(C_237, k1_relat_1('#skF_17')))), inference(resolution, [status(thm)], [c_1725, c_1398])).
% 4.38/1.86  tff(c_1824, plain, (v1_xboole_0(k1_relat_1('#skF_17'))), inference(resolution, [status(thm)], [c_4, c_1764])).
% 4.38/1.86  tff(c_870, plain, (![B_159]: (~v1_xboole_0(B_159) | B_159='#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_832, c_494])).
% 4.38/1.86  tff(c_1833, plain, (k1_relat_1('#skF_17')='#skF_17'), inference(resolution, [status(thm)], [c_1824, c_870])).
% 4.38/1.86  tff(c_1844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_867, c_1833])).
% 4.38/1.86  tff(c_1845, plain, (v1_xboole_0(k2_relset_1('#skF_15', '#skF_16', '#skF_17'))), inference(splitRight, [status(thm)], [c_95])).
% 4.38/1.86  tff(c_2640, plain, (v1_xboole_0(k2_relat_1('#skF_17'))), inference(demodulation, [status(thm), theory('equality')], [c_2636, c_1845])).
% 4.38/1.86  tff(c_1934, plain, (![A_266]: (k1_xboole_0=A_266 | r2_hidden(k4_tarski('#skF_13'(A_266), '#skF_14'(A_266)), A_266) | ~v1_relat_1(A_266))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.38/1.86  tff(c_2036, plain, (![A_273]: (r2_hidden('#skF_14'(A_273), k2_relat_1(A_273)) | k1_xboole_0=A_273 | ~v1_relat_1(A_273))), inference(resolution, [status(thm)], [c_1934, c_44])).
% 4.38/1.86  tff(c_2051, plain, (![A_273]: (~v1_xboole_0(k2_relat_1(A_273)) | k1_xboole_0=A_273 | ~v1_relat_1(A_273))), inference(resolution, [status(thm)], [c_2036, c_2])).
% 4.38/1.86  tff(c_2649, plain, (k1_xboole_0='#skF_17' | ~v1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_2640, c_2051])).
% 4.38/1.86  tff(c_2657, plain, (k1_xboole_0='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_2649])).
% 4.38/1.86  tff(c_2708, plain, (k1_relset_1('#skF_15', '#skF_16', '#skF_17')!='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_2657, c_70])).
% 4.38/1.86  tff(c_2814, plain, (k1_relat_1('#skF_17')!='#skF_17'), inference(demodulation, [status(thm), theory('equality')], [c_2783, c_2708])).
% 4.38/1.86  tff(c_2707, plain, (v1_xboole_0('#skF_17')), inference(demodulation, [status(thm), theory('equality')], [c_2657, c_107])).
% 4.38/1.86  tff(c_3266, plain, (![C_386, A_387]: (r2_hidden(k4_tarski(C_386, '#skF_8'(A_387, k1_relat_1(A_387), C_386)), A_387) | ~r2_hidden(C_386, k1_relat_1(A_387)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.38/1.86  tff(c_3295, plain, (![A_388, C_389]: (~v1_xboole_0(A_388) | ~r2_hidden(C_389, k1_relat_1(A_388)))), inference(resolution, [status(thm)], [c_3266, c_2])).
% 4.38/1.86  tff(c_3350, plain, (![A_390]: (~v1_xboole_0(A_390) | v1_xboole_0(k1_relat_1(A_390)))), inference(resolution, [status(thm)], [c_4, c_3295])).
% 4.38/1.86  tff(c_2819, plain, (![A_344, B_345]: (r2_hidden('#skF_3'(A_344, B_345), B_345) | r2_hidden('#skF_4'(A_344, B_345), A_344) | B_345=A_344)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.38/1.86  tff(c_2953, plain, (![A_357, B_358]: (~v1_xboole_0(A_357) | r2_hidden('#skF_3'(A_357, B_358), B_358) | B_358=A_357)), inference(resolution, [status(thm)], [c_2819, c_2])).
% 4.38/1.86  tff(c_2984, plain, (![B_359, A_360]: (~v1_xboole_0(B_359) | ~v1_xboole_0(A_360) | B_359=A_360)), inference(resolution, [status(thm)], [c_2953, c_2])).
% 4.38/1.86  tff(c_2990, plain, (![A_360]: (~v1_xboole_0(A_360) | A_360='#skF_17')), inference(resolution, [status(thm)], [c_2707, c_2984])).
% 4.38/1.86  tff(c_3362, plain, (![A_391]: (k1_relat_1(A_391)='#skF_17' | ~v1_xboole_0(A_391))), inference(resolution, [status(thm)], [c_3350, c_2990])).
% 4.38/1.86  tff(c_3371, plain, (k1_relat_1('#skF_17')='#skF_17'), inference(resolution, [status(thm)], [c_2707, c_3362])).
% 4.38/1.86  tff(c_3377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2814, c_3371])).
% 4.38/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.86  
% 4.38/1.86  Inference rules
% 4.38/1.86  ----------------------
% 4.38/1.86  #Ref     : 0
% 4.38/1.86  #Sup     : 652
% 4.38/1.86  #Fact    : 0
% 4.38/1.86  #Define  : 0
% 4.38/1.86  #Split   : 5
% 4.38/1.86  #Chain   : 0
% 4.38/1.86  #Close   : 0
% 4.38/1.86  
% 4.38/1.86  Ordering : KBO
% 4.38/1.86  
% 4.38/1.86  Simplification rules
% 4.38/1.86  ----------------------
% 4.38/1.86  #Subsume      : 132
% 4.38/1.86  #Demod        : 313
% 4.38/1.86  #Tautology    : 176
% 4.38/1.86  #SimpNegUnit  : 3
% 4.38/1.86  #BackRed      : 89
% 4.38/1.86  
% 4.38/1.86  #Partial instantiations: 0
% 4.38/1.86  #Strategies tried      : 1
% 4.38/1.86  
% 4.38/1.86  Timing (in seconds)
% 4.38/1.86  ----------------------
% 4.38/1.87  Preprocessing        : 0.34
% 4.38/1.87  Parsing              : 0.17
% 4.38/1.87  CNF conversion       : 0.03
% 4.38/1.87  Main loop            : 0.70
% 4.38/1.87  Inferencing          : 0.25
% 4.38/1.87  Reduction            : 0.21
% 4.38/1.87  Demodulation         : 0.14
% 4.38/1.87  BG Simplification    : 0.03
% 4.38/1.87  Subsumption          : 0.14
% 4.38/1.87  Abstraction          : 0.04
% 4.38/1.87  MUC search           : 0.00
% 4.38/1.87  Cooper               : 0.00
% 4.38/1.87  Total                : 1.08
% 4.38/1.87  Index Insertion      : 0.00
% 4.38/1.87  Index Deletion       : 0.00
% 4.38/1.87  Index Matching       : 0.00
% 4.38/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
