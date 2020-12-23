%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:23 EST 2020

% Result     : Theorem 8.42s
% Output     : CNFRefutation 8.42s
% Verified   : 
% Statistics : Number of formulae       :  178 (1164 expanded)
%              Number of leaves         :   47 ( 404 expanded)
%              Depth                    :   21
%              Number of atoms          :  304 (2970 expanded)
%              Number of equality atoms :   86 ( 649 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_3 > #skF_13 > #skF_8 > #skF_14 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_9923,plain,(
    ! [A_694,B_695] :
      ( r2_hidden('#skF_1'(A_694,B_695),B_695)
      | r2_hidden('#skF_2'(A_694,B_695),A_694)
      | B_695 = A_694 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_188,plain,(
    ! [A_139,B_140,C_141] :
      ( k2_relset_1(A_139,B_140,C_141) = k2_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_192,plain,(
    k2_relset_1('#skF_11','#skF_12','#skF_13') = k2_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_76,c_188])).

tff(c_74,plain,(
    k2_relset_1('#skF_11','#skF_12','#skF_13') != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_193,plain,(
    k2_relat_1('#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_74])).

tff(c_4467,plain,(
    ! [A_455,B_456] :
      ( r2_hidden(k4_tarski('#skF_4'(A_455,B_456),'#skF_3'(A_455,B_456)),A_455)
      | r2_hidden('#skF_5'(A_455,B_456),B_456)
      | k2_relat_1(A_455) = B_456 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_119,plain,(
    ! [C_109,B_110,A_111] :
      ( ~ v1_xboole_0(C_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(C_109))
      | ~ r2_hidden(A_111,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_122,plain,(
    ! [A_111] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(A_111,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_76,c_119])).

tff(c_123,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_135,plain,(
    ! [A_119,C_120,B_121] :
      ( m1_subset_1(A_119,C_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(C_120))
      | ~ r2_hidden(A_119,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,(
    ! [A_119] :
      ( m1_subset_1(A_119,k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(A_119,'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_76,c_135])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_130,plain,(
    ! [B_115,D_116,A_117,C_118] :
      ( r2_hidden(B_115,D_116)
      | ~ r2_hidden(k4_tarski(A_117,B_115),k2_zfmisc_1(C_118,D_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4373,plain,(
    ! [B_441,D_442,C_443,A_444] :
      ( r2_hidden(B_441,D_442)
      | v1_xboole_0(k2_zfmisc_1(C_443,D_442))
      | ~ m1_subset_1(k4_tarski(A_444,B_441),k2_zfmisc_1(C_443,D_442)) ) ),
    inference(resolution,[status(thm)],[c_18,c_130])).

tff(c_4377,plain,(
    ! [B_441,A_444] :
      ( r2_hidden(B_441,'#skF_12')
      | v1_xboole_0(k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(k4_tarski(A_444,B_441),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_138,c_4373])).

tff(c_4380,plain,(
    ! [B_441,A_444] :
      ( r2_hidden(B_441,'#skF_12')
      | ~ r2_hidden(k4_tarski(A_444,B_441),'#skF_13') ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_4377])).

tff(c_5758,plain,(
    ! [B_509] :
      ( r2_hidden('#skF_3'('#skF_13',B_509),'#skF_12')
      | r2_hidden('#skF_5'('#skF_13',B_509),B_509)
      | k2_relat_1('#skF_13') = B_509 ) ),
    inference(resolution,[status(thm)],[c_4467,c_4380])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden('#skF_3'(A_17,B_18),B_18)
      | r2_hidden('#skF_5'(A_17,B_18),B_18)
      | k2_relat_1(A_17) = B_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5771,plain,
    ( r2_hidden('#skF_5'('#skF_13','#skF_12'),'#skF_12')
    | k2_relat_1('#skF_13') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_5758,c_32])).

tff(c_5808,plain,(
    r2_hidden('#skF_5'('#skF_13','#skF_12'),'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_193,c_5771])).

tff(c_84,plain,(
    ! [D_93] :
      ( r2_hidden('#skF_14'(D_93),'#skF_11')
      | ~ r2_hidden(D_93,'#skF_12') ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_78,plain,(
    v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_166,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_170,plain,(
    k1_relset_1('#skF_11','#skF_12','#skF_13') = k1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_76,c_166])).

tff(c_4706,plain,(
    ! [B_464,A_465,C_466] :
      ( k1_xboole_0 = B_464
      | k1_relset_1(A_465,B_464,C_466) = A_465
      | ~ v1_funct_2(C_466,A_465,B_464)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_465,B_464))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4709,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_11'
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_76,c_4706])).

tff(c_4712,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_relat_1('#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_170,c_4709])).

tff(c_4713,plain,(
    k1_relat_1('#skF_13') = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_4712])).

tff(c_93,plain,(
    ! [C_100,A_101,B_102] :
      ( v1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_97,plain,(
    v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_76,c_93])).

tff(c_80,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_82,plain,(
    ! [D_93] :
      ( k1_funct_1('#skF_13','#skF_14'(D_93)) = D_93
      | ~ r2_hidden(D_93,'#skF_12') ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2835,plain,(
    ! [A_342,D_343] :
      ( r2_hidden(k1_funct_1(A_342,D_343),k2_relat_1(A_342))
      | ~ r2_hidden(D_343,k1_relat_1(A_342))
      | ~ v1_funct_1(A_342)
      | ~ v1_relat_1(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2851,plain,(
    ! [D_93] :
      ( r2_hidden(D_93,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_14'(D_93),k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden(D_93,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2835])).

tff(c_2859,plain,(
    ! [D_93] :
      ( r2_hidden(D_93,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_14'(D_93),k1_relat_1('#skF_13'))
      | ~ r2_hidden(D_93,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_80,c_2851])).

tff(c_4827,plain,(
    ! [D_472] :
      ( r2_hidden(D_472,k2_relat_1('#skF_13'))
      | ~ r2_hidden('#skF_14'(D_472),'#skF_11')
      | ~ r2_hidden(D_472,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4713,c_2859])).

tff(c_4836,plain,(
    ! [D_93] :
      ( r2_hidden(D_93,k2_relat_1('#skF_13'))
      | ~ r2_hidden(D_93,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_84,c_4827])).

tff(c_24,plain,(
    ! [A_17,C_32] :
      ( r2_hidden(k4_tarski('#skF_6'(A_17,k2_relat_1(A_17),C_32),C_32),A_17)
      | ~ r2_hidden(C_32,k2_relat_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5004,plain,(
    ! [A_479,B_480,D_481] :
      ( r2_hidden(k4_tarski('#skF_4'(A_479,B_480),'#skF_3'(A_479,B_480)),A_479)
      | ~ r2_hidden(k4_tarski(D_481,'#skF_5'(A_479,B_480)),A_479)
      | k2_relat_1(A_479) = B_480 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8823,plain,(
    ! [A_643,B_644] :
      ( r2_hidden(k4_tarski('#skF_4'(A_643,B_644),'#skF_3'(A_643,B_644)),A_643)
      | k2_relat_1(A_643) = B_644
      | ~ r2_hidden('#skF_5'(A_643,B_644),k2_relat_1(A_643)) ) ),
    inference(resolution,[status(thm)],[c_24,c_5004])).

tff(c_9036,plain,(
    ! [B_647] :
      ( r2_hidden('#skF_3'('#skF_13',B_647),'#skF_12')
      | k2_relat_1('#skF_13') = B_647
      | ~ r2_hidden('#skF_5'('#skF_13',B_647),k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_8823,c_4380])).

tff(c_9073,plain,(
    ! [B_648] :
      ( r2_hidden('#skF_3'('#skF_13',B_648),'#skF_12')
      | k2_relat_1('#skF_13') = B_648
      | ~ r2_hidden('#skF_5'('#skF_13',B_648),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_4836,c_9036])).

tff(c_28,plain,(
    ! [A_17,B_18,D_31] :
      ( ~ r2_hidden('#skF_3'(A_17,B_18),B_18)
      | ~ r2_hidden(k4_tarski(D_31,'#skF_5'(A_17,B_18)),A_17)
      | k2_relat_1(A_17) = B_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_9078,plain,(
    ! [D_31] :
      ( ~ r2_hidden(k4_tarski(D_31,'#skF_5'('#skF_13','#skF_12')),'#skF_13')
      | k2_relat_1('#skF_13') = '#skF_12'
      | ~ r2_hidden('#skF_5'('#skF_13','#skF_12'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_9073,c_28])).

tff(c_9093,plain,(
    ! [D_31] :
      ( ~ r2_hidden(k4_tarski(D_31,'#skF_5'('#skF_13','#skF_12')),'#skF_13')
      | k2_relat_1('#skF_13') = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5808,c_9078])).

tff(c_9102,plain,(
    ! [D_649] : ~ r2_hidden(k4_tarski(D_649,'#skF_5'('#skF_13','#skF_12')),'#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_9093])).

tff(c_9110,plain,(
    ~ r2_hidden('#skF_5'('#skF_13','#skF_12'),k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_24,c_9102])).

tff(c_9205,plain,(
    ~ r2_hidden('#skF_5'('#skF_13','#skF_12'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_4836,c_9110])).

tff(c_9212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5808,c_9205])).

tff(c_9213,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_4712])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_157,plain,(
    ! [A_132,B_133] :
      ( r2_hidden('#skF_1'(A_132,B_133),B_133)
      | r2_hidden('#skF_2'(A_132,B_133),A_132)
      | B_133 = A_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [B_77,A_76] :
      ( ~ r1_tarski(B_77,A_76)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_264,plain,(
    ! [A_157,B_158] :
      ( ~ r1_tarski(A_157,'#skF_2'(A_157,B_158))
      | r2_hidden('#skF_1'(A_157,B_158),B_158)
      | B_158 = A_157 ) ),
    inference(resolution,[status(thm)],[c_157,c_54])).

tff(c_268,plain,(
    ! [B_158] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_158),B_158)
      | k1_xboole_0 = B_158 ) ),
    inference(resolution,[status(thm)],[c_10,c_264])).

tff(c_294,plain,(
    ! [A_161,C_162] :
      ( r2_hidden(k4_tarski('#skF_6'(A_161,k2_relat_1(A_161),C_162),C_162),A_161)
      | ~ r2_hidden(C_162,k2_relat_1(A_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2922,plain,(
    ! [A_356,C_357] :
      ( ~ r1_tarski(A_356,k4_tarski('#skF_6'(A_356,k2_relat_1(A_356),C_357),C_357))
      | ~ r2_hidden(C_357,k2_relat_1(A_356)) ) ),
    inference(resolution,[status(thm)],[c_294,c_54])).

tff(c_2929,plain,(
    ! [C_358] : ~ r2_hidden(C_358,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_10,c_2922])).

tff(c_2964,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_2929])).

tff(c_2927,plain,(
    ! [C_357] : ~ r2_hidden(C_357,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_10,c_2922])).

tff(c_2970,plain,(
    ! [C_357] : ~ r2_hidden(C_357,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2964,c_2927])).

tff(c_9232,plain,(
    ! [C_357] : ~ r2_hidden(C_357,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9213,c_2970])).

tff(c_124,plain,(
    ! [C_112,A_113,D_114] :
      ( r2_hidden(C_112,k2_relat_1(A_113))
      | ~ r2_hidden(k4_tarski(D_114,C_112),A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_145,plain,(
    ! [C_127,B_128,D_129] :
      ( r2_hidden(C_127,k2_relat_1(B_128))
      | v1_xboole_0(B_128)
      | ~ m1_subset_1(k4_tarski(D_129,C_127),B_128) ) ),
    inference(resolution,[status(thm)],[c_18,c_124])).

tff(c_148,plain,(
    ! [C_127,D_129] :
      ( r2_hidden(C_127,k2_relat_1(k2_zfmisc_1('#skF_11','#skF_12')))
      | v1_xboole_0(k2_zfmisc_1('#skF_11','#skF_12'))
      | ~ r2_hidden(k4_tarski(D_129,C_127),'#skF_13') ) ),
    inference(resolution,[status(thm)],[c_138,c_145])).

tff(c_151,plain,(
    ! [C_127,D_129] :
      ( r2_hidden(C_127,k2_relat_1(k2_zfmisc_1('#skF_11','#skF_12')))
      | ~ r2_hidden(k4_tarski(D_129,C_127),'#skF_13') ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_148])).

tff(c_353,plain,(
    ! [C_166] :
      ( r2_hidden(C_166,k2_relat_1(k2_zfmisc_1('#skF_11','#skF_12')))
      | ~ r2_hidden(C_166,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_294,c_151])).

tff(c_14,plain,(
    ! [B_6,D_8,A_5,C_7] :
      ( r2_hidden(B_6,D_8)
      | ~ r2_hidden(k4_tarski(A_5,B_6),k2_zfmisc_1(C_7,D_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_314,plain,(
    ! [C_162,D_8,C_7] :
      ( r2_hidden(C_162,D_8)
      | ~ r2_hidden(C_162,k2_relat_1(k2_zfmisc_1(C_7,D_8))) ) ),
    inference(resolution,[status(thm)],[c_294,c_14])).

tff(c_381,plain,(
    ! [C_167] :
      ( r2_hidden(C_167,'#skF_12')
      | ~ r2_hidden(C_167,k2_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_353,c_314])).

tff(c_411,plain,
    ( r2_hidden('#skF_1'(k1_xboole_0,k2_relat_1('#skF_13')),'#skF_12')
    | k2_relat_1('#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_381])).

tff(c_418,plain,(
    k2_relat_1('#skF_13') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_422,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_193])).

tff(c_566,plain,(
    ! [A_179,D_180] :
      ( r2_hidden(k1_funct_1(A_179,D_180),k2_relat_1(A_179))
      | ~ r2_hidden(D_180,k1_relat_1(A_179))
      | ~ v1_funct_1(A_179)
      | ~ v1_relat_1(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_576,plain,(
    ! [D_180] :
      ( r2_hidden(k1_funct_1('#skF_13',D_180),k1_xboole_0)
      | ~ r2_hidden(D_180,k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_566])).

tff(c_586,plain,(
    ! [D_181] :
      ( r2_hidden(k1_funct_1('#skF_13',D_181),k1_xboole_0)
      | ~ r2_hidden(D_181,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_80,c_576])).

tff(c_592,plain,(
    ! [D_181] :
      ( ~ r1_tarski(k1_xboole_0,k1_funct_1('#skF_13',D_181))
      | ~ r2_hidden(D_181,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_586,c_54])).

tff(c_600,plain,(
    ! [D_182] : ~ r2_hidden(D_182,k1_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_592])).

tff(c_630,plain,(
    k1_relat_1('#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_268,c_600])).

tff(c_637,plain,(
    k1_relset_1('#skF_11','#skF_12','#skF_13') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_170])).

tff(c_1633,plain,(
    ! [B_273,A_274,C_275] :
      ( k1_xboole_0 = B_273
      | k1_relset_1(A_274,B_273,C_275) = A_274
      | ~ v1_funct_2(C_275,A_274,B_273)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_274,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1636,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_11'
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_76,c_1633])).

tff(c_1639,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_637,c_1636])).

tff(c_1640,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_1639])).

tff(c_1662,plain,(
    '#skF_11' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1640,c_422])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),A_1)
      | B_2 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_599,plain,(
    ! [D_181] : ~ r2_hidden(D_181,k1_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_592])).

tff(c_636,plain,(
    ! [D_181] : ~ r2_hidden(D_181,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_599])).

tff(c_1659,plain,(
    ! [D_181] : ~ r2_hidden(D_181,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1640,c_636])).

tff(c_2178,plain,(
    ! [D_294] : ~ r2_hidden(D_294,'#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_1659,c_84])).

tff(c_2474,plain,(
    ! [B_307] :
      ( r2_hidden('#skF_1'('#skF_12',B_307),B_307)
      | B_307 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_8,c_2178])).

tff(c_2490,plain,(
    '#skF_11' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_2474,c_1659])).

tff(c_2521,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1662,c_2490])).

tff(c_2522,plain,(
    r2_hidden('#skF_1'(k1_xboole_0,k2_relat_1('#skF_13')),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_9243,plain,(
    r2_hidden('#skF_1'('#skF_12',k2_relat_1('#skF_13')),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9213,c_2522])).

tff(c_9891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9232,c_9243])).

tff(c_9892,plain,(
    ! [A_111] : ~ r2_hidden(A_111,'#skF_13') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_9937,plain,(
    ! [B_695] :
      ( r2_hidden('#skF_1'('#skF_13',B_695),B_695)
      | B_695 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_9923,c_9892])).

tff(c_10107,plain,(
    ! [A_726,C_727] :
      ( r2_hidden(k4_tarski('#skF_6'(A_726,k2_relat_1(A_726),C_727),C_727),A_726)
      | ~ r2_hidden(C_727,k2_relat_1(A_726)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10131,plain,(
    ! [C_728] : ~ r2_hidden(C_728,k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_10107,c_9892])).

tff(c_10162,plain,(
    k2_relat_1('#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_9937,c_10131])).

tff(c_9985,plain,(
    ! [A_702,B_703,C_704] :
      ( k2_relset_1(A_702,B_703,C_704) = k2_relat_1(C_704)
      | ~ m1_subset_1(C_704,k1_zfmisc_1(k2_zfmisc_1(A_702,B_703))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_9989,plain,(
    k2_relset_1('#skF_11','#skF_12','#skF_13') = k2_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_76,c_9985])).

tff(c_9990,plain,(
    k2_relat_1('#skF_13') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9989,c_74])).

tff(c_10168,plain,(
    '#skF_13' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10162,c_9990])).

tff(c_9949,plain,(
    ! [B_698] :
      ( r2_hidden('#skF_1'('#skF_13',B_698),B_698)
      | B_698 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_9923,c_9892])).

tff(c_9960,plain,(
    ! [B_699] :
      ( ~ r1_tarski(B_699,'#skF_1'('#skF_13',B_699))
      | B_699 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_9949,c_54])).

tff(c_9965,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(resolution,[status(thm)],[c_10,c_9960])).

tff(c_9967,plain,(
    ! [A_4] : r1_tarski('#skF_13',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9965,c_10])).

tff(c_10054,plain,(
    ! [B_716,A_717] :
      ( ~ r1_tarski(B_716,'#skF_1'(A_717,B_716))
      | r2_hidden('#skF_2'(A_717,B_716),A_717)
      | B_716 = A_717 ) ),
    inference(resolution,[status(thm)],[c_9923,c_54])).

tff(c_10058,plain,(
    ! [A_717] :
      ( r2_hidden('#skF_2'(A_717,'#skF_13'),A_717)
      | A_717 = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_9967,c_10054])).

tff(c_10223,plain,(
    ! [A_732,D_733] :
      ( r2_hidden(k1_funct_1(A_732,D_733),k2_relat_1(A_732))
      | ~ r2_hidden(D_733,k1_relat_1(A_732))
      | ~ v1_funct_1(A_732)
      | ~ v1_relat_1(A_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10233,plain,(
    ! [D_733] :
      ( r2_hidden(k1_funct_1('#skF_13',D_733),'#skF_13')
      | ~ r2_hidden(D_733,k1_relat_1('#skF_13'))
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10162,c_10223])).

tff(c_10240,plain,(
    ! [D_733] :
      ( r2_hidden(k1_funct_1('#skF_13',D_733),'#skF_13')
      | ~ r2_hidden(D_733,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_80,c_10233])).

tff(c_10245,plain,(
    ! [D_734] : ~ r2_hidden(D_734,k1_relat_1('#skF_13')) ),
    inference(negUnitSimplification,[status(thm)],[c_9892,c_10240])).

tff(c_10276,plain,(
    k1_relat_1('#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_9937,c_10245])).

tff(c_9995,plain,(
    ! [A_705,B_706,C_707] :
      ( k1_relset_1(A_705,B_706,C_707) = k1_relat_1(C_707)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(k2_zfmisc_1(A_705,B_706))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_9999,plain,(
    k1_relset_1('#skF_11','#skF_12','#skF_13') = k1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_76,c_9995])).

tff(c_10282,plain,(
    k1_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10276,c_9999])).

tff(c_72,plain,(
    ! [B_88,A_87,C_89] :
      ( k1_xboole_0 = B_88
      | k1_relset_1(A_87,B_88,C_89) = A_87
      | ~ v1_funct_2(C_89,A_87,B_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_11538,plain,(
    ! [B_860,A_861,C_862] :
      ( B_860 = '#skF_13'
      | k1_relset_1(A_861,B_860,C_862) = A_861
      | ~ v1_funct_2(C_862,A_861,B_860)
      | ~ m1_subset_1(C_862,k1_zfmisc_1(k2_zfmisc_1(A_861,B_860))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9965,c_72])).

tff(c_11541,plain,
    ( '#skF_13' = '#skF_12'
    | k1_relset_1('#skF_11','#skF_12','#skF_13') = '#skF_11'
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(resolution,[status(thm)],[c_76,c_11538])).

tff(c_11544,plain,
    ( '#skF_13' = '#skF_12'
    | '#skF_11' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_10282,c_11541])).

tff(c_11545,plain,(
    '#skF_11' = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_10168,c_11544])).

tff(c_87,plain,(
    ! [D_98] :
      ( r2_hidden('#skF_14'(D_98),'#skF_11')
      | ~ r2_hidden(D_98,'#skF_12') ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_91,plain,(
    ! [D_98] :
      ( ~ r1_tarski('#skF_11','#skF_14'(D_98))
      | ~ r2_hidden(D_98,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_87,c_54])).

tff(c_11565,plain,(
    ! [D_98] :
      ( ~ r1_tarski('#skF_13','#skF_14'(D_98))
      | ~ r2_hidden(D_98,'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11545,c_91])).

tff(c_11578,plain,(
    ! [D_863] : ~ r2_hidden(D_863,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9967,c_11565])).

tff(c_11598,plain,(
    '#skF_13' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_10058,c_11578])).

tff(c_11624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10168,c_11598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.42/2.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.42/2.98  
% 8.42/2.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.42/2.98  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_3 > #skF_13 > #skF_8 > #skF_14 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10
% 8.42/2.98  
% 8.42/2.98  %Foreground sorts:
% 8.42/2.98  
% 8.42/2.98  
% 8.42/2.98  %Background operators:
% 8.42/2.98  
% 8.42/2.98  
% 8.42/2.98  %Foreground operators:
% 8.42/2.98  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.42/2.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.42/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.42/2.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.42/2.98  tff('#skF_11', type, '#skF_11': $i).
% 8.42/2.98  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 8.42/2.98  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.42/2.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.42/2.98  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.42/2.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.42/2.98  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.42/2.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.42/2.98  tff('#skF_13', type, '#skF_13': $i).
% 8.42/2.98  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 8.42/2.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.42/2.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.42/2.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.42/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.42/2.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.42/2.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.42/2.98  tff('#skF_14', type, '#skF_14': $i > $i).
% 8.42/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.42/2.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.42/2.98  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 8.42/2.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.42/2.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.42/2.98  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 8.42/2.98  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.42/2.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.42/2.98  tff('#skF_12', type, '#skF_12': $i).
% 8.42/2.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.42/2.98  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 8.42/2.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.42/2.98  
% 8.42/3.01  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 8.42/3.01  tff(f_136, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 8.42/3.01  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.42/3.01  tff(f_67, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 8.42/3.01  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 8.42/3.01  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 8.42/3.01  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 8.42/3.01  tff(f_40, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 8.42/3.01  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.42/3.01  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.42/3.01  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.42/3.01  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 8.42/3.01  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.42/3.01  tff(f_87, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.42/3.01  tff(c_9923, plain, (![A_694, B_695]: (r2_hidden('#skF_1'(A_694, B_695), B_695) | r2_hidden('#skF_2'(A_694, B_695), A_694) | B_695=A_694)), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.42/3.01  tff(c_76, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.42/3.01  tff(c_188, plain, (![A_139, B_140, C_141]: (k2_relset_1(A_139, B_140, C_141)=k2_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.42/3.01  tff(c_192, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')=k2_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_76, c_188])).
% 8.42/3.01  tff(c_74, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.42/3.01  tff(c_193, plain, (k2_relat_1('#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_74])).
% 8.42/3.01  tff(c_4467, plain, (![A_455, B_456]: (r2_hidden(k4_tarski('#skF_4'(A_455, B_456), '#skF_3'(A_455, B_456)), A_455) | r2_hidden('#skF_5'(A_455, B_456), B_456) | k2_relat_1(A_455)=B_456)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.42/3.01  tff(c_119, plain, (![C_109, B_110, A_111]: (~v1_xboole_0(C_109) | ~m1_subset_1(B_110, k1_zfmisc_1(C_109)) | ~r2_hidden(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.42/3.01  tff(c_122, plain, (![A_111]: (~v1_xboole_0(k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(A_111, '#skF_13'))), inference(resolution, [status(thm)], [c_76, c_119])).
% 8.42/3.01  tff(c_123, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_11', '#skF_12'))), inference(splitLeft, [status(thm)], [c_122])).
% 8.42/3.01  tff(c_135, plain, (![A_119, C_120, B_121]: (m1_subset_1(A_119, C_120) | ~m1_subset_1(B_121, k1_zfmisc_1(C_120)) | ~r2_hidden(A_119, B_121))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.42/3.01  tff(c_138, plain, (![A_119]: (m1_subset_1(A_119, k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(A_119, '#skF_13'))), inference(resolution, [status(thm)], [c_76, c_135])).
% 8.42/3.01  tff(c_18, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.42/3.01  tff(c_130, plain, (![B_115, D_116, A_117, C_118]: (r2_hidden(B_115, D_116) | ~r2_hidden(k4_tarski(A_117, B_115), k2_zfmisc_1(C_118, D_116)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.42/3.01  tff(c_4373, plain, (![B_441, D_442, C_443, A_444]: (r2_hidden(B_441, D_442) | v1_xboole_0(k2_zfmisc_1(C_443, D_442)) | ~m1_subset_1(k4_tarski(A_444, B_441), k2_zfmisc_1(C_443, D_442)))), inference(resolution, [status(thm)], [c_18, c_130])).
% 8.42/3.01  tff(c_4377, plain, (![B_441, A_444]: (r2_hidden(B_441, '#skF_12') | v1_xboole_0(k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(k4_tarski(A_444, B_441), '#skF_13'))), inference(resolution, [status(thm)], [c_138, c_4373])).
% 8.42/3.01  tff(c_4380, plain, (![B_441, A_444]: (r2_hidden(B_441, '#skF_12') | ~r2_hidden(k4_tarski(A_444, B_441), '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_123, c_4377])).
% 8.42/3.01  tff(c_5758, plain, (![B_509]: (r2_hidden('#skF_3'('#skF_13', B_509), '#skF_12') | r2_hidden('#skF_5'('#skF_13', B_509), B_509) | k2_relat_1('#skF_13')=B_509)), inference(resolution, [status(thm)], [c_4467, c_4380])).
% 8.42/3.01  tff(c_32, plain, (![A_17, B_18]: (~r2_hidden('#skF_3'(A_17, B_18), B_18) | r2_hidden('#skF_5'(A_17, B_18), B_18) | k2_relat_1(A_17)=B_18)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.42/3.01  tff(c_5771, plain, (r2_hidden('#skF_5'('#skF_13', '#skF_12'), '#skF_12') | k2_relat_1('#skF_13')='#skF_12'), inference(resolution, [status(thm)], [c_5758, c_32])).
% 8.42/3.01  tff(c_5808, plain, (r2_hidden('#skF_5'('#skF_13', '#skF_12'), '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_193, c_193, c_5771])).
% 8.42/3.01  tff(c_84, plain, (![D_93]: (r2_hidden('#skF_14'(D_93), '#skF_11') | ~r2_hidden(D_93, '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.42/3.01  tff(c_78, plain, (v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.42/3.01  tff(c_166, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.42/3.01  tff(c_170, plain, (k1_relset_1('#skF_11', '#skF_12', '#skF_13')=k1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_76, c_166])).
% 8.42/3.01  tff(c_4706, plain, (![B_464, A_465, C_466]: (k1_xboole_0=B_464 | k1_relset_1(A_465, B_464, C_466)=A_465 | ~v1_funct_2(C_466, A_465, B_464) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_465, B_464))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.42/3.01  tff(c_4709, plain, (k1_xboole_0='#skF_12' | k1_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_11' | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(resolution, [status(thm)], [c_76, c_4706])).
% 8.42/3.01  tff(c_4712, plain, (k1_xboole_0='#skF_12' | k1_relat_1('#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_170, c_4709])).
% 8.42/3.01  tff(c_4713, plain, (k1_relat_1('#skF_13')='#skF_11'), inference(splitLeft, [status(thm)], [c_4712])).
% 8.42/3.01  tff(c_93, plain, (![C_100, A_101, B_102]: (v1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.42/3.01  tff(c_97, plain, (v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_76, c_93])).
% 8.42/3.01  tff(c_80, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.42/3.01  tff(c_82, plain, (![D_93]: (k1_funct_1('#skF_13', '#skF_14'(D_93))=D_93 | ~r2_hidden(D_93, '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.42/3.01  tff(c_2835, plain, (![A_342, D_343]: (r2_hidden(k1_funct_1(A_342, D_343), k2_relat_1(A_342)) | ~r2_hidden(D_343, k1_relat_1(A_342)) | ~v1_funct_1(A_342) | ~v1_relat_1(A_342))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.42/3.01  tff(c_2851, plain, (![D_93]: (r2_hidden(D_93, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_14'(D_93), k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden(D_93, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_2835])).
% 8.42/3.01  tff(c_2859, plain, (![D_93]: (r2_hidden(D_93, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_14'(D_93), k1_relat_1('#skF_13')) | ~r2_hidden(D_93, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_80, c_2851])).
% 8.42/3.01  tff(c_4827, plain, (![D_472]: (r2_hidden(D_472, k2_relat_1('#skF_13')) | ~r2_hidden('#skF_14'(D_472), '#skF_11') | ~r2_hidden(D_472, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_4713, c_2859])).
% 8.42/3.01  tff(c_4836, plain, (![D_93]: (r2_hidden(D_93, k2_relat_1('#skF_13')) | ~r2_hidden(D_93, '#skF_12'))), inference(resolution, [status(thm)], [c_84, c_4827])).
% 8.42/3.01  tff(c_24, plain, (![A_17, C_32]: (r2_hidden(k4_tarski('#skF_6'(A_17, k2_relat_1(A_17), C_32), C_32), A_17) | ~r2_hidden(C_32, k2_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.42/3.01  tff(c_5004, plain, (![A_479, B_480, D_481]: (r2_hidden(k4_tarski('#skF_4'(A_479, B_480), '#skF_3'(A_479, B_480)), A_479) | ~r2_hidden(k4_tarski(D_481, '#skF_5'(A_479, B_480)), A_479) | k2_relat_1(A_479)=B_480)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.42/3.01  tff(c_8823, plain, (![A_643, B_644]: (r2_hidden(k4_tarski('#skF_4'(A_643, B_644), '#skF_3'(A_643, B_644)), A_643) | k2_relat_1(A_643)=B_644 | ~r2_hidden('#skF_5'(A_643, B_644), k2_relat_1(A_643)))), inference(resolution, [status(thm)], [c_24, c_5004])).
% 8.42/3.01  tff(c_9036, plain, (![B_647]: (r2_hidden('#skF_3'('#skF_13', B_647), '#skF_12') | k2_relat_1('#skF_13')=B_647 | ~r2_hidden('#skF_5'('#skF_13', B_647), k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_8823, c_4380])).
% 8.42/3.01  tff(c_9073, plain, (![B_648]: (r2_hidden('#skF_3'('#skF_13', B_648), '#skF_12') | k2_relat_1('#skF_13')=B_648 | ~r2_hidden('#skF_5'('#skF_13', B_648), '#skF_12'))), inference(resolution, [status(thm)], [c_4836, c_9036])).
% 8.42/3.01  tff(c_28, plain, (![A_17, B_18, D_31]: (~r2_hidden('#skF_3'(A_17, B_18), B_18) | ~r2_hidden(k4_tarski(D_31, '#skF_5'(A_17, B_18)), A_17) | k2_relat_1(A_17)=B_18)), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.42/3.01  tff(c_9078, plain, (![D_31]: (~r2_hidden(k4_tarski(D_31, '#skF_5'('#skF_13', '#skF_12')), '#skF_13') | k2_relat_1('#skF_13')='#skF_12' | ~r2_hidden('#skF_5'('#skF_13', '#skF_12'), '#skF_12'))), inference(resolution, [status(thm)], [c_9073, c_28])).
% 8.42/3.01  tff(c_9093, plain, (![D_31]: (~r2_hidden(k4_tarski(D_31, '#skF_5'('#skF_13', '#skF_12')), '#skF_13') | k2_relat_1('#skF_13')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_5808, c_9078])).
% 8.42/3.01  tff(c_9102, plain, (![D_649]: (~r2_hidden(k4_tarski(D_649, '#skF_5'('#skF_13', '#skF_12')), '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_193, c_9093])).
% 8.42/3.01  tff(c_9110, plain, (~r2_hidden('#skF_5'('#skF_13', '#skF_12'), k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_24, c_9102])).
% 8.42/3.01  tff(c_9205, plain, (~r2_hidden('#skF_5'('#skF_13', '#skF_12'), '#skF_12')), inference(resolution, [status(thm)], [c_4836, c_9110])).
% 8.42/3.01  tff(c_9212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5808, c_9205])).
% 8.42/3.01  tff(c_9213, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_4712])).
% 8.42/3.01  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.42/3.01  tff(c_157, plain, (![A_132, B_133]: (r2_hidden('#skF_1'(A_132, B_133), B_133) | r2_hidden('#skF_2'(A_132, B_133), A_132) | B_133=A_132)), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.42/3.01  tff(c_54, plain, (![B_77, A_76]: (~r1_tarski(B_77, A_76) | ~r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.42/3.01  tff(c_264, plain, (![A_157, B_158]: (~r1_tarski(A_157, '#skF_2'(A_157, B_158)) | r2_hidden('#skF_1'(A_157, B_158), B_158) | B_158=A_157)), inference(resolution, [status(thm)], [c_157, c_54])).
% 8.42/3.01  tff(c_268, plain, (![B_158]: (r2_hidden('#skF_1'(k1_xboole_0, B_158), B_158) | k1_xboole_0=B_158)), inference(resolution, [status(thm)], [c_10, c_264])).
% 8.42/3.01  tff(c_294, plain, (![A_161, C_162]: (r2_hidden(k4_tarski('#skF_6'(A_161, k2_relat_1(A_161), C_162), C_162), A_161) | ~r2_hidden(C_162, k2_relat_1(A_161)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.42/3.01  tff(c_2922, plain, (![A_356, C_357]: (~r1_tarski(A_356, k4_tarski('#skF_6'(A_356, k2_relat_1(A_356), C_357), C_357)) | ~r2_hidden(C_357, k2_relat_1(A_356)))), inference(resolution, [status(thm)], [c_294, c_54])).
% 8.42/3.01  tff(c_2929, plain, (![C_358]: (~r2_hidden(C_358, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_10, c_2922])).
% 8.42/3.01  tff(c_2964, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_268, c_2929])).
% 8.42/3.01  tff(c_2927, plain, (![C_357]: (~r2_hidden(C_357, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_10, c_2922])).
% 8.42/3.01  tff(c_2970, plain, (![C_357]: (~r2_hidden(C_357, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2964, c_2927])).
% 8.42/3.01  tff(c_9232, plain, (![C_357]: (~r2_hidden(C_357, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_9213, c_2970])).
% 8.42/3.01  tff(c_124, plain, (![C_112, A_113, D_114]: (r2_hidden(C_112, k2_relat_1(A_113)) | ~r2_hidden(k4_tarski(D_114, C_112), A_113))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.42/3.01  tff(c_145, plain, (![C_127, B_128, D_129]: (r2_hidden(C_127, k2_relat_1(B_128)) | v1_xboole_0(B_128) | ~m1_subset_1(k4_tarski(D_129, C_127), B_128))), inference(resolution, [status(thm)], [c_18, c_124])).
% 8.42/3.01  tff(c_148, plain, (![C_127, D_129]: (r2_hidden(C_127, k2_relat_1(k2_zfmisc_1('#skF_11', '#skF_12'))) | v1_xboole_0(k2_zfmisc_1('#skF_11', '#skF_12')) | ~r2_hidden(k4_tarski(D_129, C_127), '#skF_13'))), inference(resolution, [status(thm)], [c_138, c_145])).
% 8.42/3.01  tff(c_151, plain, (![C_127, D_129]: (r2_hidden(C_127, k2_relat_1(k2_zfmisc_1('#skF_11', '#skF_12'))) | ~r2_hidden(k4_tarski(D_129, C_127), '#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_123, c_148])).
% 8.42/3.01  tff(c_353, plain, (![C_166]: (r2_hidden(C_166, k2_relat_1(k2_zfmisc_1('#skF_11', '#skF_12'))) | ~r2_hidden(C_166, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_294, c_151])).
% 8.42/3.01  tff(c_14, plain, (![B_6, D_8, A_5, C_7]: (r2_hidden(B_6, D_8) | ~r2_hidden(k4_tarski(A_5, B_6), k2_zfmisc_1(C_7, D_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.42/3.01  tff(c_314, plain, (![C_162, D_8, C_7]: (r2_hidden(C_162, D_8) | ~r2_hidden(C_162, k2_relat_1(k2_zfmisc_1(C_7, D_8))))), inference(resolution, [status(thm)], [c_294, c_14])).
% 8.42/3.01  tff(c_381, plain, (![C_167]: (r2_hidden(C_167, '#skF_12') | ~r2_hidden(C_167, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_353, c_314])).
% 8.42/3.01  tff(c_411, plain, (r2_hidden('#skF_1'(k1_xboole_0, k2_relat_1('#skF_13')), '#skF_12') | k2_relat_1('#skF_13')=k1_xboole_0), inference(resolution, [status(thm)], [c_268, c_381])).
% 8.42/3.01  tff(c_418, plain, (k2_relat_1('#skF_13')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_411])).
% 8.42/3.01  tff(c_422, plain, (k1_xboole_0!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_418, c_193])).
% 8.42/3.01  tff(c_566, plain, (![A_179, D_180]: (r2_hidden(k1_funct_1(A_179, D_180), k2_relat_1(A_179)) | ~r2_hidden(D_180, k1_relat_1(A_179)) | ~v1_funct_1(A_179) | ~v1_relat_1(A_179))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.42/3.01  tff(c_576, plain, (![D_180]: (r2_hidden(k1_funct_1('#skF_13', D_180), k1_xboole_0) | ~r2_hidden(D_180, k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_418, c_566])).
% 8.42/3.01  tff(c_586, plain, (![D_181]: (r2_hidden(k1_funct_1('#skF_13', D_181), k1_xboole_0) | ~r2_hidden(D_181, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_80, c_576])).
% 8.42/3.01  tff(c_592, plain, (![D_181]: (~r1_tarski(k1_xboole_0, k1_funct_1('#skF_13', D_181)) | ~r2_hidden(D_181, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_586, c_54])).
% 8.42/3.01  tff(c_600, plain, (![D_182]: (~r2_hidden(D_182, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_592])).
% 8.42/3.01  tff(c_630, plain, (k1_relat_1('#skF_13')=k1_xboole_0), inference(resolution, [status(thm)], [c_268, c_600])).
% 8.42/3.01  tff(c_637, plain, (k1_relset_1('#skF_11', '#skF_12', '#skF_13')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_630, c_170])).
% 8.42/3.01  tff(c_1633, plain, (![B_273, A_274, C_275]: (k1_xboole_0=B_273 | k1_relset_1(A_274, B_273, C_275)=A_274 | ~v1_funct_2(C_275, A_274, B_273) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_274, B_273))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.42/3.01  tff(c_1636, plain, (k1_xboole_0='#skF_12' | k1_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_11' | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(resolution, [status(thm)], [c_76, c_1633])).
% 8.42/3.01  tff(c_1639, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_637, c_1636])).
% 8.42/3.01  tff(c_1640, plain, (k1_xboole_0='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_422, c_1639])).
% 8.42/3.01  tff(c_1662, plain, ('#skF_11'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1640, c_422])).
% 8.42/3.01  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), A_1) | B_2=A_1)), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.42/3.01  tff(c_599, plain, (![D_181]: (~r2_hidden(D_181, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_592])).
% 8.42/3.01  tff(c_636, plain, (![D_181]: (~r2_hidden(D_181, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_630, c_599])).
% 8.42/3.01  tff(c_1659, plain, (![D_181]: (~r2_hidden(D_181, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1640, c_636])).
% 8.42/3.01  tff(c_2178, plain, (![D_294]: (~r2_hidden(D_294, '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_1659, c_84])).
% 8.42/3.01  tff(c_2474, plain, (![B_307]: (r2_hidden('#skF_1'('#skF_12', B_307), B_307) | B_307='#skF_12')), inference(resolution, [status(thm)], [c_8, c_2178])).
% 8.42/3.01  tff(c_2490, plain, ('#skF_11'='#skF_12'), inference(resolution, [status(thm)], [c_2474, c_1659])).
% 8.42/3.01  tff(c_2521, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1662, c_2490])).
% 8.42/3.01  tff(c_2522, plain, (r2_hidden('#skF_1'(k1_xboole_0, k2_relat_1('#skF_13')), '#skF_12')), inference(splitRight, [status(thm)], [c_411])).
% 8.42/3.01  tff(c_9243, plain, (r2_hidden('#skF_1'('#skF_12', k2_relat_1('#skF_13')), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_9213, c_2522])).
% 8.42/3.01  tff(c_9891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9232, c_9243])).
% 8.42/3.01  tff(c_9892, plain, (![A_111]: (~r2_hidden(A_111, '#skF_13'))), inference(splitRight, [status(thm)], [c_122])).
% 8.42/3.01  tff(c_9937, plain, (![B_695]: (r2_hidden('#skF_1'('#skF_13', B_695), B_695) | B_695='#skF_13')), inference(resolution, [status(thm)], [c_9923, c_9892])).
% 8.42/3.01  tff(c_10107, plain, (![A_726, C_727]: (r2_hidden(k4_tarski('#skF_6'(A_726, k2_relat_1(A_726), C_727), C_727), A_726) | ~r2_hidden(C_727, k2_relat_1(A_726)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.42/3.01  tff(c_10131, plain, (![C_728]: (~r2_hidden(C_728, k2_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_10107, c_9892])).
% 8.42/3.01  tff(c_10162, plain, (k2_relat_1('#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_9937, c_10131])).
% 8.42/3.01  tff(c_9985, plain, (![A_702, B_703, C_704]: (k2_relset_1(A_702, B_703, C_704)=k2_relat_1(C_704) | ~m1_subset_1(C_704, k1_zfmisc_1(k2_zfmisc_1(A_702, B_703))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.42/3.01  tff(c_9989, plain, (k2_relset_1('#skF_11', '#skF_12', '#skF_13')=k2_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_76, c_9985])).
% 8.42/3.01  tff(c_9990, plain, (k2_relat_1('#skF_13')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_9989, c_74])).
% 8.42/3.01  tff(c_10168, plain, ('#skF_13'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_10162, c_9990])).
% 8.42/3.01  tff(c_9949, plain, (![B_698]: (r2_hidden('#skF_1'('#skF_13', B_698), B_698) | B_698='#skF_13')), inference(resolution, [status(thm)], [c_9923, c_9892])).
% 8.42/3.01  tff(c_9960, plain, (![B_699]: (~r1_tarski(B_699, '#skF_1'('#skF_13', B_699)) | B_699='#skF_13')), inference(resolution, [status(thm)], [c_9949, c_54])).
% 8.42/3.01  tff(c_9965, plain, (k1_xboole_0='#skF_13'), inference(resolution, [status(thm)], [c_10, c_9960])).
% 8.42/3.01  tff(c_9967, plain, (![A_4]: (r1_tarski('#skF_13', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_9965, c_10])).
% 8.42/3.01  tff(c_10054, plain, (![B_716, A_717]: (~r1_tarski(B_716, '#skF_1'(A_717, B_716)) | r2_hidden('#skF_2'(A_717, B_716), A_717) | B_716=A_717)), inference(resolution, [status(thm)], [c_9923, c_54])).
% 8.42/3.01  tff(c_10058, plain, (![A_717]: (r2_hidden('#skF_2'(A_717, '#skF_13'), A_717) | A_717='#skF_13')), inference(resolution, [status(thm)], [c_9967, c_10054])).
% 8.42/3.01  tff(c_10223, plain, (![A_732, D_733]: (r2_hidden(k1_funct_1(A_732, D_733), k2_relat_1(A_732)) | ~r2_hidden(D_733, k1_relat_1(A_732)) | ~v1_funct_1(A_732) | ~v1_relat_1(A_732))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.42/3.01  tff(c_10233, plain, (![D_733]: (r2_hidden(k1_funct_1('#skF_13', D_733), '#skF_13') | ~r2_hidden(D_733, k1_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_10162, c_10223])).
% 8.42/3.01  tff(c_10240, plain, (![D_733]: (r2_hidden(k1_funct_1('#skF_13', D_733), '#skF_13') | ~r2_hidden(D_733, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_80, c_10233])).
% 8.42/3.01  tff(c_10245, plain, (![D_734]: (~r2_hidden(D_734, k1_relat_1('#skF_13')))), inference(negUnitSimplification, [status(thm)], [c_9892, c_10240])).
% 8.42/3.01  tff(c_10276, plain, (k1_relat_1('#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_9937, c_10245])).
% 8.42/3.01  tff(c_9995, plain, (![A_705, B_706, C_707]: (k1_relset_1(A_705, B_706, C_707)=k1_relat_1(C_707) | ~m1_subset_1(C_707, k1_zfmisc_1(k2_zfmisc_1(A_705, B_706))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.42/3.01  tff(c_9999, plain, (k1_relset_1('#skF_11', '#skF_12', '#skF_13')=k1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_76, c_9995])).
% 8.42/3.01  tff(c_10282, plain, (k1_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_10276, c_9999])).
% 8.42/3.01  tff(c_72, plain, (![B_88, A_87, C_89]: (k1_xboole_0=B_88 | k1_relset_1(A_87, B_88, C_89)=A_87 | ~v1_funct_2(C_89, A_87, B_88) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.42/3.01  tff(c_11538, plain, (![B_860, A_861, C_862]: (B_860='#skF_13' | k1_relset_1(A_861, B_860, C_862)=A_861 | ~v1_funct_2(C_862, A_861, B_860) | ~m1_subset_1(C_862, k1_zfmisc_1(k2_zfmisc_1(A_861, B_860))))), inference(demodulation, [status(thm), theory('equality')], [c_9965, c_72])).
% 8.42/3.01  tff(c_11541, plain, ('#skF_13'='#skF_12' | k1_relset_1('#skF_11', '#skF_12', '#skF_13')='#skF_11' | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(resolution, [status(thm)], [c_76, c_11538])).
% 8.42/3.01  tff(c_11544, plain, ('#skF_13'='#skF_12' | '#skF_11'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_10282, c_11541])).
% 8.42/3.01  tff(c_11545, plain, ('#skF_11'='#skF_13'), inference(negUnitSimplification, [status(thm)], [c_10168, c_11544])).
% 8.42/3.01  tff(c_87, plain, (![D_98]: (r2_hidden('#skF_14'(D_98), '#skF_11') | ~r2_hidden(D_98, '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.42/3.01  tff(c_91, plain, (![D_98]: (~r1_tarski('#skF_11', '#skF_14'(D_98)) | ~r2_hidden(D_98, '#skF_12'))), inference(resolution, [status(thm)], [c_87, c_54])).
% 8.42/3.01  tff(c_11565, plain, (![D_98]: (~r1_tarski('#skF_13', '#skF_14'(D_98)) | ~r2_hidden(D_98, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_11545, c_91])).
% 8.42/3.01  tff(c_11578, plain, (![D_863]: (~r2_hidden(D_863, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_9967, c_11565])).
% 8.42/3.01  tff(c_11598, plain, ('#skF_13'='#skF_12'), inference(resolution, [status(thm)], [c_10058, c_11578])).
% 8.42/3.01  tff(c_11624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10168, c_11598])).
% 8.42/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.42/3.01  
% 8.42/3.01  Inference rules
% 8.42/3.01  ----------------------
% 8.42/3.01  #Ref     : 0
% 8.42/3.01  #Sup     : 2556
% 8.42/3.01  #Fact    : 0
% 8.42/3.01  #Define  : 0
% 8.42/3.01  #Split   : 32
% 8.42/3.01  #Chain   : 0
% 8.42/3.01  #Close   : 0
% 8.42/3.01  
% 8.42/3.01  Ordering : KBO
% 8.42/3.01  
% 8.42/3.01  Simplification rules
% 8.42/3.01  ----------------------
% 8.42/3.01  #Subsume      : 569
% 8.42/3.01  #Demod        : 770
% 8.42/3.01  #Tautology    : 295
% 8.42/3.01  #SimpNegUnit  : 210
% 8.42/3.01  #BackRed      : 171
% 8.42/3.01  
% 8.42/3.01  #Partial instantiations: 0
% 8.42/3.01  #Strategies tried      : 1
% 8.42/3.01  
% 8.42/3.01  Timing (in seconds)
% 8.42/3.01  ----------------------
% 8.42/3.01  Preprocessing        : 0.34
% 8.42/3.01  Parsing              : 0.17
% 8.42/3.01  CNF conversion       : 0.03
% 8.76/3.01  Main loop            : 1.88
% 8.76/3.01  Inferencing          : 0.57
% 8.76/3.01  Reduction            : 0.55
% 8.76/3.01  Demodulation         : 0.34
% 8.76/3.01  BG Simplification    : 0.08
% 8.76/3.01  Subsumption          : 0.49
% 8.76/3.01  Abstraction          : 0.10
% 8.76/3.01  MUC search           : 0.00
% 8.76/3.01  Cooper               : 0.00
% 8.76/3.01  Total                : 2.27
% 8.76/3.01  Index Insertion      : 0.00
% 8.76/3.01  Index Deletion       : 0.00
% 8.76/3.01  Index Matching       : 0.00
% 8.76/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
