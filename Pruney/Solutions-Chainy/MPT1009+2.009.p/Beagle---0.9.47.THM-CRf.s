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
% DateTime   : Thu Dec  3 10:14:43 EST 2020

% Result     : Theorem 6.20s
% Output     : CNFRefutation 6.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 361 expanded)
%              Number of leaves         :   40 ( 141 expanded)
%              Depth                    :   14
%              Number of atoms          :  149 ( 787 expanded)
%              Number of equality atoms :   39 ( 199 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_122,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_135,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_122])).

tff(c_40,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,A_20),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_26,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3225,plain,(
    ! [A_298,B_299,C_300,D_301] :
      ( k7_relset_1(A_298,B_299,C_300,D_301) = k9_relat_1(C_300,D_301)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_298,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3236,plain,(
    ! [D_301] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_301) = k9_relat_1('#skF_4',D_301) ),
    inference(resolution,[status(thm)],[c_62,c_3225])).

tff(c_3136,plain,(
    ! [B_287,A_288] :
      ( k1_tarski(k1_funct_1(B_287,A_288)) = k2_relat_1(B_287)
      | k1_tarski(A_288) != k1_relat_1(B_287)
      | ~ v1_funct_1(B_287)
      | ~ v1_relat_1(B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3145,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3136,c_58])).

tff(c_3151,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_66,c_3145])).

tff(c_3258,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3236,c_3151])).

tff(c_3259,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3258])).

tff(c_399,plain,(
    ! [C_86,A_87,B_88] :
      ( v4_relat_1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_414,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_399])).

tff(c_320,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(k1_relat_1(B_81),A_82)
      | ~ v4_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5270,plain,(
    ! [B_445,B_446] :
      ( k1_tarski(B_445) = k1_relat_1(B_446)
      | k1_relat_1(B_446) = k1_xboole_0
      | ~ v4_relat_1(B_446,k1_tarski(B_445))
      | ~ v1_relat_1(B_446) ) ),
    inference(resolution,[status(thm)],[c_320,c_16])).

tff(c_5328,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_5270])).

tff(c_5360,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_5328])).

tff(c_5361,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_3259,c_5360])).

tff(c_52,plain,(
    ! [B_35,A_34] :
      ( m1_subset_1(B_35,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_35),A_34)))
      | ~ r1_tarski(k2_relat_1(B_35),A_34)
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5393,plain,(
    ! [A_34] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A_34)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_34)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5361,c_52])).

tff(c_5433,plain,(
    ! [A_34] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_66,c_26,c_5393])).

tff(c_5504,plain,(
    ! [A_450] : ~ r1_tarski(k2_relat_1('#skF_4'),A_450) ),
    inference(splitLeft,[status(thm)],[c_5433])).

tff(c_5516,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_5504])).

tff(c_5517,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_5433])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5565,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5517,c_28])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_136,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_5663,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5565,c_148])).

tff(c_5739,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5663,c_8])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_162,plain,(
    ! [C_53] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_122])).

tff(c_168,plain,(
    ! [A_54] :
      ( v1_relat_1(A_54)
      | ~ r1_tarski(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_162])).

tff(c_177,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_168])).

tff(c_24,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_223,plain,(
    ! [C_64,B_65,A_66] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_246,plain,(
    ! [A_71,B_72,A_73] :
      ( v5_relat_1(A_71,B_72)
      | ~ r1_tarski(A_71,k2_zfmisc_1(A_73,B_72)) ) ),
    inference(resolution,[status(thm)],[c_30,c_223])).

tff(c_266,plain,(
    ! [A_73,B_72] : v5_relat_1(k2_zfmisc_1(A_73,B_72),B_72) ),
    inference(resolution,[status(thm)],[c_6,c_246])).

tff(c_291,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(k2_relat_1(B_79),A_80)
      | ~ v5_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_349,plain,(
    ! [B_83] :
      ( k2_relat_1(B_83) = k1_xboole_0
      | ~ v5_relat_1(B_83,k1_xboole_0)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_291,c_148])).

tff(c_353,plain,(
    ! [A_73] :
      ( k2_relat_1(k2_zfmisc_1(A_73,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_73,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_266,c_349])).

tff(c_364,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_24,c_24,c_353])).

tff(c_375,plain,(
    ! [A_20] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_20),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_40])).

tff(c_384,plain,(
    ! [A_84] : r1_tarski(k9_relat_1(k1_xboole_0,A_84),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_375])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_392,plain,(
    ! [A_84] :
      ( k9_relat_1(k1_xboole_0,A_84) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,A_84)) ) ),
    inference(resolution,[status(thm)],[c_384,c_2])).

tff(c_397,plain,(
    ! [A_84] : k9_relat_1(k1_xboole_0,A_84) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_392])).

tff(c_5725,plain,(
    ! [A_84] : k9_relat_1('#skF_4',A_84) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5663,c_5663,c_397])).

tff(c_3243,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3236,c_58])).

tff(c_6273,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5725,c_3243])).

tff(c_6277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5739,c_6273])).

tff(c_6278,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3258])).

tff(c_6361,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_6278])).

tff(c_6365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_6361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.20/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.20/2.17  
% 6.20/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.20/2.17  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.20/2.17  
% 6.20/2.17  %Foreground sorts:
% 6.20/2.17  
% 6.20/2.17  
% 6.20/2.17  %Background operators:
% 6.20/2.17  
% 6.20/2.17  
% 6.20/2.17  %Foreground operators:
% 6.20/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.20/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.20/2.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.20/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.20/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.20/2.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.20/2.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.20/2.17  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.20/2.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.20/2.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.20/2.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.20/2.17  tff('#skF_2', type, '#skF_2': $i).
% 6.20/2.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.20/2.17  tff('#skF_3', type, '#skF_3': $i).
% 6.20/2.17  tff('#skF_1', type, '#skF_1': $i).
% 6.20/2.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.20/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.20/2.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.20/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.20/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.20/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.20/2.17  tff('#skF_4', type, '#skF_4': $i).
% 6.20/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.20/2.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.20/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.20/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.20/2.17  
% 6.20/2.19  tff(f_117, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 6.20/2.19  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.20/2.19  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 6.20/2.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.20/2.19  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.20/2.19  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.20/2.19  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 6.20/2.19  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.20/2.19  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 6.20/2.19  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 6.20/2.19  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 6.20/2.19  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.20/2.19  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.20/2.19  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.20/2.19  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.20/2.19  tff(c_122, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.20/2.19  tff(c_135, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_122])).
% 6.20/2.19  tff(c_40, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, A_20), k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.20/2.19  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.20/2.19  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.20/2.19  tff(c_26, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.20/2.19  tff(c_3225, plain, (![A_298, B_299, C_300, D_301]: (k7_relset_1(A_298, B_299, C_300, D_301)=k9_relat_1(C_300, D_301) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_298, B_299))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.20/2.19  tff(c_3236, plain, (![D_301]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_301)=k9_relat_1('#skF_4', D_301))), inference(resolution, [status(thm)], [c_62, c_3225])).
% 6.20/2.19  tff(c_3136, plain, (![B_287, A_288]: (k1_tarski(k1_funct_1(B_287, A_288))=k2_relat_1(B_287) | k1_tarski(A_288)!=k1_relat_1(B_287) | ~v1_funct_1(B_287) | ~v1_relat_1(B_287))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.20/2.19  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.20/2.19  tff(c_3145, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3136, c_58])).
% 6.20/2.19  tff(c_3151, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_66, c_3145])).
% 6.20/2.19  tff(c_3258, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3236, c_3151])).
% 6.20/2.19  tff(c_3259, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3258])).
% 6.20/2.19  tff(c_399, plain, (![C_86, A_87, B_88]: (v4_relat_1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.20/2.19  tff(c_414, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_399])).
% 6.20/2.19  tff(c_320, plain, (![B_81, A_82]: (r1_tarski(k1_relat_1(B_81), A_82) | ~v4_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.20/2.19  tff(c_16, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.20/2.19  tff(c_5270, plain, (![B_445, B_446]: (k1_tarski(B_445)=k1_relat_1(B_446) | k1_relat_1(B_446)=k1_xboole_0 | ~v4_relat_1(B_446, k1_tarski(B_445)) | ~v1_relat_1(B_446))), inference(resolution, [status(thm)], [c_320, c_16])).
% 6.20/2.19  tff(c_5328, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_414, c_5270])).
% 6.20/2.19  tff(c_5360, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_135, c_5328])).
% 6.20/2.19  tff(c_5361, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_3259, c_5360])).
% 6.20/2.19  tff(c_52, plain, (![B_35, A_34]: (m1_subset_1(B_35, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_35), A_34))) | ~r1_tarski(k2_relat_1(B_35), A_34) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.20/2.19  tff(c_5393, plain, (![A_34]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A_34))) | ~r1_tarski(k2_relat_1('#skF_4'), A_34) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5361, c_52])).
% 6.20/2.19  tff(c_5433, plain, (![A_34]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_4'), A_34))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_66, c_26, c_5393])).
% 6.20/2.19  tff(c_5504, plain, (![A_450]: (~r1_tarski(k2_relat_1('#skF_4'), A_450))), inference(splitLeft, [status(thm)], [c_5433])).
% 6.20/2.19  tff(c_5516, plain, $false, inference(resolution, [status(thm)], [c_6, c_5504])).
% 6.20/2.19  tff(c_5517, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_5433])).
% 6.20/2.19  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.20/2.19  tff(c_5565, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_5517, c_28])).
% 6.20/2.19  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.20/2.19  tff(c_136, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.20/2.19  tff(c_148, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_136])).
% 6.20/2.19  tff(c_5663, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5565, c_148])).
% 6.20/2.19  tff(c_5739, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5663, c_8])).
% 6.20/2.19  tff(c_30, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.20/2.19  tff(c_162, plain, (![C_53]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_122])).
% 6.20/2.19  tff(c_168, plain, (![A_54]: (v1_relat_1(A_54) | ~r1_tarski(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_162])).
% 6.20/2.19  tff(c_177, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_168])).
% 6.20/2.19  tff(c_24, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.20/2.19  tff(c_223, plain, (![C_64, B_65, A_66]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.20/2.19  tff(c_246, plain, (![A_71, B_72, A_73]: (v5_relat_1(A_71, B_72) | ~r1_tarski(A_71, k2_zfmisc_1(A_73, B_72)))), inference(resolution, [status(thm)], [c_30, c_223])).
% 6.20/2.19  tff(c_266, plain, (![A_73, B_72]: (v5_relat_1(k2_zfmisc_1(A_73, B_72), B_72))), inference(resolution, [status(thm)], [c_6, c_246])).
% 6.20/2.19  tff(c_291, plain, (![B_79, A_80]: (r1_tarski(k2_relat_1(B_79), A_80) | ~v5_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.20/2.19  tff(c_349, plain, (![B_83]: (k2_relat_1(B_83)=k1_xboole_0 | ~v5_relat_1(B_83, k1_xboole_0) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_291, c_148])).
% 6.20/2.19  tff(c_353, plain, (![A_73]: (k2_relat_1(k2_zfmisc_1(A_73, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_73, k1_xboole_0)))), inference(resolution, [status(thm)], [c_266, c_349])).
% 6.20/2.19  tff(c_364, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_177, c_24, c_24, c_353])).
% 6.20/2.19  tff(c_375, plain, (![A_20]: (r1_tarski(k9_relat_1(k1_xboole_0, A_20), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_364, c_40])).
% 6.20/2.19  tff(c_384, plain, (![A_84]: (r1_tarski(k9_relat_1(k1_xboole_0, A_84), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_375])).
% 6.20/2.19  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.20/2.19  tff(c_392, plain, (![A_84]: (k9_relat_1(k1_xboole_0, A_84)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1(k1_xboole_0, A_84)))), inference(resolution, [status(thm)], [c_384, c_2])).
% 6.20/2.19  tff(c_397, plain, (![A_84]: (k9_relat_1(k1_xboole_0, A_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_392])).
% 6.20/2.19  tff(c_5725, plain, (![A_84]: (k9_relat_1('#skF_4', A_84)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5663, c_5663, c_397])).
% 6.20/2.19  tff(c_3243, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3236, c_58])).
% 6.20/2.19  tff(c_6273, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5725, c_3243])).
% 6.20/2.19  tff(c_6277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5739, c_6273])).
% 6.20/2.19  tff(c_6278, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3258])).
% 6.20/2.19  tff(c_6361, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_6278])).
% 6.20/2.19  tff(c_6365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_6361])).
% 6.20/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.20/2.19  
% 6.20/2.19  Inference rules
% 6.20/2.19  ----------------------
% 6.20/2.19  #Ref     : 0
% 6.20/2.19  #Sup     : 1272
% 6.20/2.19  #Fact    : 0
% 6.20/2.19  #Define  : 0
% 6.20/2.19  #Split   : 6
% 6.20/2.19  #Chain   : 0
% 6.20/2.19  #Close   : 0
% 6.20/2.19  
% 6.20/2.19  Ordering : KBO
% 6.20/2.19  
% 6.20/2.19  Simplification rules
% 6.20/2.19  ----------------------
% 6.20/2.19  #Subsume      : 136
% 6.20/2.19  #Demod        : 2668
% 6.20/2.19  #Tautology    : 643
% 6.20/2.19  #SimpNegUnit  : 2
% 6.20/2.19  #BackRed      : 150
% 6.20/2.19  
% 6.20/2.19  #Partial instantiations: 0
% 6.20/2.19  #Strategies tried      : 1
% 6.20/2.19  
% 6.20/2.19  Timing (in seconds)
% 6.20/2.19  ----------------------
% 6.20/2.19  Preprocessing        : 0.33
% 6.20/2.19  Parsing              : 0.17
% 6.20/2.19  CNF conversion       : 0.02
% 6.20/2.19  Main loop            : 1.10
% 6.20/2.19  Inferencing          : 0.34
% 6.20/2.19  Reduction            : 0.44
% 6.20/2.19  Demodulation         : 0.32
% 6.20/2.19  BG Simplification    : 0.04
% 6.20/2.19  Subsumption          : 0.20
% 6.20/2.19  Abstraction          : 0.05
% 6.20/2.19  MUC search           : 0.00
% 6.20/2.19  Cooper               : 0.00
% 6.20/2.19  Total                : 1.46
% 6.20/2.19  Index Insertion      : 0.00
% 6.20/2.19  Index Deletion       : 0.00
% 6.20/2.19  Index Matching       : 0.00
% 6.20/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
