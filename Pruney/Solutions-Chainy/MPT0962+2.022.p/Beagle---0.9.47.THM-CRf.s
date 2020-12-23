%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:54 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :  167 (1664 expanded)
%              Number of leaves         :   30 ( 532 expanded)
%              Depth                    :   16
%              Number of atoms          :  295 (4269 expanded)
%              Number of equality atoms :   75 ( 798 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3047,plain,(
    ! [C_404,A_405,B_406] :
      ( m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(A_405,B_406)))
      | ~ r1_tarski(k2_relat_1(C_404),B_406)
      | ~ r1_tarski(k1_relat_1(C_404),A_405)
      | ~ v1_relat_1(C_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_2'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [A_35,B_36] :
      ( ~ v1_xboole_0(A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_113,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_113])).

tff(c_126,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_130,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_126])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46])).

tff(c_89,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_278,plain,(
    ! [C_73,A_74,B_75] :
      ( m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ r1_tarski(k2_relat_1(C_73),B_75)
      | ~ r1_tarski(k1_relat_1(C_73),A_74)
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_561,plain,(
    ! [C_133,A_134,B_135] :
      ( r1_tarski(C_133,k2_zfmisc_1(A_134,B_135))
      | ~ r1_tarski(k2_relat_1(C_133),B_135)
      | ~ r1_tarski(k1_relat_1(C_133),A_134)
      | ~ v1_relat_1(C_133) ) ),
    inference(resolution,[status(thm)],[c_278,c_26])).

tff(c_566,plain,(
    ! [A_134] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_134,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_134)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_561])).

tff(c_575,plain,(
    ! [A_136] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_136,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_566])).

tff(c_585,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_575])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_185,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_196,plain,(
    ! [A_54,B_55,A_14] :
      ( k1_relset_1(A_54,B_55,A_14) = k1_relat_1(A_14)
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_54,B_55)) ) ),
    inference(resolution,[status(thm)],[c_28,c_185])).

tff(c_605,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_585,c_196])).

tff(c_502,plain,(
    ! [B_123,C_124,A_125] :
      ( k1_xboole_0 = B_123
      | v1_funct_2(C_124,A_125,B_123)
      | k1_relset_1(A_125,B_123,C_124) != A_125
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_680,plain,(
    ! [B_145,A_146,A_147] :
      ( k1_xboole_0 = B_145
      | v1_funct_2(A_146,A_147,B_145)
      | k1_relset_1(A_147,B_145,A_146) != A_147
      | ~ r1_tarski(A_146,k2_zfmisc_1(A_147,B_145)) ) ),
    inference(resolution,[status(thm)],[c_28,c_502])).

tff(c_686,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_585,c_680])).

tff(c_704,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_686])).

tff(c_705,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_704])).

tff(c_741,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_12])).

tff(c_743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_741])).

tff(c_744,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_902,plain,(
    ! [C_180,A_181,B_182] :
      ( m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ r1_tarski(k2_relat_1(C_180),B_182)
      | ~ r1_tarski(k1_relat_1(C_180),A_181)
      | ~ v1_relat_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2266,plain,(
    ! [C_332,A_333,B_334] :
      ( r1_tarski(C_332,k2_zfmisc_1(A_333,B_334))
      | ~ r1_tarski(k2_relat_1(C_332),B_334)
      | ~ r1_tarski(k1_relat_1(C_332),A_333)
      | ~ v1_relat_1(C_332) ) ),
    inference(resolution,[status(thm)],[c_902,c_26])).

tff(c_2389,plain,(
    ! [C_349,A_350] :
      ( r1_tarski(C_349,k2_zfmisc_1(A_350,k2_relat_1(C_349)))
      | ~ r1_tarski(k1_relat_1(C_349),A_350)
      | ~ v1_relat_1(C_349) ) ),
    inference(resolution,[status(thm)],[c_18,c_2266])).

tff(c_2416,plain,(
    ! [A_350] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_350,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_350)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_2389])).

tff(c_2442,plain,(
    ! [A_352] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_352,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2416])).

tff(c_2457,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_2442])).

tff(c_811,plain,(
    ! [A_161,B_162,C_163] :
      ( k1_relset_1(A_161,B_162,C_163) = k1_relat_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_822,plain,(
    ! [A_161,B_162,A_14] :
      ( k1_relset_1(A_161,B_162,A_14) = k1_relat_1(A_14)
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_161,B_162)) ) ),
    inference(resolution,[status(thm)],[c_28,c_811])).

tff(c_2478,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2457,c_822])).

tff(c_2180,plain,(
    ! [B_318,C_319,A_320] :
      ( k1_xboole_0 = B_318
      | v1_funct_2(C_319,A_320,B_318)
      | k1_relset_1(A_320,B_318,C_319) != A_320
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_320,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2483,plain,(
    ! [B_353,A_354,A_355] :
      ( k1_xboole_0 = B_353
      | v1_funct_2(A_354,A_355,B_353)
      | k1_relset_1(A_355,B_353,A_354) != A_355
      | ~ r1_tarski(A_354,k2_zfmisc_1(A_355,B_353)) ) ),
    inference(resolution,[status(thm)],[c_28,c_2180])).

tff(c_2486,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2457,c_2483])).

tff(c_2509,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_2486])).

tff(c_2534,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2478,c_2509])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2166,plain,(
    ! [C_316,A_317] :
      ( m1_subset_1(C_316,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_316),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_316),A_317)
      | ~ v1_relat_1(C_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_902])).

tff(c_2168,plain,(
    ! [A_317] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_317)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_2166])).

tff(c_2173,plain,(
    ! [A_317] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2168])).

tff(c_2175,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2173])).

tff(c_2549,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2534,c_2175])).

tff(c_2572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2549])).

tff(c_2574,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2173])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_780,plain,(
    ! [C_155,B_156,A_157] :
      ( r2_hidden(C_155,B_156)
      | ~ r2_hidden(C_155,A_157)
      | ~ r1_tarski(A_157,B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_787,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_1'(A_158),B_159)
      | ~ r1_tarski(A_158,B_159)
      | v1_xboole_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_4,c_780])).

tff(c_794,plain,(
    ! [B_159,A_158] :
      ( ~ v1_xboole_0(B_159)
      | ~ r1_tarski(A_158,B_159)
      | v1_xboole_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_787,c_2])).

tff(c_2585,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2574,c_794])).

tff(c_2599,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2585])).

tff(c_120,plain,(
    ! [B_36,A_35] :
      ( B_36 = A_35
      | ~ r1_tarski(B_36,A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_100,c_113])).

tff(c_2588,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2574,c_120])).

tff(c_2602,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2588])).

tff(c_2573,plain,(
    ! [A_317] :
      ( ~ r1_tarski(k1_relat_1('#skF_4'),A_317)
      | m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_2173])).

tff(c_2737,plain,(
    ! [A_317] :
      ( ~ r1_tarski(k1_relat_1('#skF_4'),A_317)
      | m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2602,c_2573])).

tff(c_2745,plain,(
    ! [A_363] : ~ r1_tarski(k1_relat_1('#skF_4'),A_363) ),
    inference(splitLeft,[status(thm)],[c_2737])).

tff(c_2755,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_2745])).

tff(c_2756,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2737])).

tff(c_2782,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_2756,c_26])).

tff(c_2792,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2782,c_120])).

tff(c_2804,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2599,c_2792])).

tff(c_1161,plain,(
    ! [C_239,A_240,B_241] :
      ( r1_tarski(C_239,k2_zfmisc_1(A_240,B_241))
      | ~ r1_tarski(k2_relat_1(C_239),B_241)
      | ~ r1_tarski(k1_relat_1(C_239),A_240)
      | ~ v1_relat_1(C_239) ) ),
    inference(resolution,[status(thm)],[c_902,c_26])).

tff(c_1174,plain,(
    ! [C_242,A_243] :
      ( r1_tarski(C_242,k2_zfmisc_1(A_243,k2_relat_1(C_242)))
      | ~ r1_tarski(k1_relat_1(C_242),A_243)
      | ~ v1_relat_1(C_242) ) ),
    inference(resolution,[status(thm)],[c_18,c_1161])).

tff(c_1197,plain,(
    ! [A_243] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_243,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_243)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_1174])).

tff(c_1217,plain,(
    ! [A_245] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_245,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1197])).

tff(c_1232,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_1217])).

tff(c_1265,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1232,c_822])).

tff(c_982,plain,(
    ! [B_201,C_202,A_203] :
      ( k1_xboole_0 = B_201
      | v1_funct_2(C_202,A_203,B_201)
      | k1_relset_1(A_203,B_201,C_202) != A_203
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_203,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1511,plain,(
    ! [B_269,A_270,A_271] :
      ( k1_xboole_0 = B_269
      | v1_funct_2(A_270,A_271,B_269)
      | k1_relset_1(A_271,B_269,A_270) != A_271
      | ~ r1_tarski(A_270,k2_zfmisc_1(A_271,B_269)) ) ),
    inference(resolution,[status(thm)],[c_28,c_982])).

tff(c_1517,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1232,c_1511])).

tff(c_1538,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1265,c_1517])).

tff(c_1539,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_1538])).

tff(c_1100,plain,(
    ! [C_225,A_226] :
      ( m1_subset_1(C_225,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_225),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_225),A_226)
      | ~ v1_relat_1(C_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_902])).

tff(c_1102,plain,(
    ! [A_226] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_226)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_1100])).

tff(c_1107,plain,(
    ! [A_226] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1102])).

tff(c_1109,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1107])).

tff(c_1554,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1539,c_1109])).

tff(c_1583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1554])).

tff(c_1585,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1107])).

tff(c_1596,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1585,c_794])).

tff(c_1610,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1596])).

tff(c_1599,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1585,c_120])).

tff(c_1613,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1599])).

tff(c_1584,plain,(
    ! [A_226] :
      ( ~ r1_tarski(k1_relat_1('#skF_4'),A_226)
      | m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_1107])).

tff(c_1685,plain,(
    ! [A_273] : ~ r1_tarski(k1_relat_1('#skF_4'),A_273) ),
    inference(splitLeft,[status(thm)],[c_1584])).

tff(c_1695,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_1685])).

tff(c_1696,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1584])).

tff(c_1780,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_1696])).

tff(c_1784,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1780,c_26])).

tff(c_1794,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1784,c_120])).

tff(c_1806,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1610,c_1794])).

tff(c_34,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_22,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_57,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_34])).

tff(c_795,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_798,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_795])).

tff(c_802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_798])).

tff(c_804,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_869,plain,(
    ! [B_175,C_176] :
      ( k1_relset_1(k1_xboole_0,B_175,C_176) = k1_relat_1(C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_811])).

tff(c_875,plain,(
    ! [B_175] : k1_relset_1(k1_xboole_0,B_175,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_804,c_869])).

tff(c_38,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_963,plain,(
    ! [C_197,B_198] :
      ( v1_funct_2(C_197,k1_xboole_0,B_198)
      | k1_relset_1(k1_xboole_0,B_198,C_197) != k1_xboole_0
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_38])).

tff(c_965,plain,(
    ! [B_198] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_198)
      | k1_relset_1(k1_xboole_0,B_198,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_804,c_963])).

tff(c_970,plain,(
    ! [B_198] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_198)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_965])).

tff(c_981,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_970])).

tff(c_1722,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_1613,c_981])).

tff(c_1818,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1806,c_1722])).

tff(c_803,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22 ) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_1730,plain,(
    ! [A_22] :
      ( v1_funct_2('#skF_3',A_22,'#skF_3')
      | A_22 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1613,c_1613,c_1613,c_803])).

tff(c_2072,plain,(
    ! [A_300] :
      ( v1_funct_2('#skF_4',A_300,'#skF_4')
      | A_300 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1806,c_1806,c_1730])).

tff(c_1823,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_89])).

tff(c_2075,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2072,c_1823])).

tff(c_2079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1818,c_2075])).

tff(c_2080,plain,(
    ! [B_198] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_198) ),
    inference(splitRight,[status(thm)],[c_970])).

tff(c_2620,plain,(
    ! [B_198] : v1_funct_2('#skF_3','#skF_3',B_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2602,c_2602,c_2080])).

tff(c_2818,plain,(
    ! [B_198] : v1_funct_2('#skF_4','#skF_4',B_198) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2804,c_2804,c_2620])).

tff(c_2081,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_970])).

tff(c_2621,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2602,c_2602,c_2081])).

tff(c_2822,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2804,c_2804,c_2621])).

tff(c_2828,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2804,c_89])).

tff(c_2895,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2822,c_2828])).

tff(c_2900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2818,c_2895])).

tff(c_2901,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3053,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3047,c_2901])).

tff(c_3067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18,c_48,c_3053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n025.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:23:35 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.88  
% 4.81/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.88  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.81/1.88  
% 4.81/1.88  %Foreground sorts:
% 4.81/1.88  
% 4.81/1.88  
% 4.81/1.88  %Background operators:
% 4.81/1.88  
% 4.81/1.88  
% 4.81/1.88  %Foreground operators:
% 4.81/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.81/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/1.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.81/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.81/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.81/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.81/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.81/1.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.81/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.81/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.81/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.81/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.81/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.81/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.81/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.81/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.81/1.88  
% 4.88/1.91  tff(f_98, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.88/1.91  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.88/1.91  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.88/1.91  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.88/1.91  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.88/1.91  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.88/1.91  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.88/1.91  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.88/1.91  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.88/1.91  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.88/1.91  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.88/1.91  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.88/1.91  tff(c_48, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.88/1.91  tff(c_3047, plain, (![C_404, A_405, B_406]: (m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(A_405, B_406))) | ~r1_tarski(k2_relat_1(C_404), B_406) | ~r1_tarski(k1_relat_1(C_404), A_405) | ~v1_relat_1(C_404))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.88/1.91  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.88/1.91  tff(c_96, plain, (![A_35, B_36]: (r2_hidden('#skF_2'(A_35, B_36), A_35) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.88/1.91  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/1.91  tff(c_100, plain, (![A_35, B_36]: (~v1_xboole_0(A_35) | r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_96, c_2])).
% 4.88/1.91  tff(c_113, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.88/1.91  tff(c_121, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_113])).
% 4.88/1.91  tff(c_126, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_121])).
% 4.88/1.91  tff(c_130, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_100, c_126])).
% 4.88/1.91  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.88/1.91  tff(c_46, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.88/1.91  tff(c_54, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46])).
% 4.88/1.91  tff(c_89, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 4.88/1.91  tff(c_278, plain, (![C_73, A_74, B_75]: (m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~r1_tarski(k2_relat_1(C_73), B_75) | ~r1_tarski(k1_relat_1(C_73), A_74) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.88/1.91  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.88/1.91  tff(c_561, plain, (![C_133, A_134, B_135]: (r1_tarski(C_133, k2_zfmisc_1(A_134, B_135)) | ~r1_tarski(k2_relat_1(C_133), B_135) | ~r1_tarski(k1_relat_1(C_133), A_134) | ~v1_relat_1(C_133))), inference(resolution, [status(thm)], [c_278, c_26])).
% 4.88/1.91  tff(c_566, plain, (![A_134]: (r1_tarski('#skF_4', k2_zfmisc_1(A_134, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_134) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_561])).
% 4.88/1.91  tff(c_575, plain, (![A_136]: (r1_tarski('#skF_4', k2_zfmisc_1(A_136, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_136))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_566])).
% 4.88/1.91  tff(c_585, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_575])).
% 4.88/1.91  tff(c_28, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.88/1.91  tff(c_185, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.88/1.91  tff(c_196, plain, (![A_54, B_55, A_14]: (k1_relset_1(A_54, B_55, A_14)=k1_relat_1(A_14) | ~r1_tarski(A_14, k2_zfmisc_1(A_54, B_55)))), inference(resolution, [status(thm)], [c_28, c_185])).
% 4.88/1.91  tff(c_605, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_585, c_196])).
% 4.88/1.91  tff(c_502, plain, (![B_123, C_124, A_125]: (k1_xboole_0=B_123 | v1_funct_2(C_124, A_125, B_123) | k1_relset_1(A_125, B_123, C_124)!=A_125 | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_123))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.88/1.91  tff(c_680, plain, (![B_145, A_146, A_147]: (k1_xboole_0=B_145 | v1_funct_2(A_146, A_147, B_145) | k1_relset_1(A_147, B_145, A_146)!=A_147 | ~r1_tarski(A_146, k2_zfmisc_1(A_147, B_145)))), inference(resolution, [status(thm)], [c_28, c_502])).
% 4.88/1.91  tff(c_686, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_585, c_680])).
% 4.88/1.91  tff(c_704, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_686])).
% 4.88/1.91  tff(c_705, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_89, c_704])).
% 4.88/1.91  tff(c_741, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_705, c_12])).
% 4.88/1.91  tff(c_743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_741])).
% 4.88/1.91  tff(c_744, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_121])).
% 4.88/1.91  tff(c_902, plain, (![C_180, A_181, B_182]: (m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~r1_tarski(k2_relat_1(C_180), B_182) | ~r1_tarski(k1_relat_1(C_180), A_181) | ~v1_relat_1(C_180))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.88/1.91  tff(c_2266, plain, (![C_332, A_333, B_334]: (r1_tarski(C_332, k2_zfmisc_1(A_333, B_334)) | ~r1_tarski(k2_relat_1(C_332), B_334) | ~r1_tarski(k1_relat_1(C_332), A_333) | ~v1_relat_1(C_332))), inference(resolution, [status(thm)], [c_902, c_26])).
% 4.88/1.91  tff(c_2389, plain, (![C_349, A_350]: (r1_tarski(C_349, k2_zfmisc_1(A_350, k2_relat_1(C_349))) | ~r1_tarski(k1_relat_1(C_349), A_350) | ~v1_relat_1(C_349))), inference(resolution, [status(thm)], [c_18, c_2266])).
% 4.88/1.91  tff(c_2416, plain, (![A_350]: (r1_tarski('#skF_4', k2_zfmisc_1(A_350, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_350) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_744, c_2389])).
% 4.88/1.91  tff(c_2442, plain, (![A_352]: (r1_tarski('#skF_4', k2_zfmisc_1(A_352, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_352))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2416])).
% 4.88/1.91  tff(c_2457, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_2442])).
% 4.88/1.91  tff(c_811, plain, (![A_161, B_162, C_163]: (k1_relset_1(A_161, B_162, C_163)=k1_relat_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.88/1.91  tff(c_822, plain, (![A_161, B_162, A_14]: (k1_relset_1(A_161, B_162, A_14)=k1_relat_1(A_14) | ~r1_tarski(A_14, k2_zfmisc_1(A_161, B_162)))), inference(resolution, [status(thm)], [c_28, c_811])).
% 4.88/1.91  tff(c_2478, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2457, c_822])).
% 4.88/1.91  tff(c_2180, plain, (![B_318, C_319, A_320]: (k1_xboole_0=B_318 | v1_funct_2(C_319, A_320, B_318) | k1_relset_1(A_320, B_318, C_319)!=A_320 | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_320, B_318))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.88/1.91  tff(c_2483, plain, (![B_353, A_354, A_355]: (k1_xboole_0=B_353 | v1_funct_2(A_354, A_355, B_353) | k1_relset_1(A_355, B_353, A_354)!=A_355 | ~r1_tarski(A_354, k2_zfmisc_1(A_355, B_353)))), inference(resolution, [status(thm)], [c_28, c_2180])).
% 4.88/1.91  tff(c_2486, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2457, c_2483])).
% 4.88/1.91  tff(c_2509, plain, (k1_xboole_0='#skF_3' | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_89, c_2486])).
% 4.88/1.91  tff(c_2534, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2478, c_2509])).
% 4.88/1.91  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.88/1.91  tff(c_2166, plain, (![C_316, A_317]: (m1_subset_1(C_316, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_316), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_316), A_317) | ~v1_relat_1(C_316))), inference(superposition, [status(thm), theory('equality')], [c_22, c_902])).
% 4.88/1.91  tff(c_2168, plain, (![A_317]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_317) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_744, c_2166])).
% 4.88/1.91  tff(c_2173, plain, (![A_317]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_317))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2168])).
% 4.88/1.91  tff(c_2175, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2173])).
% 4.88/1.91  tff(c_2549, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2534, c_2175])).
% 4.88/1.91  tff(c_2572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_2549])).
% 4.88/1.91  tff(c_2574, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2173])).
% 4.88/1.91  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.88/1.91  tff(c_780, plain, (![C_155, B_156, A_157]: (r2_hidden(C_155, B_156) | ~r2_hidden(C_155, A_157) | ~r1_tarski(A_157, B_156))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.88/1.91  tff(c_787, plain, (![A_158, B_159]: (r2_hidden('#skF_1'(A_158), B_159) | ~r1_tarski(A_158, B_159) | v1_xboole_0(A_158))), inference(resolution, [status(thm)], [c_4, c_780])).
% 4.88/1.91  tff(c_794, plain, (![B_159, A_158]: (~v1_xboole_0(B_159) | ~r1_tarski(A_158, B_159) | v1_xboole_0(A_158))), inference(resolution, [status(thm)], [c_787, c_2])).
% 4.88/1.91  tff(c_2585, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_2574, c_794])).
% 4.88/1.91  tff(c_2599, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2585])).
% 4.88/1.91  tff(c_120, plain, (![B_36, A_35]: (B_36=A_35 | ~r1_tarski(B_36, A_35) | ~v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_100, c_113])).
% 4.88/1.91  tff(c_2588, plain, (k1_xboole_0='#skF_3' | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2574, c_120])).
% 4.88/1.91  tff(c_2602, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2588])).
% 4.88/1.91  tff(c_2573, plain, (![A_317]: (~r1_tarski(k1_relat_1('#skF_4'), A_317) | m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_2173])).
% 4.88/1.91  tff(c_2737, plain, (![A_317]: (~r1_tarski(k1_relat_1('#skF_4'), A_317) | m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2602, c_2573])).
% 4.88/1.91  tff(c_2745, plain, (![A_363]: (~r1_tarski(k1_relat_1('#skF_4'), A_363))), inference(splitLeft, [status(thm)], [c_2737])).
% 4.88/1.91  tff(c_2755, plain, $false, inference(resolution, [status(thm)], [c_18, c_2745])).
% 4.88/1.91  tff(c_2756, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2737])).
% 4.88/1.91  tff(c_2782, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_2756, c_26])).
% 4.88/1.91  tff(c_2792, plain, ('#skF_3'='#skF_4' | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_2782, c_120])).
% 4.88/1.91  tff(c_2804, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2599, c_2792])).
% 4.88/1.91  tff(c_1161, plain, (![C_239, A_240, B_241]: (r1_tarski(C_239, k2_zfmisc_1(A_240, B_241)) | ~r1_tarski(k2_relat_1(C_239), B_241) | ~r1_tarski(k1_relat_1(C_239), A_240) | ~v1_relat_1(C_239))), inference(resolution, [status(thm)], [c_902, c_26])).
% 4.88/1.91  tff(c_1174, plain, (![C_242, A_243]: (r1_tarski(C_242, k2_zfmisc_1(A_243, k2_relat_1(C_242))) | ~r1_tarski(k1_relat_1(C_242), A_243) | ~v1_relat_1(C_242))), inference(resolution, [status(thm)], [c_18, c_1161])).
% 4.88/1.91  tff(c_1197, plain, (![A_243]: (r1_tarski('#skF_4', k2_zfmisc_1(A_243, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_243) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_744, c_1174])).
% 4.88/1.91  tff(c_1217, plain, (![A_245]: (r1_tarski('#skF_4', k2_zfmisc_1(A_245, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_245))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1197])).
% 4.88/1.91  tff(c_1232, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_1217])).
% 4.88/1.91  tff(c_1265, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1232, c_822])).
% 4.88/1.91  tff(c_982, plain, (![B_201, C_202, A_203]: (k1_xboole_0=B_201 | v1_funct_2(C_202, A_203, B_201) | k1_relset_1(A_203, B_201, C_202)!=A_203 | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_203, B_201))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.88/1.91  tff(c_1511, plain, (![B_269, A_270, A_271]: (k1_xboole_0=B_269 | v1_funct_2(A_270, A_271, B_269) | k1_relset_1(A_271, B_269, A_270)!=A_271 | ~r1_tarski(A_270, k2_zfmisc_1(A_271, B_269)))), inference(resolution, [status(thm)], [c_28, c_982])).
% 4.88/1.91  tff(c_1517, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1232, c_1511])).
% 4.88/1.91  tff(c_1538, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1265, c_1517])).
% 4.88/1.91  tff(c_1539, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_89, c_1538])).
% 4.88/1.91  tff(c_1100, plain, (![C_225, A_226]: (m1_subset_1(C_225, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_225), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_225), A_226) | ~v1_relat_1(C_225))), inference(superposition, [status(thm), theory('equality')], [c_22, c_902])).
% 4.88/1.91  tff(c_1102, plain, (![A_226]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_226) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_744, c_1100])).
% 4.88/1.91  tff(c_1107, plain, (![A_226]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_226))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1102])).
% 4.88/1.91  tff(c_1109, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1107])).
% 4.88/1.91  tff(c_1554, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1539, c_1109])).
% 4.88/1.91  tff(c_1583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_1554])).
% 4.88/1.91  tff(c_1585, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1107])).
% 4.88/1.91  tff(c_1596, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1585, c_794])).
% 4.88/1.91  tff(c_1610, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1596])).
% 4.88/1.91  tff(c_1599, plain, (k1_xboole_0='#skF_3' | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_1585, c_120])).
% 4.88/1.91  tff(c_1613, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1599])).
% 4.88/1.91  tff(c_1584, plain, (![A_226]: (~r1_tarski(k1_relat_1('#skF_4'), A_226) | m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1107])).
% 4.88/1.91  tff(c_1685, plain, (![A_273]: (~r1_tarski(k1_relat_1('#skF_4'), A_273))), inference(splitLeft, [status(thm)], [c_1584])).
% 4.88/1.91  tff(c_1695, plain, $false, inference(resolution, [status(thm)], [c_18, c_1685])).
% 4.88/1.91  tff(c_1696, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1584])).
% 4.88/1.91  tff(c_1780, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_1696])).
% 4.88/1.91  tff(c_1784, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1780, c_26])).
% 4.88/1.91  tff(c_1794, plain, ('#skF_3'='#skF_4' | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1784, c_120])).
% 4.88/1.91  tff(c_1806, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1610, c_1794])).
% 4.88/1.91  tff(c_34, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_22, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.88/1.91  tff(c_57, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_34])).
% 4.88/1.91  tff(c_795, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_57])).
% 4.88/1.91  tff(c_798, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_795])).
% 4.88/1.91  tff(c_802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_798])).
% 4.88/1.91  tff(c_804, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_57])).
% 4.88/1.91  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.88/1.91  tff(c_869, plain, (![B_175, C_176]: (k1_relset_1(k1_xboole_0, B_175, C_176)=k1_relat_1(C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_811])).
% 4.88/1.91  tff(c_875, plain, (![B_175]: (k1_relset_1(k1_xboole_0, B_175, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_804, c_869])).
% 4.88/1.91  tff(c_38, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.88/1.91  tff(c_963, plain, (![C_197, B_198]: (v1_funct_2(C_197, k1_xboole_0, B_198) | k1_relset_1(k1_xboole_0, B_198, C_197)!=k1_xboole_0 | ~m1_subset_1(C_197, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_38])).
% 4.88/1.91  tff(c_965, plain, (![B_198]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_198) | k1_relset_1(k1_xboole_0, B_198, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_804, c_963])).
% 4.88/1.91  tff(c_970, plain, (![B_198]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_198) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_875, c_965])).
% 4.88/1.91  tff(c_981, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_970])).
% 4.88/1.91  tff(c_1722, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_1613, c_981])).
% 4.88/1.91  tff(c_1818, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1806, c_1722])).
% 4.88/1.91  tff(c_803, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22)), inference(splitRight, [status(thm)], [c_57])).
% 4.88/1.91  tff(c_1730, plain, (![A_22]: (v1_funct_2('#skF_3', A_22, '#skF_3') | A_22='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1613, c_1613, c_1613, c_803])).
% 4.88/1.91  tff(c_2072, plain, (![A_300]: (v1_funct_2('#skF_4', A_300, '#skF_4') | A_300='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1806, c_1806, c_1730])).
% 4.88/1.91  tff(c_1823, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1806, c_89])).
% 4.88/1.91  tff(c_2075, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_2072, c_1823])).
% 4.88/1.91  tff(c_2079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1818, c_2075])).
% 4.88/1.91  tff(c_2080, plain, (![B_198]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_198))), inference(splitRight, [status(thm)], [c_970])).
% 4.88/1.91  tff(c_2620, plain, (![B_198]: (v1_funct_2('#skF_3', '#skF_3', B_198))), inference(demodulation, [status(thm), theory('equality')], [c_2602, c_2602, c_2080])).
% 4.88/1.91  tff(c_2818, plain, (![B_198]: (v1_funct_2('#skF_4', '#skF_4', B_198))), inference(demodulation, [status(thm), theory('equality')], [c_2804, c_2804, c_2620])).
% 4.88/1.91  tff(c_2081, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_970])).
% 4.88/1.91  tff(c_2621, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2602, c_2602, c_2081])).
% 4.88/1.91  tff(c_2822, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2804, c_2804, c_2621])).
% 4.88/1.91  tff(c_2828, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2804, c_89])).
% 4.88/1.91  tff(c_2895, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2822, c_2828])).
% 4.88/1.91  tff(c_2900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2818, c_2895])).
% 4.88/1.91  tff(c_2901, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(splitRight, [status(thm)], [c_54])).
% 4.88/1.91  tff(c_3053, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3047, c_2901])).
% 4.88/1.91  tff(c_3067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_18, c_48, c_3053])).
% 4.88/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.91  
% 4.88/1.91  Inference rules
% 4.88/1.91  ----------------------
% 4.88/1.91  #Ref     : 0
% 4.88/1.91  #Sup     : 631
% 4.88/1.91  #Fact    : 0
% 4.88/1.91  #Define  : 0
% 4.88/1.91  #Split   : 26
% 4.88/1.91  #Chain   : 0
% 4.88/1.91  #Close   : 0
% 4.88/1.91  
% 4.88/1.91  Ordering : KBO
% 4.88/1.91  
% 4.88/1.91  Simplification rules
% 4.88/1.91  ----------------------
% 4.88/1.91  #Subsume      : 101
% 4.88/1.91  #Demod        : 614
% 4.88/1.91  #Tautology    : 225
% 4.88/1.91  #SimpNegUnit  : 9
% 4.88/1.91  #BackRed      : 203
% 4.88/1.91  
% 4.88/1.91  #Partial instantiations: 0
% 4.88/1.91  #Strategies tried      : 1
% 4.88/1.91  
% 4.88/1.91  Timing (in seconds)
% 4.88/1.91  ----------------------
% 4.88/1.91  Preprocessing        : 0.31
% 4.88/1.91  Parsing              : 0.16
% 4.88/1.91  CNF conversion       : 0.02
% 4.88/1.91  Main loop            : 0.77
% 4.88/1.91  Inferencing          : 0.27
% 4.88/1.91  Reduction            : 0.23
% 4.88/1.91  Demodulation         : 0.15
% 4.88/1.91  BG Simplification    : 0.03
% 4.88/1.91  Subsumption          : 0.17
% 4.88/1.91  Abstraction          : 0.04
% 4.88/1.91  MUC search           : 0.00
% 4.88/1.91  Cooper               : 0.00
% 4.88/1.91  Total                : 1.13
% 4.88/1.91  Index Insertion      : 0.00
% 4.88/1.91  Index Deletion       : 0.00
% 4.88/1.91  Index Matching       : 0.00
% 4.88/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
