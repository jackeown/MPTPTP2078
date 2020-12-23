%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:35 EST 2020

% Result     : Theorem 5.65s
% Output     : CNFRefutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 286 expanded)
%              Number of leaves         :   37 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  166 ( 851 expanded)
%              Number of equality atoms :   54 ( 203 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_288,plain,(
    ! [C_94,B_95,A_96] :
      ( v1_xboole_0(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(B_95,A_96)))
      | ~ v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_309,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_288])).

tff(c_316,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_786,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( r2_relset_1(A_150,B_151,C_152,C_152)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_858,plain,(
    ! [C_163] :
      ( r2_relset_1('#skF_4','#skF_5',C_163,C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_66,c_786])).

tff(c_873,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_858])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_119,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_139,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_119])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_490,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_517,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_490])).

tff(c_586,plain,(
    ! [B_134,A_135,C_136] :
      ( k1_xboole_0 = B_134
      | k1_relset_1(A_135,B_134,C_136) = A_135
      | ~ v1_funct_2(C_136,A_135,B_134)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_596,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_586])).

tff(c_617,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_517,c_596])).

tff(c_643,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_138,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_119])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_516,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_490])).

tff(c_593,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_586])).

tff(c_614,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_516,c_593])).

tff(c_622,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_614])).

tff(c_877,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_3'(A_164,B_165),k1_relat_1(A_164))
      | B_165 = A_164
      | k1_relat_1(B_165) != k1_relat_1(A_164)
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_885,plain,(
    ! [B_165] :
      ( r2_hidden('#skF_3'('#skF_6',B_165),'#skF_4')
      | B_165 = '#skF_6'
      | k1_relat_1(B_165) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_877])).

tff(c_3047,plain,(
    ! [B_277] :
      ( r2_hidden('#skF_3'('#skF_6',B_277),'#skF_4')
      | B_277 = '#skF_6'
      | k1_relat_1(B_277) != '#skF_4'
      | ~ v1_funct_1(B_277)
      | ~ v1_relat_1(B_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_70,c_622,c_885])).

tff(c_58,plain,(
    ! [E_48] :
      ( k1_funct_1('#skF_7',E_48) = k1_funct_1('#skF_6',E_48)
      | ~ r2_hidden(E_48,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3144,plain,(
    ! [B_283] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_283)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_283))
      | B_283 = '#skF_6'
      | k1_relat_1(B_283) != '#skF_4'
      | ~ v1_funct_1(B_283)
      | ~ v1_relat_1(B_283) ) ),
    inference(resolution,[status(thm)],[c_3047,c_58])).

tff(c_28,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_3'(A_18,B_22)) != k1_funct_1(A_18,'#skF_3'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3154,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3144,c_28])).

tff(c_3168,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_64,c_643,c_138,c_70,c_622,c_643,c_3154])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3189,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3168,c_56])).

tff(c_3201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_873,c_3189])).

tff(c_3202,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3230,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3202,c_8])).

tff(c_3232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_3230])).

tff(c_3233,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_614])).

tff(c_3261,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3233,c_8])).

tff(c_3263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_3261])).

tff(c_3264,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_101,plain,(
    ! [B_54,A_55] :
      ( ~ v1_xboole_0(B_54)
      | B_54 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [A_55] :
      ( k1_xboole_0 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_3271,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3264,c_104])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3306,plain,(
    ! [A_12] : m1_subset_1('#skF_6',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_20])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1('#skF_2'(A_10),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3642,plain,(
    ! [A_320,B_321,C_322,D_323] :
      ( r2_relset_1(A_320,B_321,C_322,C_322)
      | ~ m1_subset_1(D_323,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321)))
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3891,plain,(
    ! [A_357,B_358,C_359] :
      ( r2_relset_1(A_357,B_358,C_359,C_359)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358))) ) ),
    inference(resolution,[status(thm)],[c_18,c_3642])).

tff(c_3906,plain,(
    ! [A_357,B_358] : r2_relset_1(A_357,B_358,'#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_3306,c_3891])).

tff(c_3265,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_3278,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3265,c_104])).

tff(c_3314,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3278])).

tff(c_310,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_288])).

tff(c_3331,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3264,c_3314,c_310])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | B_7 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3369,plain,(
    ! [A_293] :
      ( A_293 = '#skF_6'
      | ~ v1_xboole_0(A_293) ) ),
    inference(resolution,[status(thm)],[c_3264,c_10])).

tff(c_3376,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3331,c_3369])).

tff(c_3320,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3314,c_56])).

tff(c_3478,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3376,c_3320])).

tff(c_3910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3906,c_3478])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:59:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.65/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.29  
% 5.65/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.29  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_1
% 5.65/2.29  
% 5.65/2.29  %Foreground sorts:
% 5.65/2.29  
% 5.65/2.29  
% 5.65/2.29  %Background operators:
% 5.65/2.29  
% 5.65/2.29  
% 5.65/2.29  %Foreground operators:
% 5.65/2.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.65/2.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.65/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.65/2.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.65/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.65/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.65/2.29  tff('#skF_7', type, '#skF_7': $i).
% 5.65/2.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.65/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.65/2.29  tff('#skF_5', type, '#skF_5': $i).
% 5.65/2.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.65/2.29  tff('#skF_6', type, '#skF_6': $i).
% 5.65/2.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.65/2.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.65/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.65/2.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.65/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.65/2.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.65/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.65/2.29  tff('#skF_4', type, '#skF_4': $i).
% 5.65/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.65/2.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.65/2.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.65/2.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.65/2.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.65/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.65/2.29  
% 6.03/2.31  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 6.03/2.31  tff(f_99, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 6.03/2.31  tff(f_109, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.03/2.31  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.03/2.31  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.03/2.31  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.03/2.31  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 6.03/2.31  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.03/2.31  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.03/2.31  tff(f_52, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.03/2.31  tff(f_50, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.03/2.31  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.03/2.31  tff(c_288, plain, (![C_94, B_95, A_96]: (v1_xboole_0(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(B_95, A_96))) | ~v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.03/2.31  tff(c_309, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_288])).
% 6.03/2.31  tff(c_316, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_309])).
% 6.03/2.31  tff(c_786, plain, (![A_150, B_151, C_152, D_153]: (r2_relset_1(A_150, B_151, C_152, C_152) | ~m1_subset_1(D_153, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.03/2.31  tff(c_858, plain, (![C_163]: (r2_relset_1('#skF_4', '#skF_5', C_163, C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_66, c_786])).
% 6.03/2.31  tff(c_873, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_858])).
% 6.03/2.31  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.03/2.31  tff(c_119, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.03/2.31  tff(c_139, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_119])).
% 6.03/2.31  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.03/2.31  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.03/2.31  tff(c_490, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.03/2.31  tff(c_517, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_490])).
% 6.03/2.31  tff(c_586, plain, (![B_134, A_135, C_136]: (k1_xboole_0=B_134 | k1_relset_1(A_135, B_134, C_136)=A_135 | ~v1_funct_2(C_136, A_135, B_134) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.03/2.31  tff(c_596, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_586])).
% 6.03/2.31  tff(c_617, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_517, c_596])).
% 6.03/2.31  tff(c_643, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_617])).
% 6.03/2.31  tff(c_138, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_119])).
% 6.03/2.31  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.03/2.31  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.03/2.31  tff(c_516, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_490])).
% 6.03/2.31  tff(c_593, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_586])).
% 6.03/2.31  tff(c_614, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_516, c_593])).
% 6.03/2.31  tff(c_622, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_614])).
% 6.03/2.31  tff(c_877, plain, (![A_164, B_165]: (r2_hidden('#skF_3'(A_164, B_165), k1_relat_1(A_164)) | B_165=A_164 | k1_relat_1(B_165)!=k1_relat_1(A_164) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165) | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.03/2.31  tff(c_885, plain, (![B_165]: (r2_hidden('#skF_3'('#skF_6', B_165), '#skF_4') | B_165='#skF_6' | k1_relat_1(B_165)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_165) | ~v1_relat_1(B_165) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_622, c_877])).
% 6.03/2.31  tff(c_3047, plain, (![B_277]: (r2_hidden('#skF_3'('#skF_6', B_277), '#skF_4') | B_277='#skF_6' | k1_relat_1(B_277)!='#skF_4' | ~v1_funct_1(B_277) | ~v1_relat_1(B_277))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_70, c_622, c_885])).
% 6.03/2.31  tff(c_58, plain, (![E_48]: (k1_funct_1('#skF_7', E_48)=k1_funct_1('#skF_6', E_48) | ~r2_hidden(E_48, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.03/2.31  tff(c_3144, plain, (![B_283]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_283))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_283)) | B_283='#skF_6' | k1_relat_1(B_283)!='#skF_4' | ~v1_funct_1(B_283) | ~v1_relat_1(B_283))), inference(resolution, [status(thm)], [c_3047, c_58])).
% 6.03/2.31  tff(c_28, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_3'(A_18, B_22))!=k1_funct_1(A_18, '#skF_3'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.03/2.31  tff(c_3154, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3144, c_28])).
% 6.03/2.31  tff(c_3168, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_64, c_643, c_138, c_70, c_622, c_643, c_3154])).
% 6.03/2.31  tff(c_56, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.03/2.31  tff(c_3189, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3168, c_56])).
% 6.03/2.31  tff(c_3201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_873, c_3189])).
% 6.03/2.31  tff(c_3202, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_617])).
% 6.03/2.31  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.03/2.31  tff(c_3230, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3202, c_8])).
% 6.03/2.31  tff(c_3232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_3230])).
% 6.03/2.31  tff(c_3233, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_614])).
% 6.03/2.31  tff(c_3261, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3233, c_8])).
% 6.03/2.31  tff(c_3263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_3261])).
% 6.03/2.31  tff(c_3264, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_309])).
% 6.03/2.31  tff(c_101, plain, (![B_54, A_55]: (~v1_xboole_0(B_54) | B_54=A_55 | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.03/2.31  tff(c_104, plain, (![A_55]: (k1_xboole_0=A_55 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_8, c_101])).
% 6.03/2.31  tff(c_3271, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_3264, c_104])).
% 6.03/2.31  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.03/2.31  tff(c_3306, plain, (![A_12]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_3271, c_20])).
% 6.03/2.31  tff(c_18, plain, (![A_10]: (m1_subset_1('#skF_2'(A_10), A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.03/2.31  tff(c_3642, plain, (![A_320, B_321, C_322, D_323]: (r2_relset_1(A_320, B_321, C_322, C_322) | ~m1_subset_1(D_323, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.03/2.31  tff(c_3891, plain, (![A_357, B_358, C_359]: (r2_relset_1(A_357, B_358, C_359, C_359) | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(A_357, B_358))))), inference(resolution, [status(thm)], [c_18, c_3642])).
% 6.03/2.31  tff(c_3906, plain, (![A_357, B_358]: (r2_relset_1(A_357, B_358, '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_3306, c_3891])).
% 6.03/2.31  tff(c_3265, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_309])).
% 6.03/2.31  tff(c_3278, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3265, c_104])).
% 6.03/2.31  tff(c_3314, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3271, c_3278])).
% 6.03/2.31  tff(c_310, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_288])).
% 6.03/2.31  tff(c_3331, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3264, c_3314, c_310])).
% 6.03/2.31  tff(c_10, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | B_7=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.03/2.31  tff(c_3369, plain, (![A_293]: (A_293='#skF_6' | ~v1_xboole_0(A_293))), inference(resolution, [status(thm)], [c_3264, c_10])).
% 6.03/2.31  tff(c_3376, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_3331, c_3369])).
% 6.03/2.31  tff(c_3320, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3314, c_56])).
% 6.03/2.31  tff(c_3478, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3376, c_3320])).
% 6.03/2.31  tff(c_3910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3906, c_3478])).
% 6.03/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.03/2.31  
% 6.03/2.31  Inference rules
% 6.03/2.31  ----------------------
% 6.03/2.31  #Ref     : 2
% 6.03/2.31  #Sup     : 851
% 6.03/2.31  #Fact    : 4
% 6.03/2.31  #Define  : 0
% 6.03/2.31  #Split   : 10
% 6.03/2.31  #Chain   : 0
% 6.03/2.31  #Close   : 0
% 6.03/2.31  
% 6.03/2.31  Ordering : KBO
% 6.03/2.31  
% 6.03/2.31  Simplification rules
% 6.03/2.31  ----------------------
% 6.03/2.31  #Subsume      : 274
% 6.03/2.31  #Demod        : 689
% 6.03/2.31  #Tautology    : 338
% 6.03/2.31  #SimpNegUnit  : 37
% 6.03/2.31  #BackRed      : 115
% 6.03/2.31  
% 6.03/2.31  #Partial instantiations: 0
% 6.03/2.31  #Strategies tried      : 1
% 6.03/2.31  
% 6.03/2.31  Timing (in seconds)
% 6.03/2.31  ----------------------
% 6.03/2.31  Preprocessing        : 0.49
% 6.03/2.31  Parsing              : 0.22
% 6.03/2.31  CNF conversion       : 0.05
% 6.03/2.31  Main loop            : 1.00
% 6.03/2.31  Inferencing          : 0.33
% 6.03/2.31  Reduction            : 0.34
% 6.03/2.31  Demodulation         : 0.24
% 6.03/2.31  BG Simplification    : 0.05
% 6.03/2.31  Subsumption          : 0.20
% 6.03/2.31  Abstraction          : 0.04
% 6.03/2.31  MUC search           : 0.00
% 6.03/2.31  Cooper               : 0.00
% 6.03/2.31  Total                : 1.52
% 6.03/2.31  Index Insertion      : 0.00
% 6.03/2.31  Index Deletion       : 0.00
% 6.03/2.31  Index Matching       : 0.00
% 6.03/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
