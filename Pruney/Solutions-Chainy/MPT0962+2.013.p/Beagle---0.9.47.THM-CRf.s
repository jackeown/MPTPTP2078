%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:53 EST 2020

% Result     : Theorem 14.24s
% Output     : CNFRefutation 14.53s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 567 expanded)
%              Number of leaves         :   34 ( 200 expanded)
%              Depth                    :   14
%              Number of atoms          :  295 (1315 expanded)
%              Number of equality atoms :   66 ( 189 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_128,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_59826,plain,(
    ! [C_1892,A_1893,B_1894] :
      ( m1_subset_1(C_1892,k1_zfmisc_1(k2_zfmisc_1(A_1893,B_1894)))
      | ~ r1_tarski(k2_relat_1(C_1892),B_1894)
      | ~ r1_tarski(k1_relat_1(C_1892),A_1893)
      | ~ v1_relat_1(C_1892) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_66,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58])).

tff(c_77,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_129,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_64,B_65] :
      ( ~ v1_xboole_0(A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_140,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_140])).

tff(c_173,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_177,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_173])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7365,plain,(
    ! [C_398,A_399,B_400] :
      ( m1_subset_1(C_398,k1_zfmisc_1(k2_zfmisc_1(A_399,B_400)))
      | ~ r1_tarski(k2_relat_1(C_398),B_400)
      | ~ r1_tarski(k1_relat_1(C_398),A_399)
      | ~ v1_relat_1(C_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_19203,plain,(
    ! [C_631,A_632,B_633] :
      ( r1_tarski(C_631,k2_zfmisc_1(A_632,B_633))
      | ~ r1_tarski(k2_relat_1(C_631),B_633)
      | ~ r1_tarski(k1_relat_1(C_631),A_632)
      | ~ v1_relat_1(C_631) ) ),
    inference(resolution,[status(thm)],[c_7365,c_22])).

tff(c_19264,plain,(
    ! [A_632] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_632,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_632)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_19203])).

tff(c_19408,plain,(
    ! [A_640] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_640,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_640) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_19264])).

tff(c_19439,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_19408])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5745,plain,(
    ! [A_329,B_330,C_331] :
      ( k1_relset_1(A_329,B_330,C_331) = k1_relat_1(C_331)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5750,plain,(
    ! [A_329,B_330,A_15] :
      ( k1_relset_1(A_329,B_330,A_15) = k1_relat_1(A_15)
      | ~ r1_tarski(A_15,k2_zfmisc_1(A_329,B_330)) ) ),
    inference(resolution,[status(thm)],[c_24,c_5745])).

tff(c_19469,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_19439,c_5750])).

tff(c_7612,plain,(
    ! [B_407,C_408,A_409] :
      ( k1_xboole_0 = B_407
      | v1_funct_2(C_408,A_409,B_407)
      | k1_relset_1(A_409,B_407,C_408) != A_409
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_409,B_407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_21322,plain,(
    ! [B_678,A_679,A_680] :
      ( k1_xboole_0 = B_678
      | v1_funct_2(A_679,A_680,B_678)
      | k1_relset_1(A_680,B_678,A_679) != A_680
      | ~ r1_tarski(A_679,k2_zfmisc_1(A_680,B_678)) ) ),
    inference(resolution,[status(thm)],[c_24,c_7612])).

tff(c_21331,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_19439,c_21322])).

tff(c_21431,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19469,c_21331])).

tff(c_21432,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_21431])).

tff(c_32,plain,(
    ! [A_24,B_25] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_24,B_25)),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5400,plain,(
    ! [C_295,B_296,A_297] :
      ( r2_hidden(C_295,B_296)
      | ~ r2_hidden(C_295,A_297)
      | ~ r1_tarski(A_297,B_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5654,plain,(
    ! [A_319,B_320] :
      ( r2_hidden('#skF_1'(A_319),B_320)
      | ~ r1_tarski(A_319,B_320)
      | v1_xboole_0(A_319) ) ),
    inference(resolution,[status(thm)],[c_4,c_5400])).

tff(c_5662,plain,(
    ! [B_321,A_322] :
      ( ~ v1_xboole_0(B_321)
      | ~ r1_tarski(A_322,B_321)
      | v1_xboole_0(A_322) ) ),
    inference(resolution,[status(thm)],[c_5654,c_2])).

tff(c_5703,plain,(
    ! [B_323,A_324] :
      ( ~ v1_xboole_0(B_323)
      | v1_xboole_0(k2_relat_1(k2_zfmisc_1(A_324,B_323))) ) ),
    inference(resolution,[status(thm)],[c_32,c_5662])).

tff(c_156,plain,(
    ! [A_68,B_69] :
      ( ~ v1_xboole_0(A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5329,plain,(
    ! [B_287,A_288] :
      ( B_287 = A_288
      | ~ r1_tarski(B_287,A_288)
      | ~ v1_xboole_0(A_288) ) ),
    inference(resolution,[status(thm)],[c_156,c_14])).

tff(c_5351,plain,(
    ! [B_289,A_290] :
      ( B_289 = A_290
      | ~ v1_xboole_0(B_289)
      | ~ v1_xboole_0(A_290) ) ),
    inference(resolution,[status(thm)],[c_139,c_5329])).

tff(c_5354,plain,(
    ! [A_290] :
      ( k1_xboole_0 = A_290
      | ~ v1_xboole_0(A_290) ) ),
    inference(resolution,[status(thm)],[c_12,c_5351])).

tff(c_5715,plain,(
    ! [A_324,B_323] :
      ( k2_relat_1(k2_zfmisc_1(A_324,B_323)) = k1_xboole_0
      | ~ v1_xboole_0(B_323) ) ),
    inference(resolution,[status(thm)],[c_5703,c_5354])).

tff(c_28,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_85,plain,(
    ! [A_53] :
      ( k1_relat_1(A_53) = k1_xboole_0
      | k2_relat_1(A_53) != k1_xboole_0
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7771,plain,(
    ! [A_413,B_414] :
      ( k1_relat_1(k2_zfmisc_1(A_413,B_414)) = k1_xboole_0
      | k2_relat_1(k2_zfmisc_1(A_413,B_414)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_7785,plain,(
    ! [A_324,B_323] :
      ( k1_relat_1(k2_zfmisc_1(A_324,B_323)) = k1_xboole_0
      | ~ v1_xboole_0(B_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5715,c_7771])).

tff(c_30,plain,(
    ! [A_22,B_23] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_22,B_23)),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5421,plain,(
    ! [A_300,C_301,B_302] :
      ( r1_tarski(A_300,C_301)
      | ~ r1_tarski(B_302,C_301)
      | ~ r1_tarski(A_300,B_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5437,plain,(
    ! [A_303] :
      ( r1_tarski(A_303,'#skF_3')
      | ~ r1_tarski(A_303,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_60,c_5421])).

tff(c_5479,plain,(
    ! [B_305] : r1_tarski(k1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_4'),B_305)),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_5437])).

tff(c_8315,plain,(
    ! [B_433] :
      ( k1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_4'),B_433)) = '#skF_3'
      | ~ r1_tarski('#skF_3',k1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_4'),B_433))) ) ),
    inference(resolution,[status(thm)],[c_5479,c_14])).

tff(c_8319,plain,(
    ! [B_323] :
      ( k1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_4'),B_323)) = '#skF_3'
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ v1_xboole_0(B_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7785,c_8315])).

tff(c_17823,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8319])).

tff(c_21471,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21432,c_17823])).

tff(c_21531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_21471])).

tff(c_21533,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8319])).

tff(c_5661,plain,(
    ! [B_320,A_319] :
      ( ~ v1_xboole_0(B_320)
      | ~ r1_tarski(A_319,B_320)
      | v1_xboole_0(A_319) ) ),
    inference(resolution,[status(thm)],[c_5654,c_2])).

tff(c_21547,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_21533,c_5661])).

tff(c_21566,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_21547])).

tff(c_21568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_21566])).

tff(c_21569,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_93,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_85])).

tff(c_99,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_21571,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21569,c_99])).

tff(c_27471,plain,(
    ! [C_993,A_994,B_995] :
      ( m1_subset_1(C_993,k1_zfmisc_1(k2_zfmisc_1(A_994,B_995)))
      | ~ r1_tarski(k2_relat_1(C_993),B_995)
      | ~ r1_tarski(k1_relat_1(C_993),A_994)
      | ~ v1_relat_1(C_993) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34602,plain,(
    ! [A_1222,B_1223,C_1224] :
      ( k1_relset_1(A_1222,B_1223,C_1224) = k1_relat_1(C_1224)
      | ~ r1_tarski(k2_relat_1(C_1224),B_1223)
      | ~ r1_tarski(k1_relat_1(C_1224),A_1222)
      | ~ v1_relat_1(C_1224) ) ),
    inference(resolution,[status(thm)],[c_27471,c_42])).

tff(c_34643,plain,(
    ! [A_1222,B_1223] :
      ( k1_relset_1(A_1222,B_1223,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_1223)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1222)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21569,c_34602])).

tff(c_35063,plain,(
    ! [A_1235,B_1236] :
      ( k1_relset_1(A_1235,B_1236,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_1236)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_34643])).

tff(c_35081,plain,(
    ! [A_1237] :
      ( k1_relset_1(A_1237,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1237) ) ),
    inference(resolution,[status(thm)],[c_18,c_35063])).

tff(c_35117,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_35081])).

tff(c_32794,plain,(
    ! [C_1162,A_1163,B_1164] :
      ( r1_tarski(C_1162,k2_zfmisc_1(A_1163,B_1164))
      | ~ r1_tarski(k2_relat_1(C_1162),B_1164)
      | ~ r1_tarski(k1_relat_1(C_1162),A_1163)
      | ~ v1_relat_1(C_1162) ) ),
    inference(resolution,[status(thm)],[c_27471,c_22])).

tff(c_47022,plain,(
    ! [C_1387,A_1388] :
      ( r1_tarski(C_1387,k2_zfmisc_1(A_1388,k2_relat_1(C_1387)))
      | ~ r1_tarski(k1_relat_1(C_1387),A_1388)
      | ~ v1_relat_1(C_1387) ) ),
    inference(resolution,[status(thm)],[c_18,c_32794])).

tff(c_47196,plain,(
    ! [A_1388] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1388,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1388)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21569,c_47022])).

tff(c_47290,plain,(
    ! [A_1389] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1389,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1389) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_47196])).

tff(c_47331,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_47290])).

tff(c_27616,plain,(
    ! [B_1002,C_1003,A_1004] :
      ( k1_xboole_0 = B_1002
      | v1_funct_2(C_1003,A_1004,B_1002)
      | k1_relset_1(A_1004,B_1002,C_1003) != A_1004
      | ~ m1_subset_1(C_1003,k1_zfmisc_1(k2_zfmisc_1(A_1004,B_1002))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_27625,plain,(
    ! [B_1002,A_15,A_1004] :
      ( k1_xboole_0 = B_1002
      | v1_funct_2(A_15,A_1004,B_1002)
      | k1_relset_1(A_1004,B_1002,A_15) != A_1004
      | ~ r1_tarski(A_15,k2_zfmisc_1(A_1004,B_1002)) ) ),
    inference(resolution,[status(thm)],[c_24,c_27616])).

tff(c_47343,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_47331,c_27625])).

tff(c_47396,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35117,c_47343])).

tff(c_47398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_21571,c_47396])).

tff(c_47399,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_47499,plain,(
    ! [C_1405,B_1406,A_1407] :
      ( r2_hidden(C_1405,B_1406)
      | ~ r2_hidden(C_1405,A_1407)
      | ~ r1_tarski(A_1407,B_1406) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48184,plain,(
    ! [A_1467,B_1468] :
      ( r2_hidden('#skF_1'(A_1467),B_1468)
      | ~ r1_tarski(A_1467,B_1468)
      | v1_xboole_0(A_1467) ) ),
    inference(resolution,[status(thm)],[c_4,c_47499])).

tff(c_48192,plain,(
    ! [B_1469,A_1470] :
      ( ~ v1_xboole_0(B_1469)
      | ~ r1_tarski(A_1470,B_1469)
      | v1_xboole_0(A_1470) ) ),
    inference(resolution,[status(thm)],[c_48184,c_2])).

tff(c_48239,plain,(
    ! [B_1471,A_1472] :
      ( ~ v1_xboole_0(B_1471)
      | v1_xboole_0(k2_relat_1(k2_zfmisc_1(A_1472,B_1471))) ) ),
    inference(resolution,[status(thm)],[c_32,c_48192])).

tff(c_47476,plain,(
    ! [A_1401,B_1402] :
      ( r2_hidden('#skF_2'(A_1401,B_1402),A_1401)
      | r1_tarski(A_1401,B_1402) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47486,plain,(
    ! [A_1401,B_1402] :
      ( ~ v1_xboole_0(A_1401)
      | r1_tarski(A_1401,B_1402) ) ),
    inference(resolution,[status(thm)],[c_47476,c_2])).

tff(c_47487,plain,(
    ! [A_1403,B_1404] :
      ( ~ v1_xboole_0(A_1403)
      | r1_tarski(A_1403,B_1404) ) ),
    inference(resolution,[status(thm)],[c_47476,c_2])).

tff(c_47907,plain,(
    ! [B_1440,A_1441] :
      ( B_1440 = A_1441
      | ~ r1_tarski(B_1440,A_1441)
      | ~ v1_xboole_0(A_1441) ) ),
    inference(resolution,[status(thm)],[c_47487,c_14])).

tff(c_47972,plain,(
    ! [B_1444,A_1445] :
      ( B_1444 = A_1445
      | ~ v1_xboole_0(B_1444)
      | ~ v1_xboole_0(A_1445) ) ),
    inference(resolution,[status(thm)],[c_47486,c_47907])).

tff(c_47975,plain,(
    ! [A_1445] :
      ( k1_xboole_0 = A_1445
      | ~ v1_xboole_0(A_1445) ) ),
    inference(resolution,[status(thm)],[c_12,c_47972])).

tff(c_48342,plain,(
    ! [A_1480,B_1481] :
      ( k2_relat_1(k2_zfmisc_1(A_1480,B_1481)) = k1_xboole_0
      | ~ v1_xboole_0(B_1481) ) ),
    inference(resolution,[status(thm)],[c_48239,c_47975])).

tff(c_48384,plain,(
    ! [B_1482] :
      ( r1_tarski(k1_xboole_0,B_1482)
      | ~ v1_xboole_0(B_1482) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48342,c_32])).

tff(c_47520,plain,(
    ! [A_1409,C_1410,B_1411] :
      ( r1_tarski(A_1409,C_1410)
      | ~ r1_tarski(B_1411,C_1410)
      | ~ r1_tarski(A_1409,B_1411) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_47531,plain,(
    ! [A_1409,B_1402,A_1401] :
      ( r1_tarski(A_1409,B_1402)
      | ~ r1_tarski(A_1409,A_1401)
      | ~ v1_xboole_0(A_1401) ) ),
    inference(resolution,[status(thm)],[c_47486,c_47520])).

tff(c_48411,plain,(
    ! [B_1402,B_1482] :
      ( r1_tarski(k1_xboole_0,B_1402)
      | ~ v1_xboole_0(B_1482) ) ),
    inference(resolution,[status(thm)],[c_48384,c_47531])).

tff(c_48489,plain,(
    ! [B_1482] : ~ v1_xboole_0(B_1482) ),
    inference(splitLeft,[status(thm)],[c_48411])).

tff(c_48496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48489,c_12])).

tff(c_48497,plain,(
    ! [B_1402] : r1_tarski(k1_xboole_0,B_1402) ),
    inference(splitRight,[status(thm)],[c_48411])).

tff(c_47400,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_49760,plain,(
    ! [C_1536,A_1537,B_1538] :
      ( m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(A_1537,B_1538)))
      | ~ r1_tarski(k2_relat_1(C_1536),B_1538)
      | ~ r1_tarski(k1_relat_1(C_1536),A_1537)
      | ~ v1_relat_1(C_1536) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56919,plain,(
    ! [C_1721,A_1722,B_1723] :
      ( r1_tarski(C_1721,k2_zfmisc_1(A_1722,B_1723))
      | ~ r1_tarski(k2_relat_1(C_1721),B_1723)
      | ~ r1_tarski(k1_relat_1(C_1721),A_1722)
      | ~ v1_relat_1(C_1721) ) ),
    inference(resolution,[status(thm)],[c_49760,c_22])).

tff(c_56962,plain,(
    ! [A_1722,B_1723] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1722,B_1723))
      | ~ r1_tarski(k1_xboole_0,B_1723)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_1722)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47400,c_56919])).

tff(c_57015,plain,(
    ! [A_1724,B_1725] : r1_tarski('#skF_4',k2_zfmisc_1(A_1724,B_1725)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_48497,c_47399,c_48497,c_56962])).

tff(c_48178,plain,(
    ! [A_1464,B_1465,C_1466] :
      ( k1_relset_1(A_1464,B_1465,C_1466) = k1_relat_1(C_1466)
      | ~ m1_subset_1(C_1466,k1_zfmisc_1(k2_zfmisc_1(A_1464,B_1465))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48183,plain,(
    ! [A_1464,B_1465,A_15] :
      ( k1_relset_1(A_1464,B_1465,A_15) = k1_relat_1(A_15)
      | ~ r1_tarski(A_15,k2_zfmisc_1(A_1464,B_1465)) ) ),
    inference(resolution,[status(thm)],[c_24,c_48178])).

tff(c_57034,plain,(
    ! [A_1724,B_1725] : k1_relset_1(A_1724,B_1725,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_57015,c_48183])).

tff(c_57060,plain,(
    ! [A_1724,B_1725] : k1_relset_1(A_1724,B_1725,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47399,c_57034])).

tff(c_49207,plain,(
    ! [C_1507,B_1508] :
      ( v1_funct_2(C_1507,k1_xboole_0,B_1508)
      | k1_relset_1(k1_xboole_0,B_1508,C_1507) != k1_xboole_0
      | ~ m1_subset_1(C_1507,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_1508))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_49212,plain,(
    ! [A_15,B_1508] :
      ( v1_funct_2(A_15,k1_xboole_0,B_1508)
      | k1_relset_1(k1_xboole_0,B_1508,A_15) != k1_xboole_0
      | ~ r1_tarski(A_15,k2_zfmisc_1(k1_xboole_0,B_1508)) ) ),
    inference(resolution,[status(thm)],[c_24,c_49207])).

tff(c_57050,plain,(
    ! [B_1725] :
      ( v1_funct_2('#skF_4',k1_xboole_0,B_1725)
      | k1_relset_1(k1_xboole_0,B_1725,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_57015,c_49212])).

tff(c_57523,plain,(
    ! [B_1725] : v1_funct_2('#skF_4',k1_xboole_0,B_1725) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57060,c_57050])).

tff(c_47401,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47399,c_77])).

tff(c_57526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57523,c_47401])).

tff(c_57527,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_59850,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_59826,c_57527])).

tff(c_59862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_18,c_60,c_59850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.24/6.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.24/6.35  
% 14.24/6.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.24/6.35  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 14.24/6.35  
% 14.24/6.35  %Foreground sorts:
% 14.24/6.35  
% 14.24/6.35  
% 14.24/6.35  %Background operators:
% 14.24/6.35  
% 14.24/6.35  
% 14.24/6.35  %Foreground operators:
% 14.24/6.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.24/6.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.24/6.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.24/6.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.24/6.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.24/6.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.24/6.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.24/6.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.24/6.35  tff('#skF_3', type, '#skF_3': $i).
% 14.24/6.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.24/6.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.24/6.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.24/6.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.24/6.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.24/6.35  tff('#skF_4', type, '#skF_4': $i).
% 14.24/6.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.24/6.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.24/6.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.24/6.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.24/6.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.24/6.35  
% 14.53/6.37  tff(f_128, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 14.53/6.37  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.53/6.37  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 14.53/6.37  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.53/6.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.53/6.37  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.53/6.37  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.53/6.37  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.53/6.37  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 14.53/6.37  tff(f_68, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 14.53/6.37  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 14.53/6.37  tff(f_85, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 14.53/6.37  tff(f_66, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 14.53/6.37  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 14.53/6.37  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.53/6.37  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.53/6.37  tff(c_60, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.53/6.37  tff(c_59826, plain, (![C_1892, A_1893, B_1894]: (m1_subset_1(C_1892, k1_zfmisc_1(k2_zfmisc_1(A_1893, B_1894))) | ~r1_tarski(k2_relat_1(C_1892), B_1894) | ~r1_tarski(k1_relat_1(C_1892), A_1893) | ~v1_relat_1(C_1892))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.53/6.37  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.53/6.37  tff(c_58, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.53/6.37  tff(c_66, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58])).
% 14.53/6.37  tff(c_77, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 14.53/6.37  tff(c_129, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.53/6.37  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.53/6.37  tff(c_139, plain, (![A_64, B_65]: (~v1_xboole_0(A_64) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_129, c_2])).
% 14.53/6.37  tff(c_140, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.53/6.37  tff(c_151, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_140])).
% 14.53/6.37  tff(c_173, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_151])).
% 14.53/6.37  tff(c_177, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_139, c_173])).
% 14.53/6.37  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.53/6.37  tff(c_7365, plain, (![C_398, A_399, B_400]: (m1_subset_1(C_398, k1_zfmisc_1(k2_zfmisc_1(A_399, B_400))) | ~r1_tarski(k2_relat_1(C_398), B_400) | ~r1_tarski(k1_relat_1(C_398), A_399) | ~v1_relat_1(C_398))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.53/6.37  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.53/6.37  tff(c_19203, plain, (![C_631, A_632, B_633]: (r1_tarski(C_631, k2_zfmisc_1(A_632, B_633)) | ~r1_tarski(k2_relat_1(C_631), B_633) | ~r1_tarski(k1_relat_1(C_631), A_632) | ~v1_relat_1(C_631))), inference(resolution, [status(thm)], [c_7365, c_22])).
% 14.53/6.37  tff(c_19264, plain, (![A_632]: (r1_tarski('#skF_4', k2_zfmisc_1(A_632, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_632) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_19203])).
% 14.53/6.37  tff(c_19408, plain, (![A_640]: (r1_tarski('#skF_4', k2_zfmisc_1(A_640, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_640))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_19264])).
% 14.53/6.37  tff(c_19439, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_19408])).
% 14.53/6.37  tff(c_24, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.53/6.37  tff(c_5745, plain, (![A_329, B_330, C_331]: (k1_relset_1(A_329, B_330, C_331)=k1_relat_1(C_331) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.53/6.37  tff(c_5750, plain, (![A_329, B_330, A_15]: (k1_relset_1(A_329, B_330, A_15)=k1_relat_1(A_15) | ~r1_tarski(A_15, k2_zfmisc_1(A_329, B_330)))), inference(resolution, [status(thm)], [c_24, c_5745])).
% 14.53/6.37  tff(c_19469, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_19439, c_5750])).
% 14.53/6.37  tff(c_7612, plain, (![B_407, C_408, A_409]: (k1_xboole_0=B_407 | v1_funct_2(C_408, A_409, B_407) | k1_relset_1(A_409, B_407, C_408)!=A_409 | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_409, B_407))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.53/6.37  tff(c_21322, plain, (![B_678, A_679, A_680]: (k1_xboole_0=B_678 | v1_funct_2(A_679, A_680, B_678) | k1_relset_1(A_680, B_678, A_679)!=A_680 | ~r1_tarski(A_679, k2_zfmisc_1(A_680, B_678)))), inference(resolution, [status(thm)], [c_24, c_7612])).
% 14.53/6.37  tff(c_21331, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_19439, c_21322])).
% 14.53/6.37  tff(c_21431, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19469, c_21331])).
% 14.53/6.37  tff(c_21432, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_77, c_21431])).
% 14.53/6.37  tff(c_32, plain, (![A_24, B_25]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_24, B_25)), B_25))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.53/6.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.53/6.37  tff(c_5400, plain, (![C_295, B_296, A_297]: (r2_hidden(C_295, B_296) | ~r2_hidden(C_295, A_297) | ~r1_tarski(A_297, B_296))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.53/6.37  tff(c_5654, plain, (![A_319, B_320]: (r2_hidden('#skF_1'(A_319), B_320) | ~r1_tarski(A_319, B_320) | v1_xboole_0(A_319))), inference(resolution, [status(thm)], [c_4, c_5400])).
% 14.53/6.37  tff(c_5662, plain, (![B_321, A_322]: (~v1_xboole_0(B_321) | ~r1_tarski(A_322, B_321) | v1_xboole_0(A_322))), inference(resolution, [status(thm)], [c_5654, c_2])).
% 14.53/6.37  tff(c_5703, plain, (![B_323, A_324]: (~v1_xboole_0(B_323) | v1_xboole_0(k2_relat_1(k2_zfmisc_1(A_324, B_323))))), inference(resolution, [status(thm)], [c_32, c_5662])).
% 14.53/6.37  tff(c_156, plain, (![A_68, B_69]: (~v1_xboole_0(A_68) | r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_129, c_2])).
% 14.53/6.37  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.53/6.37  tff(c_5329, plain, (![B_287, A_288]: (B_287=A_288 | ~r1_tarski(B_287, A_288) | ~v1_xboole_0(A_288))), inference(resolution, [status(thm)], [c_156, c_14])).
% 14.53/6.37  tff(c_5351, plain, (![B_289, A_290]: (B_289=A_290 | ~v1_xboole_0(B_289) | ~v1_xboole_0(A_290))), inference(resolution, [status(thm)], [c_139, c_5329])).
% 14.53/6.37  tff(c_5354, plain, (![A_290]: (k1_xboole_0=A_290 | ~v1_xboole_0(A_290))), inference(resolution, [status(thm)], [c_12, c_5351])).
% 14.53/6.37  tff(c_5715, plain, (![A_324, B_323]: (k2_relat_1(k2_zfmisc_1(A_324, B_323))=k1_xboole_0 | ~v1_xboole_0(B_323))), inference(resolution, [status(thm)], [c_5703, c_5354])).
% 14.53/6.37  tff(c_28, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 14.53/6.37  tff(c_85, plain, (![A_53]: (k1_relat_1(A_53)=k1_xboole_0 | k2_relat_1(A_53)!=k1_xboole_0 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.53/6.37  tff(c_7771, plain, (![A_413, B_414]: (k1_relat_1(k2_zfmisc_1(A_413, B_414))=k1_xboole_0 | k2_relat_1(k2_zfmisc_1(A_413, B_414))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_85])).
% 14.53/6.37  tff(c_7785, plain, (![A_324, B_323]: (k1_relat_1(k2_zfmisc_1(A_324, B_323))=k1_xboole_0 | ~v1_xboole_0(B_323))), inference(superposition, [status(thm), theory('equality')], [c_5715, c_7771])).
% 14.53/6.37  tff(c_30, plain, (![A_22, B_23]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_22, B_23)), A_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.53/6.37  tff(c_5421, plain, (![A_300, C_301, B_302]: (r1_tarski(A_300, C_301) | ~r1_tarski(B_302, C_301) | ~r1_tarski(A_300, B_302))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.53/6.37  tff(c_5437, plain, (![A_303]: (r1_tarski(A_303, '#skF_3') | ~r1_tarski(A_303, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_60, c_5421])).
% 14.53/6.37  tff(c_5479, plain, (![B_305]: (r1_tarski(k1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_4'), B_305)), '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_5437])).
% 14.53/6.37  tff(c_8315, plain, (![B_433]: (k1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_4'), B_433))='#skF_3' | ~r1_tarski('#skF_3', k1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_4'), B_433))))), inference(resolution, [status(thm)], [c_5479, c_14])).
% 14.53/6.37  tff(c_8319, plain, (![B_323]: (k1_relat_1(k2_zfmisc_1(k2_relat_1('#skF_4'), B_323))='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0) | ~v1_xboole_0(B_323))), inference(superposition, [status(thm), theory('equality')], [c_7785, c_8315])).
% 14.53/6.37  tff(c_17823, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8319])).
% 14.53/6.37  tff(c_21471, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21432, c_17823])).
% 14.53/6.37  tff(c_21531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_21471])).
% 14.53/6.37  tff(c_21533, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8319])).
% 14.53/6.37  tff(c_5661, plain, (![B_320, A_319]: (~v1_xboole_0(B_320) | ~r1_tarski(A_319, B_320) | v1_xboole_0(A_319))), inference(resolution, [status(thm)], [c_5654, c_2])).
% 14.53/6.37  tff(c_21547, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_21533, c_5661])).
% 14.53/6.37  tff(c_21566, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_21547])).
% 14.53/6.37  tff(c_21568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_21566])).
% 14.53/6.37  tff(c_21569, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_151])).
% 14.53/6.37  tff(c_93, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_85])).
% 14.53/6.37  tff(c_99, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_93])).
% 14.53/6.37  tff(c_21571, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21569, c_99])).
% 14.53/6.37  tff(c_27471, plain, (![C_993, A_994, B_995]: (m1_subset_1(C_993, k1_zfmisc_1(k2_zfmisc_1(A_994, B_995))) | ~r1_tarski(k2_relat_1(C_993), B_995) | ~r1_tarski(k1_relat_1(C_993), A_994) | ~v1_relat_1(C_993))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.53/6.37  tff(c_42, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.53/6.37  tff(c_34602, plain, (![A_1222, B_1223, C_1224]: (k1_relset_1(A_1222, B_1223, C_1224)=k1_relat_1(C_1224) | ~r1_tarski(k2_relat_1(C_1224), B_1223) | ~r1_tarski(k1_relat_1(C_1224), A_1222) | ~v1_relat_1(C_1224))), inference(resolution, [status(thm)], [c_27471, c_42])).
% 14.53/6.37  tff(c_34643, plain, (![A_1222, B_1223]: (k1_relset_1(A_1222, B_1223, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_1223) | ~r1_tarski(k1_relat_1('#skF_4'), A_1222) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21569, c_34602])).
% 14.53/6.37  tff(c_35063, plain, (![A_1235, B_1236]: (k1_relset_1(A_1235, B_1236, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_1236) | ~r1_tarski(k1_relat_1('#skF_4'), A_1235))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_34643])).
% 14.53/6.37  tff(c_35081, plain, (![A_1237]: (k1_relset_1(A_1237, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), A_1237))), inference(resolution, [status(thm)], [c_18, c_35063])).
% 14.53/6.37  tff(c_35117, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_35081])).
% 14.53/6.37  tff(c_32794, plain, (![C_1162, A_1163, B_1164]: (r1_tarski(C_1162, k2_zfmisc_1(A_1163, B_1164)) | ~r1_tarski(k2_relat_1(C_1162), B_1164) | ~r1_tarski(k1_relat_1(C_1162), A_1163) | ~v1_relat_1(C_1162))), inference(resolution, [status(thm)], [c_27471, c_22])).
% 14.53/6.37  tff(c_47022, plain, (![C_1387, A_1388]: (r1_tarski(C_1387, k2_zfmisc_1(A_1388, k2_relat_1(C_1387))) | ~r1_tarski(k1_relat_1(C_1387), A_1388) | ~v1_relat_1(C_1387))), inference(resolution, [status(thm)], [c_18, c_32794])).
% 14.53/6.37  tff(c_47196, plain, (![A_1388]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1388, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_1388) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21569, c_47022])).
% 14.53/6.37  tff(c_47290, plain, (![A_1389]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1389, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_1389))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_47196])).
% 14.53/6.37  tff(c_47331, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_47290])).
% 14.53/6.37  tff(c_27616, plain, (![B_1002, C_1003, A_1004]: (k1_xboole_0=B_1002 | v1_funct_2(C_1003, A_1004, B_1002) | k1_relset_1(A_1004, B_1002, C_1003)!=A_1004 | ~m1_subset_1(C_1003, k1_zfmisc_1(k2_zfmisc_1(A_1004, B_1002))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.53/6.37  tff(c_27625, plain, (![B_1002, A_15, A_1004]: (k1_xboole_0=B_1002 | v1_funct_2(A_15, A_1004, B_1002) | k1_relset_1(A_1004, B_1002, A_15)!=A_1004 | ~r1_tarski(A_15, k2_zfmisc_1(A_1004, B_1002)))), inference(resolution, [status(thm)], [c_24, c_27616])).
% 14.53/6.37  tff(c_47343, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_47331, c_27625])).
% 14.53/6.37  tff(c_47396, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35117, c_47343])).
% 14.53/6.37  tff(c_47398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_21571, c_47396])).
% 14.53/6.37  tff(c_47399, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_93])).
% 14.53/6.37  tff(c_47499, plain, (![C_1405, B_1406, A_1407]: (r2_hidden(C_1405, B_1406) | ~r2_hidden(C_1405, A_1407) | ~r1_tarski(A_1407, B_1406))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.53/6.37  tff(c_48184, plain, (![A_1467, B_1468]: (r2_hidden('#skF_1'(A_1467), B_1468) | ~r1_tarski(A_1467, B_1468) | v1_xboole_0(A_1467))), inference(resolution, [status(thm)], [c_4, c_47499])).
% 14.53/6.37  tff(c_48192, plain, (![B_1469, A_1470]: (~v1_xboole_0(B_1469) | ~r1_tarski(A_1470, B_1469) | v1_xboole_0(A_1470))), inference(resolution, [status(thm)], [c_48184, c_2])).
% 14.53/6.37  tff(c_48239, plain, (![B_1471, A_1472]: (~v1_xboole_0(B_1471) | v1_xboole_0(k2_relat_1(k2_zfmisc_1(A_1472, B_1471))))), inference(resolution, [status(thm)], [c_32, c_48192])).
% 14.53/6.37  tff(c_47476, plain, (![A_1401, B_1402]: (r2_hidden('#skF_2'(A_1401, B_1402), A_1401) | r1_tarski(A_1401, B_1402))), inference(cnfTransformation, [status(thm)], [f_38])).
% 14.53/6.37  tff(c_47486, plain, (![A_1401, B_1402]: (~v1_xboole_0(A_1401) | r1_tarski(A_1401, B_1402))), inference(resolution, [status(thm)], [c_47476, c_2])).
% 14.53/6.37  tff(c_47487, plain, (![A_1403, B_1404]: (~v1_xboole_0(A_1403) | r1_tarski(A_1403, B_1404))), inference(resolution, [status(thm)], [c_47476, c_2])).
% 14.53/6.37  tff(c_47907, plain, (![B_1440, A_1441]: (B_1440=A_1441 | ~r1_tarski(B_1440, A_1441) | ~v1_xboole_0(A_1441))), inference(resolution, [status(thm)], [c_47487, c_14])).
% 14.53/6.37  tff(c_47972, plain, (![B_1444, A_1445]: (B_1444=A_1445 | ~v1_xboole_0(B_1444) | ~v1_xboole_0(A_1445))), inference(resolution, [status(thm)], [c_47486, c_47907])).
% 14.53/6.37  tff(c_47975, plain, (![A_1445]: (k1_xboole_0=A_1445 | ~v1_xboole_0(A_1445))), inference(resolution, [status(thm)], [c_12, c_47972])).
% 14.53/6.37  tff(c_48342, plain, (![A_1480, B_1481]: (k2_relat_1(k2_zfmisc_1(A_1480, B_1481))=k1_xboole_0 | ~v1_xboole_0(B_1481))), inference(resolution, [status(thm)], [c_48239, c_47975])).
% 14.53/6.37  tff(c_48384, plain, (![B_1482]: (r1_tarski(k1_xboole_0, B_1482) | ~v1_xboole_0(B_1482))), inference(superposition, [status(thm), theory('equality')], [c_48342, c_32])).
% 14.53/6.37  tff(c_47520, plain, (![A_1409, C_1410, B_1411]: (r1_tarski(A_1409, C_1410) | ~r1_tarski(B_1411, C_1410) | ~r1_tarski(A_1409, B_1411))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.53/6.37  tff(c_47531, plain, (![A_1409, B_1402, A_1401]: (r1_tarski(A_1409, B_1402) | ~r1_tarski(A_1409, A_1401) | ~v1_xboole_0(A_1401))), inference(resolution, [status(thm)], [c_47486, c_47520])).
% 14.53/6.37  tff(c_48411, plain, (![B_1402, B_1482]: (r1_tarski(k1_xboole_0, B_1402) | ~v1_xboole_0(B_1482))), inference(resolution, [status(thm)], [c_48384, c_47531])).
% 14.53/6.37  tff(c_48489, plain, (![B_1482]: (~v1_xboole_0(B_1482))), inference(splitLeft, [status(thm)], [c_48411])).
% 14.53/6.37  tff(c_48496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48489, c_12])).
% 14.53/6.37  tff(c_48497, plain, (![B_1402]: (r1_tarski(k1_xboole_0, B_1402))), inference(splitRight, [status(thm)], [c_48411])).
% 14.53/6.37  tff(c_47400, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_93])).
% 14.53/6.37  tff(c_49760, plain, (![C_1536, A_1537, B_1538]: (m1_subset_1(C_1536, k1_zfmisc_1(k2_zfmisc_1(A_1537, B_1538))) | ~r1_tarski(k2_relat_1(C_1536), B_1538) | ~r1_tarski(k1_relat_1(C_1536), A_1537) | ~v1_relat_1(C_1536))), inference(cnfTransformation, [status(thm)], [f_97])).
% 14.53/6.37  tff(c_56919, plain, (![C_1721, A_1722, B_1723]: (r1_tarski(C_1721, k2_zfmisc_1(A_1722, B_1723)) | ~r1_tarski(k2_relat_1(C_1721), B_1723) | ~r1_tarski(k1_relat_1(C_1721), A_1722) | ~v1_relat_1(C_1721))), inference(resolution, [status(thm)], [c_49760, c_22])).
% 14.53/6.37  tff(c_56962, plain, (![A_1722, B_1723]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1722, B_1723)) | ~r1_tarski(k1_xboole_0, B_1723) | ~r1_tarski(k1_relat_1('#skF_4'), A_1722) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_47400, c_56919])).
% 14.53/6.37  tff(c_57015, plain, (![A_1724, B_1725]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1724, B_1725)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_48497, c_47399, c_48497, c_56962])).
% 14.53/6.37  tff(c_48178, plain, (![A_1464, B_1465, C_1466]: (k1_relset_1(A_1464, B_1465, C_1466)=k1_relat_1(C_1466) | ~m1_subset_1(C_1466, k1_zfmisc_1(k2_zfmisc_1(A_1464, B_1465))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 14.53/6.37  tff(c_48183, plain, (![A_1464, B_1465, A_15]: (k1_relset_1(A_1464, B_1465, A_15)=k1_relat_1(A_15) | ~r1_tarski(A_15, k2_zfmisc_1(A_1464, B_1465)))), inference(resolution, [status(thm)], [c_24, c_48178])).
% 14.53/6.37  tff(c_57034, plain, (![A_1724, B_1725]: (k1_relset_1(A_1724, B_1725, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_57015, c_48183])).
% 14.53/6.37  tff(c_57060, plain, (![A_1724, B_1725]: (k1_relset_1(A_1724, B_1725, '#skF_4')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_47399, c_57034])).
% 14.53/6.37  tff(c_49207, plain, (![C_1507, B_1508]: (v1_funct_2(C_1507, k1_xboole_0, B_1508) | k1_relset_1(k1_xboole_0, B_1508, C_1507)!=k1_xboole_0 | ~m1_subset_1(C_1507, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_1508))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.53/6.37  tff(c_49212, plain, (![A_15, B_1508]: (v1_funct_2(A_15, k1_xboole_0, B_1508) | k1_relset_1(k1_xboole_0, B_1508, A_15)!=k1_xboole_0 | ~r1_tarski(A_15, k2_zfmisc_1(k1_xboole_0, B_1508)))), inference(resolution, [status(thm)], [c_24, c_49207])).
% 14.53/6.37  tff(c_57050, plain, (![B_1725]: (v1_funct_2('#skF_4', k1_xboole_0, B_1725) | k1_relset_1(k1_xboole_0, B_1725, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_57015, c_49212])).
% 14.53/6.37  tff(c_57523, plain, (![B_1725]: (v1_funct_2('#skF_4', k1_xboole_0, B_1725))), inference(demodulation, [status(thm), theory('equality')], [c_57060, c_57050])).
% 14.53/6.37  tff(c_47401, plain, (~v1_funct_2('#skF_4', k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47399, c_77])).
% 14.53/6.37  tff(c_57526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57523, c_47401])).
% 14.53/6.37  tff(c_57527, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 14.53/6.37  tff(c_59850, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_59826, c_57527])).
% 14.53/6.37  tff(c_59862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_18, c_60, c_59850])).
% 14.53/6.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.53/6.37  
% 14.53/6.37  Inference rules
% 14.53/6.37  ----------------------
% 14.53/6.37  #Ref     : 0
% 14.53/6.37  #Sup     : 13726
% 14.53/6.37  #Fact    : 0
% 14.53/6.37  #Define  : 0
% 14.53/6.37  #Split   : 41
% 14.53/6.37  #Chain   : 0
% 14.53/6.37  #Close   : 0
% 14.53/6.37  
% 14.53/6.37  Ordering : KBO
% 14.53/6.37  
% 14.53/6.37  Simplification rules
% 14.53/6.37  ----------------------
% 14.53/6.37  #Subsume      : 5827
% 14.53/6.37  #Demod        : 9748
% 14.53/6.37  #Tautology    : 4517
% 14.53/6.37  #SimpNegUnit  : 207
% 14.53/6.37  #BackRed      : 141
% 14.53/6.37  
% 14.53/6.37  #Partial instantiations: 0
% 14.53/6.37  #Strategies tried      : 1
% 14.53/6.37  
% 14.53/6.37  Timing (in seconds)
% 14.53/6.37  ----------------------
% 14.53/6.38  Preprocessing        : 0.34
% 14.53/6.38  Parsing              : 0.18
% 14.53/6.38  CNF conversion       : 0.02
% 14.53/6.38  Main loop            : 5.25
% 14.53/6.38  Inferencing          : 1.30
% 14.53/6.38  Reduction            : 1.86
% 14.53/6.38  Demodulation         : 1.36
% 14.53/6.38  BG Simplification    : 0.13
% 14.53/6.38  Subsumption          : 1.63
% 14.53/6.38  Abstraction          : 0.23
% 14.53/6.38  MUC search           : 0.00
% 14.53/6.38  Cooper               : 0.00
% 14.53/6.38  Total                : 5.65
% 14.53/6.38  Index Insertion      : 0.00
% 14.53/6.38  Index Deletion       : 0.00
% 14.53/6.38  Index Matching       : 0.00
% 14.53/6.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
