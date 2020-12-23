%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:47 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 770 expanded)
%              Number of leaves         :   37 ( 269 expanded)
%              Depth                    :   11
%              Number of atoms          :  309 (2157 expanded)
%              Number of equality atoms :  119 ( 652 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_117,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1725,plain,(
    ! [C_222,A_223,B_224] :
      ( v1_relat_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1737,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1725])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_74,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_72,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2003,plain,(
    ! [A_264,B_265,C_266] :
      ( k2_relset_1(A_264,B_265,C_266) = k2_relat_1(C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2012,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2003])).

tff(c_2022,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2012])).

tff(c_30,plain,(
    ! [A_11] :
      ( k1_relat_1(k2_funct_1(A_11)) = k2_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [A_10] :
      ( v1_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_158,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_161,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_158])).

tff(c_164,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_161])).

tff(c_173,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_176,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_173])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_176])).

tff(c_185,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_194,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_196,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_204,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_196])).

tff(c_408,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_relset_1(A_83,B_84,C_85) = k2_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_414,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_408])).

tff(c_423,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_414])).

tff(c_26,plain,(
    ! [A_10] :
      ( v1_relat_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_186,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_295,plain,(
    ! [A_66] :
      ( k1_relat_1(k2_funct_1(A_66)) = k2_relat_1(A_66)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_60,plain,(
    ! [A_25] :
      ( v1_funct_2(A_25,k1_relat_1(A_25),k2_relat_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_965,plain,(
    ! [A_134] :
      ( v1_funct_2(k2_funct_1(A_134),k2_relat_1(A_134),k2_relat_1(k2_funct_1(A_134)))
      | ~ v1_funct_1(k2_funct_1(A_134))
      | ~ v1_relat_1(k2_funct_1(A_134))
      | ~ v2_funct_1(A_134)
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_60])).

tff(c_968,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_965])).

tff(c_979,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_80,c_74,c_186,c_968])).

tff(c_982,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_979])).

tff(c_985,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_982])).

tff(c_989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_80,c_985])).

tff(c_991,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_979])).

tff(c_20,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_211,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_204,c_20])).

tff(c_213,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_437,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_213])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_323,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_333,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_323])).

tff(c_813,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_825,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_813])).

tff(c_840,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_333,c_825])).

tff(c_841,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_437,c_840])).

tff(c_28,plain,(
    ! [A_11] :
      ( k2_relat_1(k2_funct_1(A_11)) = k1_relat_1(A_11)
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_350,plain,(
    ! [A_75] :
      ( m1_subset_1(A_75,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_75),k2_relat_1(A_75))))
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1060,plain,(
    ! [A_137] :
      ( m1_subset_1(k2_funct_1(A_137),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_137)),k1_relat_1(A_137))))
      | ~ v1_funct_1(k2_funct_1(A_137))
      | ~ v1_relat_1(k2_funct_1(A_137))
      | ~ v2_funct_1(A_137)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_350])).

tff(c_1078,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_1060])).

tff(c_1094,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_80,c_74,c_991,c_186,c_1078])).

tff(c_1114,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1094])).

tff(c_1127,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_80,c_74,c_423,c_1114])).

tff(c_1129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_1127])).

tff(c_1130,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_22,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_83,plain,(
    ! [A_22] :
      ( v1_funct_2(k1_xboole_0,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_1232,plain,(
    ! [A_22] :
      ( v1_funct_2('#skF_4',A_22,'#skF_4')
      | A_22 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1130,c_1130,c_1130,c_1130,c_83])).

tff(c_1233,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1232])).

tff(c_1139,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1130,c_12])).

tff(c_1131,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_1156,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1131])).

tff(c_1288,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1297,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1288])).

tff(c_1299,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1156,c_72,c_1297])).

tff(c_1301,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_76])).

tff(c_1305,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_1301])).

tff(c_1307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1233,c_1305])).

tff(c_1309,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1141,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1130,c_18])).

tff(c_134,plain,(
    ! [A_34] :
      ( k2_relat_1(A_34) != k1_xboole_0
      | k1_xboole_0 = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_141,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) != k1_xboole_0
      | k2_funct_1(A_10) = k1_xboole_0
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_26,c_134])).

tff(c_1361,plain,(
    ! [A_169] :
      ( k2_relat_1(k2_funct_1(A_169)) != '#skF_4'
      | k2_funct_1(A_169) = '#skF_4'
      | ~ v1_funct_1(A_169)
      | ~ v1_relat_1(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1130,c_141])).

tff(c_1710,plain,(
    ! [A_220] :
      ( k1_relat_1(A_220) != '#skF_4'
      | k2_funct_1(A_220) = '#skF_4'
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220)
      | ~ v2_funct_1(A_220)
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1361])).

tff(c_1713,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1710])).

tff(c_1716,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_80,c_1141,c_1713])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1140,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_4',B_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1130,c_14])).

tff(c_1370,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relset_1(A_171,B_172,C_173) = k2_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1379,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1370])).

tff(c_1381,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1156,c_1379])).

tff(c_1382,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_194])).

tff(c_1386,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1140,c_1382])).

tff(c_1717,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_1386])).

tff(c_1721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1309,c_1717])).

tff(c_1722,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_1744,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1737,c_20])).

tff(c_1758,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1744])).

tff(c_2023,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_1758])).

tff(c_1923,plain,(
    ! [A_254,B_255,C_256] :
      ( k1_relset_1(A_254,B_255,C_256) = k1_relat_1(C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1937,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1923])).

tff(c_2325,plain,(
    ! [B_299,A_300,C_301] :
      ( k1_xboole_0 = B_299
      | k1_relset_1(A_300,B_299,C_301) = A_300
      | ~ v1_funct_2(C_301,A_300,B_299)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_300,B_299))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2340,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2325])).

tff(c_2357,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1937,c_2340])).

tff(c_2358,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2023,c_2357])).

tff(c_22,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1745,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1737,c_22])).

tff(c_1759,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1745])).

tff(c_2366,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2358,c_1759])).

tff(c_1723,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_1936,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1723,c_1923])).

tff(c_2454,plain,(
    ! [B_306,C_307,A_308] :
      ( k1_xboole_0 = B_306
      | v1_funct_2(C_307,A_308,B_306)
      | k1_relset_1(A_308,B_306,C_307) != A_308
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_308,B_306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2466,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1723,c_2454])).

tff(c_2480,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1936,c_2466])).

tff(c_2481,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1722,c_2366,c_2480])).

tff(c_2489,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2481])).

tff(c_2492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_80,c_74,c_2022,c_2489])).

tff(c_2493,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1745])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2503,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2493,c_2493,c_16])).

tff(c_2495,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2493,c_1758])).

tff(c_2524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2503,c_2495])).

tff(c_2525,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1744])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2535,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2525,c_8])).

tff(c_2526,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1744])).

tff(c_2545,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2525,c_2526])).

tff(c_2532,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2525,c_2525,c_18])).

tff(c_3184,plain,(
    ! [B_361,A_362] :
      ( v1_funct_2(B_361,k1_relat_1(B_361),A_362)
      | ~ r1_tarski(k2_relat_1(B_361),A_362)
      | ~ v1_funct_1(B_361)
      | ~ v1_relat_1(B_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3193,plain,(
    ! [A_362] :
      ( v1_funct_2('#skF_4','#skF_4',A_362)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_362)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2532,c_3184])).

tff(c_3196,plain,(
    ! [A_362] : v1_funct_2('#skF_4','#skF_4',A_362) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_80,c_2535,c_2545,c_3193])).

tff(c_3090,plain,(
    ! [A_352,B_353,C_354] :
      ( k2_relset_1(A_352,B_353,C_354) = k2_relat_1(C_354)
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(A_352,B_353))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3102,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_3090])).

tff(c_3106,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2545,c_3102])).

tff(c_1736,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1723,c_1725])).

tff(c_1752,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1736,c_20])).

tff(c_2934,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2525,c_2525,c_1752])).

tff(c_2935,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2934])).

tff(c_2938,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2935])).

tff(c_2941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_80,c_74,c_2532,c_2938])).

tff(c_2942,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2934])).

tff(c_2946,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2942,c_1722])).

tff(c_3110,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3106,c_2946])).

tff(c_3200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3196,c_3110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.85  
% 4.83/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.85  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.83/1.85  
% 4.83/1.85  %Foreground sorts:
% 4.83/1.85  
% 4.83/1.85  
% 4.83/1.85  %Background operators:
% 4.83/1.85  
% 4.83/1.85  
% 4.83/1.85  %Foreground operators:
% 4.83/1.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.83/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.83/1.85  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.83/1.85  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.83/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.83/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.83/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.83/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.83/1.85  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 4.83/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.83/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.83/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.83/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.83/1.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.83/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.83/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.83/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.83/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.83/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.83/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/1.85  
% 4.83/1.88  tff(f_146, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.83/1.88  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.83/1.88  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.83/1.88  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.83/1.88  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.83/1.88  tff(f_117, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.83/1.88  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.83/1.88  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.83/1.88  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.83/1.88  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.83/1.88  tff(f_43, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.83/1.88  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.83/1.88  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.83/1.88  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.83/1.88  tff(c_1725, plain, (![C_222, A_223, B_224]: (v1_relat_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.83/1.88  tff(c_1737, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1725])).
% 4.83/1.88  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.83/1.88  tff(c_74, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.83/1.88  tff(c_72, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.83/1.88  tff(c_2003, plain, (![A_264, B_265, C_266]: (k2_relset_1(A_264, B_265, C_266)=k2_relat_1(C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.83/1.88  tff(c_2012, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2003])).
% 4.83/1.88  tff(c_2022, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2012])).
% 4.83/1.88  tff(c_30, plain, (![A_11]: (k1_relat_1(k2_funct_1(A_11))=k2_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.83/1.88  tff(c_24, plain, (![A_10]: (v1_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.83/1.88  tff(c_70, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.83/1.88  tff(c_158, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_70])).
% 4.83/1.88  tff(c_161, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_158])).
% 4.83/1.88  tff(c_164, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_161])).
% 4.83/1.88  tff(c_173, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.83/1.88  tff(c_176, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_173])).
% 4.83/1.88  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_176])).
% 4.83/1.88  tff(c_185, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_70])).
% 4.83/1.88  tff(c_194, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_185])).
% 4.83/1.88  tff(c_196, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.83/1.88  tff(c_204, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_196])).
% 4.83/1.88  tff(c_408, plain, (![A_83, B_84, C_85]: (k2_relset_1(A_83, B_84, C_85)=k2_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.83/1.88  tff(c_414, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_408])).
% 4.83/1.88  tff(c_423, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_414])).
% 4.83/1.88  tff(c_26, plain, (![A_10]: (v1_relat_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.83/1.88  tff(c_186, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_70])).
% 4.83/1.88  tff(c_295, plain, (![A_66]: (k1_relat_1(k2_funct_1(A_66))=k2_relat_1(A_66) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.83/1.88  tff(c_60, plain, (![A_25]: (v1_funct_2(A_25, k1_relat_1(A_25), k2_relat_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.83/1.88  tff(c_965, plain, (![A_134]: (v1_funct_2(k2_funct_1(A_134), k2_relat_1(A_134), k2_relat_1(k2_funct_1(A_134))) | ~v1_funct_1(k2_funct_1(A_134)) | ~v1_relat_1(k2_funct_1(A_134)) | ~v2_funct_1(A_134) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(superposition, [status(thm), theory('equality')], [c_295, c_60])).
% 4.83/1.88  tff(c_968, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_423, c_965])).
% 4.83/1.88  tff(c_979, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_80, c_74, c_186, c_968])).
% 4.83/1.88  tff(c_982, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_979])).
% 4.83/1.88  tff(c_985, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_982])).
% 4.83/1.88  tff(c_989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_204, c_80, c_985])).
% 4.83/1.88  tff(c_991, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_979])).
% 4.83/1.88  tff(c_20, plain, (![A_9]: (k2_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.83/1.88  tff(c_211, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_204, c_20])).
% 4.83/1.88  tff(c_213, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_211])).
% 4.83/1.88  tff(c_437, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_423, c_213])).
% 4.83/1.88  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 4.83/1.88  tff(c_323, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.83/1.88  tff(c_333, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_323])).
% 4.83/1.88  tff(c_813, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.83/1.88  tff(c_825, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_813])).
% 4.83/1.88  tff(c_840, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_333, c_825])).
% 4.83/1.88  tff(c_841, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_437, c_840])).
% 4.83/1.88  tff(c_28, plain, (![A_11]: (k2_relat_1(k2_funct_1(A_11))=k1_relat_1(A_11) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.83/1.88  tff(c_350, plain, (![A_75]: (m1_subset_1(A_75, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_75), k2_relat_1(A_75)))) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.83/1.88  tff(c_1060, plain, (![A_137]: (m1_subset_1(k2_funct_1(A_137), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_137)), k1_relat_1(A_137)))) | ~v1_funct_1(k2_funct_1(A_137)) | ~v1_relat_1(k2_funct_1(A_137)) | ~v2_funct_1(A_137) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(superposition, [status(thm), theory('equality')], [c_28, c_350])).
% 4.83/1.88  tff(c_1078, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_841, c_1060])).
% 4.83/1.88  tff(c_1094, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_80, c_74, c_991, c_186, c_1078])).
% 4.83/1.88  tff(c_1114, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1094])).
% 4.83/1.88  tff(c_1127, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_80, c_74, c_423, c_1114])).
% 4.83/1.88  tff(c_1129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_1127])).
% 4.83/1.88  tff(c_1130, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_211])).
% 4.83/1.88  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.83/1.88  tff(c_46, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_22, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.83/1.88  tff(c_83, plain, (![A_22]: (v1_funct_2(k1_xboole_0, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 4.83/1.88  tff(c_1232, plain, (![A_22]: (v1_funct_2('#skF_4', A_22, '#skF_4') | A_22='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1130, c_1130, c_1130, c_1130, c_83])).
% 4.83/1.88  tff(c_1233, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1232])).
% 4.83/1.88  tff(c_1139, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1130, c_12])).
% 4.83/1.88  tff(c_1131, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_211])).
% 4.83/1.88  tff(c_1156, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1131])).
% 4.83/1.88  tff(c_1288, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.83/1.88  tff(c_1297, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1288])).
% 4.83/1.88  tff(c_1299, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1156, c_72, c_1297])).
% 4.83/1.88  tff(c_1301, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_76])).
% 4.83/1.88  tff(c_1305, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_1301])).
% 4.83/1.88  tff(c_1307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1233, c_1305])).
% 4.83/1.88  tff(c_1309, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1232])).
% 4.83/1.88  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.83/1.88  tff(c_1141, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1130, c_18])).
% 4.83/1.88  tff(c_134, plain, (![A_34]: (k2_relat_1(A_34)!=k1_xboole_0 | k1_xboole_0=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.83/1.88  tff(c_141, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))!=k1_xboole_0 | k2_funct_1(A_10)=k1_xboole_0 | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_26, c_134])).
% 4.83/1.88  tff(c_1361, plain, (![A_169]: (k2_relat_1(k2_funct_1(A_169))!='#skF_4' | k2_funct_1(A_169)='#skF_4' | ~v1_funct_1(A_169) | ~v1_relat_1(A_169))), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1130, c_141])).
% 4.83/1.88  tff(c_1710, plain, (![A_220]: (k1_relat_1(A_220)!='#skF_4' | k2_funct_1(A_220)='#skF_4' | ~v1_funct_1(A_220) | ~v1_relat_1(A_220) | ~v2_funct_1(A_220) | ~v1_funct_1(A_220) | ~v1_relat_1(A_220))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1361])).
% 4.83/1.88  tff(c_1713, plain, (k1_relat_1('#skF_4')!='#skF_4' | k2_funct_1('#skF_4')='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1710])).
% 4.83/1.88  tff(c_1716, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_80, c_1141, c_1713])).
% 4.83/1.88  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.83/1.88  tff(c_1140, plain, (![B_8]: (k2_zfmisc_1('#skF_4', B_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1130, c_14])).
% 4.83/1.88  tff(c_1370, plain, (![A_171, B_172, C_173]: (k2_relset_1(A_171, B_172, C_173)=k2_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.83/1.88  tff(c_1379, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1370])).
% 4.83/1.88  tff(c_1381, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1156, c_1379])).
% 4.83/1.88  tff(c_1382, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1381, c_194])).
% 4.83/1.88  tff(c_1386, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1140, c_1382])).
% 4.83/1.88  tff(c_1717, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1716, c_1386])).
% 4.83/1.88  tff(c_1721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1309, c_1717])).
% 4.83/1.88  tff(c_1722, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_185])).
% 4.83/1.88  tff(c_1744, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1737, c_20])).
% 4.83/1.88  tff(c_1758, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1744])).
% 4.83/1.88  tff(c_2023, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2022, c_1758])).
% 4.83/1.88  tff(c_1923, plain, (![A_254, B_255, C_256]: (k1_relset_1(A_254, B_255, C_256)=k1_relat_1(C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.83/1.88  tff(c_1937, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1923])).
% 4.83/1.88  tff(c_2325, plain, (![B_299, A_300, C_301]: (k1_xboole_0=B_299 | k1_relset_1(A_300, B_299, C_301)=A_300 | ~v1_funct_2(C_301, A_300, B_299) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_300, B_299))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.83/1.88  tff(c_2340, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_2325])).
% 4.83/1.88  tff(c_2357, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1937, c_2340])).
% 4.83/1.88  tff(c_2358, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2023, c_2357])).
% 4.83/1.88  tff(c_22, plain, (![A_9]: (k1_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.83/1.88  tff(c_1745, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1737, c_22])).
% 4.83/1.88  tff(c_1759, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1745])).
% 4.83/1.88  tff(c_2366, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2358, c_1759])).
% 4.83/1.88  tff(c_1723, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_185])).
% 4.83/1.88  tff(c_1936, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1723, c_1923])).
% 4.83/1.88  tff(c_2454, plain, (![B_306, C_307, A_308]: (k1_xboole_0=B_306 | v1_funct_2(C_307, A_308, B_306) | k1_relset_1(A_308, B_306, C_307)!=A_308 | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_308, B_306))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.83/1.88  tff(c_2466, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_1723, c_2454])).
% 4.83/1.88  tff(c_2480, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1936, c_2466])).
% 4.83/1.88  tff(c_2481, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1722, c_2366, c_2480])).
% 4.83/1.88  tff(c_2489, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2481])).
% 4.83/1.88  tff(c_2492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1737, c_80, c_74, c_2022, c_2489])).
% 4.83/1.88  tff(c_2493, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1745])).
% 4.83/1.88  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.83/1.88  tff(c_2503, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2493, c_2493, c_16])).
% 4.83/1.88  tff(c_2495, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2493, c_1758])).
% 4.83/1.88  tff(c_2524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2503, c_2495])).
% 4.83/1.88  tff(c_2525, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1744])).
% 4.83/1.88  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.83/1.88  tff(c_2535, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2525, c_8])).
% 4.83/1.88  tff(c_2526, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1744])).
% 4.83/1.88  tff(c_2545, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2525, c_2526])).
% 4.83/1.88  tff(c_2532, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2525, c_2525, c_18])).
% 4.83/1.88  tff(c_3184, plain, (![B_361, A_362]: (v1_funct_2(B_361, k1_relat_1(B_361), A_362) | ~r1_tarski(k2_relat_1(B_361), A_362) | ~v1_funct_1(B_361) | ~v1_relat_1(B_361))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.83/1.88  tff(c_3193, plain, (![A_362]: (v1_funct_2('#skF_4', '#skF_4', A_362) | ~r1_tarski(k2_relat_1('#skF_4'), A_362) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2532, c_3184])).
% 4.83/1.88  tff(c_3196, plain, (![A_362]: (v1_funct_2('#skF_4', '#skF_4', A_362))), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_80, c_2535, c_2545, c_3193])).
% 4.83/1.88  tff(c_3090, plain, (![A_352, B_353, C_354]: (k2_relset_1(A_352, B_353, C_354)=k2_relat_1(C_354) | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(A_352, B_353))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.83/1.88  tff(c_3102, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_3090])).
% 4.83/1.88  tff(c_3106, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2545, c_3102])).
% 4.83/1.88  tff(c_1736, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1723, c_1725])).
% 4.83/1.88  tff(c_1752, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0 | k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1736, c_20])).
% 4.83/1.88  tff(c_2934, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2525, c_2525, c_1752])).
% 4.83/1.88  tff(c_2935, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_2934])).
% 4.83/1.88  tff(c_2938, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_2935])).
% 4.83/1.88  tff(c_2941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1737, c_80, c_74, c_2532, c_2938])).
% 4.83/1.88  tff(c_2942, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_2934])).
% 4.83/1.88  tff(c_2946, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2942, c_1722])).
% 4.83/1.88  tff(c_3110, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3106, c_2946])).
% 4.83/1.88  tff(c_3200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3196, c_3110])).
% 4.83/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.88  
% 4.83/1.88  Inference rules
% 4.83/1.88  ----------------------
% 4.83/1.88  #Ref     : 0
% 4.83/1.88  #Sup     : 676
% 4.83/1.88  #Fact    : 0
% 4.83/1.88  #Define  : 0
% 4.83/1.88  #Split   : 22
% 4.83/1.88  #Chain   : 0
% 4.83/1.88  #Close   : 0
% 4.83/1.88  
% 4.83/1.88  Ordering : KBO
% 4.83/1.88  
% 4.83/1.88  Simplification rules
% 4.83/1.88  ----------------------
% 4.83/1.88  #Subsume      : 71
% 4.83/1.88  #Demod        : 831
% 4.83/1.88  #Tautology    : 408
% 4.83/1.88  #SimpNegUnit  : 19
% 4.83/1.88  #BackRed      : 89
% 4.83/1.88  
% 4.83/1.88  #Partial instantiations: 0
% 4.83/1.88  #Strategies tried      : 1
% 4.83/1.88  
% 4.83/1.88  Timing (in seconds)
% 4.83/1.88  ----------------------
% 4.83/1.88  Preprocessing        : 0.34
% 4.83/1.88  Parsing              : 0.18
% 4.83/1.88  CNF conversion       : 0.02
% 4.83/1.88  Main loop            : 0.74
% 4.83/1.88  Inferencing          : 0.28
% 4.83/1.88  Reduction            : 0.24
% 4.83/1.88  Demodulation         : 0.17
% 4.83/1.88  BG Simplification    : 0.03
% 4.83/1.88  Subsumption          : 0.13
% 4.83/1.88  Abstraction          : 0.03
% 4.83/1.88  MUC search           : 0.00
% 4.83/1.88  Cooper               : 0.00
% 4.83/1.88  Total                : 1.14
% 4.83/1.88  Index Insertion      : 0.00
% 4.83/1.88  Index Deletion       : 0.00
% 4.83/1.88  Index Matching       : 0.00
% 4.83/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
