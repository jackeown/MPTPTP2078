%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:46 EST 2020

% Result     : Theorem 6.19s
% Output     : CNFRefutation 6.54s
% Verified   : 
% Statistics : Number of formulae       :  226 (1173 expanded)
%              Number of leaves         :   37 ( 383 expanded)
%              Depth                    :   13
%              Number of atoms          :  398 (3312 expanded)
%              Number of equality atoms :  153 ( 935 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
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

tff(f_122,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_112,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4438,plain,(
    ! [C_375,A_376,B_377] :
      ( v1_relat_1(C_375)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4455,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_4438])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_72,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_70,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5583,plain,(
    ! [A_482,B_483,C_484] :
      ( k2_relset_1(A_482,B_483,C_484) = k2_relat_1(C_484)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_482,B_483))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5596,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_5583])).

tff(c_5606,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5596])).

tff(c_30,plain,(
    ! [A_10] :
      ( k1_relat_1(k2_funct_1(A_10)) = k2_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [A_9] :
      ( v1_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_133,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_136,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_133])).

tff(c_139,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_136])).

tff(c_246,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_256,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_246])).

tff(c_267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_256])).

tff(c_268,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_284,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_326,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_344,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_326])).

tff(c_764,plain,(
    ! [A_121,B_122,C_123] :
      ( k2_relset_1(A_121,B_122,C_123) = k2_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_774,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_764])).

tff(c_784,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_774])).

tff(c_26,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_269,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_453,plain,(
    ! [A_83] :
      ( k1_relat_1(k2_funct_1(A_83)) = k2_relat_1(A_83)
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_64,plain,(
    ! [A_26] :
      ( v1_funct_2(A_26,k1_relat_1(A_26),k2_relat_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2265,plain,(
    ! [A_220] :
      ( v1_funct_2(k2_funct_1(A_220),k2_relat_1(A_220),k2_relat_1(k2_funct_1(A_220)))
      | ~ v1_funct_1(k2_funct_1(A_220))
      | ~ v1_relat_1(k2_funct_1(A_220))
      | ~ v2_funct_1(A_220)
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_64])).

tff(c_2271,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_784,c_2265])).

tff(c_2281,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_78,c_72,c_269,c_2271])).

tff(c_2282,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2281])).

tff(c_2285,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_2282])).

tff(c_2289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_78,c_2285])).

tff(c_2291,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2281])).

tff(c_20,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_351,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_344,c_20])).

tff(c_353,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_785,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_353])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_682,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_701,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_682])).

tff(c_990,plain,(
    ! [B_143,A_144,C_145] :
      ( k1_xboole_0 = B_143
      | k1_relset_1(A_144,B_143,C_145) = A_144
      | ~ v1_funct_2(C_145,A_144,B_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1006,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_990])).

tff(c_1024,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_701,c_1006])).

tff(c_1025,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_785,c_1024])).

tff(c_28,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_795,plain,(
    ! [A_124] :
      ( m1_subset_1(A_124,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_124),k2_relat_1(A_124))))
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2759,plain,(
    ! [A_246] :
      ( m1_subset_1(k2_funct_1(A_246),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_246)),k1_relat_1(A_246))))
      | ~ v1_funct_1(k2_funct_1(A_246))
      | ~ v1_relat_1(k2_funct_1(A_246))
      | ~ v2_funct_1(A_246)
      | ~ v1_funct_1(A_246)
      | ~ v1_relat_1(A_246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_795])).

tff(c_2786,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_2759])).

tff(c_2807,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_78,c_72,c_2291,c_269,c_2786])).

tff(c_2830,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2807])).

tff(c_2844,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_78,c_72,c_784,c_2830])).

tff(c_2846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_2844])).

tff(c_2847,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_315,plain,(
    ! [A_68,B_69] : m1_subset_1('#skF_1'(A_68,B_69),k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_321,plain,(
    ! [B_5] : m1_subset_1('#skF_1'(k1_xboole_0,B_5),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_315])).

tff(c_2948,plain,(
    ! [B_255] : m1_subset_1('#skF_1'('#skF_4',B_255),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2847,c_321])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2958,plain,(
    ! [B_256] : r1_tarski('#skF_1'('#skF_4',B_256),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2948,c_16])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_289,plain,(
    ! [B_65,A_66] :
      ( B_65 = A_66
      | ~ r1_tarski(B_65,A_66)
      | ~ r1_tarski(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_301,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_289])).

tff(c_2849,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2847,c_301])).

tff(c_2969,plain,(
    ! [B_256] : '#skF_1'('#skF_4',B_256) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2958,c_2849])).

tff(c_2947,plain,(
    ! [B_5] : m1_subset_1('#skF_1'('#skF_4',B_5),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2847,c_321])).

tff(c_2974,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2969,c_2947])).

tff(c_2848,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_2859,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2848])).

tff(c_3106,plain,(
    ! [A_267] :
      ( k1_relat_1(k2_funct_1(A_267)) = k2_relat_1(A_267)
      | ~ v2_funct_1(A_267)
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4362,plain,(
    ! [A_374] :
      ( v1_funct_2(k2_funct_1(A_374),k2_relat_1(A_374),k2_relat_1(k2_funct_1(A_374)))
      | ~ v1_funct_1(k2_funct_1(A_374))
      | ~ v1_relat_1(k2_funct_1(A_374))
      | ~ v2_funct_1(A_374)
      | ~ v1_funct_1(A_374)
      | ~ v1_relat_1(A_374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3106,c_64])).

tff(c_4374,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2859,c_4362])).

tff(c_4378,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_78,c_72,c_269,c_4374])).

tff(c_4379,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4378])).

tff(c_4382,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_4379])).

tff(c_4386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_78,c_4382])).

tff(c_4388,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4378])).

tff(c_22,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) != k1_xboole_0
      | k1_xboole_0 = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2851,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) != '#skF_4'
      | A_8 = '#skF_4'
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2847,c_22])).

tff(c_4396,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4388,c_2851])).

tff(c_4411,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4396])).

tff(c_4414,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4411])).

tff(c_4417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_78,c_72,c_2859,c_4414])).

tff(c_4418,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4396])).

tff(c_2852,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2847,c_14])).

tff(c_3400,plain,(
    ! [A_300,B_301,C_302] :
      ( k2_relset_1(A_300,B_301,C_302) = k2_relat_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3419,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_3400])).

tff(c_3424,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2859,c_70,c_3419])).

tff(c_3427,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3424,c_284])).

tff(c_3433,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2852,c_3427])).

tff(c_4423,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4418,c_3433])).

tff(c_4431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2974,c_4423])).

tff(c_4432,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_4959,plain,(
    ! [A_430,B_431,C_432] :
      ( k2_relset_1(A_430,B_431,C_432) = k2_relat_1(C_432)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4975,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_4959])).

tff(c_4987,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4975])).

tff(c_4433,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_4848,plain,(
    ! [A_416,B_417,C_418] :
      ( k1_relset_1(A_416,B_417,C_418) = k1_relat_1(C_418)
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(A_416,B_417))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4869,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4433,c_4848])).

tff(c_5141,plain,(
    ! [B_444,C_445,A_446] :
      ( k1_xboole_0 = B_444
      | v1_funct_2(C_445,A_446,B_444)
      | k1_relset_1(A_446,B_444,C_445) != A_446
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_446,B_444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5153,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4433,c_5141])).

tff(c_5175,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4869,c_5153])).

tff(c_5176,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4432,c_5175])).

tff(c_5204,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5176])).

tff(c_5207,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5204])).

tff(c_5210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4455,c_78,c_72,c_4987,c_5207])).

tff(c_5211,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5176])).

tff(c_5252,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5211,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5251,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5211,c_5211,c_12])).

tff(c_4437,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4433,c_16])).

tff(c_4480,plain,(
    ! [B_379,A_380] :
      ( B_379 = A_380
      | ~ r1_tarski(B_379,A_380)
      | ~ r1_tarski(A_380,B_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4489,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4')
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4437,c_4480])).

tff(c_4771,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4489])).

tff(c_5289,plain,(
    ~ r1_tarski('#skF_2',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5251,c_4771])).

tff(c_5294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5252,c_5289])).

tff(c_5295,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4489])).

tff(c_5300,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5295,c_4433])).

tff(c_5480,plain,(
    ! [A_470,B_471,C_472] :
      ( k1_relset_1(A_470,B_471,C_472) = k1_relat_1(C_472)
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(A_470,B_471))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5515,plain,(
    ! [C_475] :
      ( k1_relset_1('#skF_3','#skF_2',C_475) = k1_relat_1(C_475)
      | ~ m1_subset_1(C_475,k1_zfmisc_1(k2_funct_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5295,c_5480])).

tff(c_5527,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5300,c_5515])).

tff(c_4462,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4455,c_20])).

tff(c_4464,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4462])).

tff(c_5607,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5606,c_4464])).

tff(c_5502,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_5480])).

tff(c_6043,plain,(
    ! [B_522,A_523,C_524] :
      ( k1_xboole_0 = B_522
      | k1_relset_1(A_523,B_522,C_524) = A_523
      | ~ v1_funct_2(C_524,A_523,B_522)
      | ~ m1_subset_1(C_524,k1_zfmisc_1(k2_zfmisc_1(A_523,B_522))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6062,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_6043])).

tff(c_6080,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5502,c_6062])).

tff(c_6081,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_5607,c_6080])).

tff(c_4463,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4455,c_22])).

tff(c_4473,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4463])).

tff(c_6090,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6081,c_4473])).

tff(c_6320,plain,(
    ! [B_535,C_536,A_537] :
      ( k1_xboole_0 = B_535
      | v1_funct_2(C_536,A_537,B_535)
      | k1_relset_1(A_537,B_535,C_536) != A_537
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_zfmisc_1(A_537,B_535))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6326,plain,(
    ! [C_536] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_536,'#skF_3','#skF_2')
      | k1_relset_1('#skF_3','#skF_2',C_536) != '#skF_3'
      | ~ m1_subset_1(C_536,k1_zfmisc_1(k2_funct_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5295,c_6320])).

tff(c_6458,plain,(
    ! [C_544] :
      ( v1_funct_2(C_544,'#skF_3','#skF_2')
      | k1_relset_1('#skF_3','#skF_2',C_544) != '#skF_3'
      | ~ m1_subset_1(C_544,k1_zfmisc_1(k2_funct_1('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6090,c_6326])).

tff(c_6464,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_5300,c_6458])).

tff(c_6472,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5527,c_6464])).

tff(c_6473,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4432,c_6472])).

tff(c_6477,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6473])).

tff(c_6480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4455,c_78,c_72,c_5606,c_6477])).

tff(c_6481,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4463])).

tff(c_6483,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6481,c_4464])).

tff(c_6482,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4463])).

tff(c_6493,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6481,c_6482])).

tff(c_6771,plain,(
    ! [A_572] :
      ( k2_relat_1(k2_funct_1(A_572)) = k1_relat_1(A_572)
      | ~ v2_funct_1(A_572)
      | ~ v1_funct_1(A_572)
      | ~ v1_relat_1(A_572) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4453,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4433,c_4438])).

tff(c_4471,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4453,c_20])).

tff(c_6552,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6481,c_6481,c_4471])).

tff(c_6553,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6552])).

tff(c_6780,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6771,c_6553])).

tff(c_6787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4455,c_78,c_72,c_6493,c_6780])).

tff(c_6788,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6552])).

tff(c_6789,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6552])).

tff(c_6812,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6788,c_6789])).

tff(c_6813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6483,c_6812])).

tff(c_6814,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4462])).

tff(c_6818,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6814,c_6814,c_14])).

tff(c_7265,plain,(
    ! [A_608,B_609] : m1_subset_1('#skF_1'(A_608,B_609),k1_zfmisc_1(k2_zfmisc_1(A_608,B_609))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_7356,plain,(
    ! [B_616] : m1_subset_1('#skF_1'('#skF_4',B_616),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6818,c_7265])).

tff(c_7370,plain,(
    ! [B_617] : r1_tarski('#skF_1'('#skF_4',B_617),'#skF_4') ),
    inference(resolution,[status(thm)],[c_7356,c_16])).

tff(c_6844,plain,(
    ! [A_575] : r1_tarski('#skF_4',A_575) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6814,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6847,plain,(
    ! [A_575] :
      ( A_575 = '#skF_4'
      | ~ r1_tarski(A_575,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6844,c_2])).

tff(c_7394,plain,(
    ! [B_618] : '#skF_1'('#skF_4',B_618) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7370,c_6847])).

tff(c_50,plain,(
    ! [A_23,B_24] : v1_funct_2('#skF_1'(A_23,B_24),A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_7405,plain,(
    ! [B_618] : v1_funct_2('#skF_4','#skF_4',B_618) ),
    inference(superposition,[status(thm),theory(equality)],[c_7394,c_50])).

tff(c_6815,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4462])).

tff(c_6825,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6814,c_6815])).

tff(c_7547,plain,(
    ! [A_633,B_634,C_635] :
      ( k2_relset_1(A_633,B_634,C_635) = k2_relat_1(C_635)
      | ~ m1_subset_1(C_635,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7566,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_7547])).

tff(c_7572,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6825,c_7566])).

tff(c_7202,plain,(
    ! [A_607] :
      ( k1_relat_1(k2_funct_1(A_607)) = k2_relat_1(A_607)
      | ~ v2_funct_1(A_607)
      | ~ v1_funct_1(A_607)
      | ~ v1_relat_1(A_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6973,plain,(
    ! [A_589] :
      ( k1_relat_1(A_589) != '#skF_4'
      | A_589 = '#skF_4'
      | ~ v1_relat_1(A_589) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6814,c_6814,c_22])).

tff(c_6990,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4453,c_6973])).

tff(c_6996,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6990])).

tff(c_7211,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7202,c_6996])).

tff(c_7218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4455,c_78,c_72,c_6825,c_7211])).

tff(c_7219,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6990])).

tff(c_6949,plain,(
    ! [A_588] :
      ( k2_relat_1(A_588) != '#skF_4'
      | A_588 = '#skF_4'
      | ~ v1_relat_1(A_588) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6814,c_6814,c_20])).

tff(c_6966,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4453,c_6949])).

tff(c_6995,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6966])).

tff(c_7221,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7219,c_6995])).

tff(c_7229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6825,c_7221])).

tff(c_7230,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6966])).

tff(c_7235,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7230,c_4432])).

tff(c_7574,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7572,c_7235])).

tff(c_7581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7405,c_7574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:23:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.19/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.19/2.25  
% 6.19/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.19/2.25  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.19/2.25  
% 6.19/2.25  %Foreground sorts:
% 6.19/2.25  
% 6.19/2.25  
% 6.19/2.25  %Background operators:
% 6.19/2.25  
% 6.19/2.25  
% 6.19/2.25  %Foreground operators:
% 6.19/2.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.19/2.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.19/2.25  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.19/2.25  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.19/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.19/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.19/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.19/2.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.19/2.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.19/2.25  tff('#skF_2', type, '#skF_2': $i).
% 6.19/2.25  tff('#skF_3', type, '#skF_3': $i).
% 6.19/2.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.19/2.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.19/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.19/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.19/2.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.19/2.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.19/2.25  tff('#skF_4', type, '#skF_4': $i).
% 6.19/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.19/2.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.19/2.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.19/2.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.19/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.19/2.25  
% 6.54/2.28  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.54/2.28  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.54/2.28  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.54/2.28  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 6.54/2.28  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.54/2.28  tff(f_122, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 6.54/2.28  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.54/2.28  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.54/2.28  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.54/2.28  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.54/2.28  tff(f_112, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 6.54/2.28  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.54/2.28  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.54/2.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.54/2.28  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.54/2.28  tff(c_4438, plain, (![C_375, A_376, B_377]: (v1_relat_1(C_375) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.54/2.28  tff(c_4455, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_4438])).
% 6.54/2.28  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.54/2.28  tff(c_72, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.54/2.28  tff(c_70, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.54/2.28  tff(c_5583, plain, (![A_482, B_483, C_484]: (k2_relset_1(A_482, B_483, C_484)=k2_relat_1(C_484) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_482, B_483))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.54/2.28  tff(c_5596, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_5583])).
% 6.54/2.28  tff(c_5606, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5596])).
% 6.54/2.28  tff(c_30, plain, (![A_10]: (k1_relat_1(k2_funct_1(A_10))=k2_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.54/2.28  tff(c_24, plain, (![A_9]: (v1_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.54/2.28  tff(c_68, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.54/2.28  tff(c_133, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 6.54/2.28  tff(c_136, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_133])).
% 6.54/2.28  tff(c_139, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_136])).
% 6.54/2.28  tff(c_246, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.54/2.28  tff(c_256, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_246])).
% 6.54/2.28  tff(c_267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_139, c_256])).
% 6.54/2.28  tff(c_268, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_68])).
% 6.54/2.28  tff(c_284, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_268])).
% 6.54/2.28  tff(c_326, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.54/2.28  tff(c_344, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_326])).
% 6.54/2.28  tff(c_764, plain, (![A_121, B_122, C_123]: (k2_relset_1(A_121, B_122, C_123)=k2_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.54/2.28  tff(c_774, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_764])).
% 6.54/2.28  tff(c_784, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_774])).
% 6.54/2.28  tff(c_26, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.54/2.28  tff(c_269, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 6.54/2.28  tff(c_453, plain, (![A_83]: (k1_relat_1(k2_funct_1(A_83))=k2_relat_1(A_83) | ~v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.54/2.28  tff(c_64, plain, (![A_26]: (v1_funct_2(A_26, k1_relat_1(A_26), k2_relat_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.54/2.28  tff(c_2265, plain, (![A_220]: (v1_funct_2(k2_funct_1(A_220), k2_relat_1(A_220), k2_relat_1(k2_funct_1(A_220))) | ~v1_funct_1(k2_funct_1(A_220)) | ~v1_relat_1(k2_funct_1(A_220)) | ~v2_funct_1(A_220) | ~v1_funct_1(A_220) | ~v1_relat_1(A_220))), inference(superposition, [status(thm), theory('equality')], [c_453, c_64])).
% 6.54/2.28  tff(c_2271, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_784, c_2265])).
% 6.54/2.28  tff(c_2281, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_78, c_72, c_269, c_2271])).
% 6.54/2.28  tff(c_2282, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2281])).
% 6.54/2.28  tff(c_2285, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_2282])).
% 6.54/2.28  tff(c_2289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_78, c_2285])).
% 6.54/2.28  tff(c_2291, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2281])).
% 6.54/2.28  tff(c_20, plain, (![A_8]: (k2_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.54/2.28  tff(c_351, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_344, c_20])).
% 6.54/2.28  tff(c_353, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_351])).
% 6.54/2.28  tff(c_785, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_784, c_353])).
% 6.54/2.28  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.54/2.28  tff(c_682, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.54/2.28  tff(c_701, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_682])).
% 6.54/2.28  tff(c_990, plain, (![B_143, A_144, C_145]: (k1_xboole_0=B_143 | k1_relset_1(A_144, B_143, C_145)=A_144 | ~v1_funct_2(C_145, A_144, B_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.54/2.28  tff(c_1006, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_990])).
% 6.54/2.28  tff(c_1024, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_701, c_1006])).
% 6.54/2.28  tff(c_1025, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_785, c_1024])).
% 6.54/2.28  tff(c_28, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.54/2.28  tff(c_795, plain, (![A_124]: (m1_subset_1(A_124, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_124), k2_relat_1(A_124)))) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.54/2.28  tff(c_2759, plain, (![A_246]: (m1_subset_1(k2_funct_1(A_246), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_246)), k1_relat_1(A_246)))) | ~v1_funct_1(k2_funct_1(A_246)) | ~v1_relat_1(k2_funct_1(A_246)) | ~v2_funct_1(A_246) | ~v1_funct_1(A_246) | ~v1_relat_1(A_246))), inference(superposition, [status(thm), theory('equality')], [c_28, c_795])).
% 6.54/2.28  tff(c_2786, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1025, c_2759])).
% 6.54/2.28  tff(c_2807, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_78, c_72, c_2291, c_269, c_2786])).
% 6.54/2.28  tff(c_2830, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2807])).
% 6.54/2.28  tff(c_2844, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_78, c_72, c_784, c_2830])).
% 6.54/2.28  tff(c_2846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_2844])).
% 6.54/2.28  tff(c_2847, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_351])).
% 6.54/2.28  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.54/2.28  tff(c_315, plain, (![A_68, B_69]: (m1_subset_1('#skF_1'(A_68, B_69), k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.54/2.28  tff(c_321, plain, (![B_5]: (m1_subset_1('#skF_1'(k1_xboole_0, B_5), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_315])).
% 6.54/2.28  tff(c_2948, plain, (![B_255]: (m1_subset_1('#skF_1'('#skF_4', B_255), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2847, c_321])).
% 6.54/2.28  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.54/2.28  tff(c_2958, plain, (![B_256]: (r1_tarski('#skF_1'('#skF_4', B_256), '#skF_4'))), inference(resolution, [status(thm)], [c_2948, c_16])).
% 6.54/2.28  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.54/2.28  tff(c_289, plain, (![B_65, A_66]: (B_65=A_66 | ~r1_tarski(B_65, A_66) | ~r1_tarski(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.54/2.28  tff(c_301, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_289])).
% 6.54/2.28  tff(c_2849, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2847, c_301])).
% 6.54/2.28  tff(c_2969, plain, (![B_256]: ('#skF_1'('#skF_4', B_256)='#skF_4')), inference(resolution, [status(thm)], [c_2958, c_2849])).
% 6.54/2.28  tff(c_2947, plain, (![B_5]: (m1_subset_1('#skF_1'('#skF_4', B_5), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2847, c_321])).
% 6.54/2.28  tff(c_2974, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2969, c_2947])).
% 6.54/2.28  tff(c_2848, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_351])).
% 6.54/2.28  tff(c_2859, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2848])).
% 6.54/2.28  tff(c_3106, plain, (![A_267]: (k1_relat_1(k2_funct_1(A_267))=k2_relat_1(A_267) | ~v2_funct_1(A_267) | ~v1_funct_1(A_267) | ~v1_relat_1(A_267))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.54/2.28  tff(c_4362, plain, (![A_374]: (v1_funct_2(k2_funct_1(A_374), k2_relat_1(A_374), k2_relat_1(k2_funct_1(A_374))) | ~v1_funct_1(k2_funct_1(A_374)) | ~v1_relat_1(k2_funct_1(A_374)) | ~v2_funct_1(A_374) | ~v1_funct_1(A_374) | ~v1_relat_1(A_374))), inference(superposition, [status(thm), theory('equality')], [c_3106, c_64])).
% 6.54/2.28  tff(c_4374, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2859, c_4362])).
% 6.54/2.28  tff(c_4378, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_78, c_72, c_269, c_4374])).
% 6.54/2.28  tff(c_4379, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4378])).
% 6.54/2.28  tff(c_4382, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_4379])).
% 6.54/2.28  tff(c_4386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_78, c_4382])).
% 6.54/2.28  tff(c_4388, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4378])).
% 6.54/2.28  tff(c_22, plain, (![A_8]: (k1_relat_1(A_8)!=k1_xboole_0 | k1_xboole_0=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.54/2.28  tff(c_2851, plain, (![A_8]: (k1_relat_1(A_8)!='#skF_4' | A_8='#skF_4' | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2847, c_22])).
% 6.54/2.28  tff(c_4396, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_4388, c_2851])).
% 6.54/2.28  tff(c_4411, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_4396])).
% 6.54/2.28  tff(c_4414, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_4411])).
% 6.54/2.28  tff(c_4417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_78, c_72, c_2859, c_4414])).
% 6.54/2.28  tff(c_4418, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_4396])).
% 6.54/2.28  tff(c_2852, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2847, c_14])).
% 6.54/2.28  tff(c_3400, plain, (![A_300, B_301, C_302]: (k2_relset_1(A_300, B_301, C_302)=k2_relat_1(C_302) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.54/2.28  tff(c_3419, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_3400])).
% 6.54/2.28  tff(c_3424, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2859, c_70, c_3419])).
% 6.54/2.28  tff(c_3427, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3424, c_284])).
% 6.54/2.28  tff(c_3433, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2852, c_3427])).
% 6.54/2.28  tff(c_4423, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4418, c_3433])).
% 6.54/2.28  tff(c_4431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2974, c_4423])).
% 6.54/2.28  tff(c_4432, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_268])).
% 6.54/2.28  tff(c_4959, plain, (![A_430, B_431, C_432]: (k2_relset_1(A_430, B_431, C_432)=k2_relat_1(C_432) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.54/2.28  tff(c_4975, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_4959])).
% 6.54/2.28  tff(c_4987, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4975])).
% 6.54/2.28  tff(c_4433, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_268])).
% 6.54/2.28  tff(c_4848, plain, (![A_416, B_417, C_418]: (k1_relset_1(A_416, B_417, C_418)=k1_relat_1(C_418) | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(A_416, B_417))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.54/2.28  tff(c_4869, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4433, c_4848])).
% 6.54/2.28  tff(c_5141, plain, (![B_444, C_445, A_446]: (k1_xboole_0=B_444 | v1_funct_2(C_445, A_446, B_444) | k1_relset_1(A_446, B_444, C_445)!=A_446 | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_446, B_444))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.54/2.28  tff(c_5153, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_4433, c_5141])).
% 6.54/2.28  tff(c_5175, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4869, c_5153])).
% 6.54/2.28  tff(c_5176, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4432, c_5175])).
% 6.54/2.28  tff(c_5204, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_5176])).
% 6.54/2.28  tff(c_5207, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_5204])).
% 6.54/2.28  tff(c_5210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4455, c_78, c_72, c_4987, c_5207])).
% 6.54/2.28  tff(c_5211, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5176])).
% 6.54/2.28  tff(c_5252, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5211, c_8])).
% 6.54/2.28  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.54/2.28  tff(c_5251, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5211, c_5211, c_12])).
% 6.54/2.28  tff(c_4437, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_4433, c_16])).
% 6.54/2.28  tff(c_4480, plain, (![B_379, A_380]: (B_379=A_380 | ~r1_tarski(B_379, A_380) | ~r1_tarski(A_380, B_379))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.54/2.28  tff(c_4489, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4') | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4437, c_4480])).
% 6.54/2.28  tff(c_4771, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4489])).
% 6.54/2.28  tff(c_5289, plain, (~r1_tarski('#skF_2', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5251, c_4771])).
% 6.54/2.28  tff(c_5294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5252, c_5289])).
% 6.54/2.28  tff(c_5295, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_4489])).
% 6.54/2.28  tff(c_5300, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5295, c_4433])).
% 6.54/2.28  tff(c_5480, plain, (![A_470, B_471, C_472]: (k1_relset_1(A_470, B_471, C_472)=k1_relat_1(C_472) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(A_470, B_471))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.54/2.28  tff(c_5515, plain, (![C_475]: (k1_relset_1('#skF_3', '#skF_2', C_475)=k1_relat_1(C_475) | ~m1_subset_1(C_475, k1_zfmisc_1(k2_funct_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_5295, c_5480])).
% 6.54/2.28  tff(c_5527, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5300, c_5515])).
% 6.54/2.28  tff(c_4462, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4455, c_20])).
% 6.54/2.28  tff(c_4464, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4462])).
% 6.54/2.28  tff(c_5607, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5606, c_4464])).
% 6.54/2.28  tff(c_5502, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_5480])).
% 6.54/2.28  tff(c_6043, plain, (![B_522, A_523, C_524]: (k1_xboole_0=B_522 | k1_relset_1(A_523, B_522, C_524)=A_523 | ~v1_funct_2(C_524, A_523, B_522) | ~m1_subset_1(C_524, k1_zfmisc_1(k2_zfmisc_1(A_523, B_522))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.54/2.28  tff(c_6062, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_6043])).
% 6.54/2.28  tff(c_6080, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5502, c_6062])).
% 6.54/2.28  tff(c_6081, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_5607, c_6080])).
% 6.54/2.28  tff(c_4463, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4455, c_22])).
% 6.54/2.28  tff(c_4473, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4463])).
% 6.54/2.28  tff(c_6090, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6081, c_4473])).
% 6.54/2.28  tff(c_6320, plain, (![B_535, C_536, A_537]: (k1_xboole_0=B_535 | v1_funct_2(C_536, A_537, B_535) | k1_relset_1(A_537, B_535, C_536)!=A_537 | ~m1_subset_1(C_536, k1_zfmisc_1(k2_zfmisc_1(A_537, B_535))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.54/2.28  tff(c_6326, plain, (![C_536]: (k1_xboole_0='#skF_2' | v1_funct_2(C_536, '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', C_536)!='#skF_3' | ~m1_subset_1(C_536, k1_zfmisc_1(k2_funct_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_5295, c_6320])).
% 6.54/2.28  tff(c_6458, plain, (![C_544]: (v1_funct_2(C_544, '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', C_544)!='#skF_3' | ~m1_subset_1(C_544, k1_zfmisc_1(k2_funct_1('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_6090, c_6326])).
% 6.54/2.28  tff(c_6464, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_5300, c_6458])).
% 6.54/2.28  tff(c_6472, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5527, c_6464])).
% 6.54/2.28  tff(c_6473, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4432, c_6472])).
% 6.54/2.28  tff(c_6477, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_6473])).
% 6.54/2.28  tff(c_6480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4455, c_78, c_72, c_5606, c_6477])).
% 6.54/2.28  tff(c_6481, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4463])).
% 6.54/2.28  tff(c_6483, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6481, c_4464])).
% 6.54/2.28  tff(c_6482, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4463])).
% 6.54/2.28  tff(c_6493, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6481, c_6482])).
% 6.54/2.28  tff(c_6771, plain, (![A_572]: (k2_relat_1(k2_funct_1(A_572))=k1_relat_1(A_572) | ~v2_funct_1(A_572) | ~v1_funct_1(A_572) | ~v1_relat_1(A_572))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.54/2.28  tff(c_4453, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4433, c_4438])).
% 6.54/2.28  tff(c_4471, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0 | k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_4453, c_20])).
% 6.54/2.28  tff(c_6552, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6481, c_6481, c_4471])).
% 6.54/2.28  tff(c_6553, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_6552])).
% 6.54/2.28  tff(c_6780, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6771, c_6553])).
% 6.54/2.28  tff(c_6787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4455, c_78, c_72, c_6493, c_6780])).
% 6.54/2.28  tff(c_6788, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_6552])).
% 6.54/2.28  tff(c_6789, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_6552])).
% 6.54/2.28  tff(c_6812, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6788, c_6789])).
% 6.54/2.28  tff(c_6813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6483, c_6812])).
% 6.54/2.28  tff(c_6814, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4462])).
% 6.54/2.28  tff(c_6818, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6814, c_6814, c_14])).
% 6.54/2.28  tff(c_7265, plain, (![A_608, B_609]: (m1_subset_1('#skF_1'(A_608, B_609), k1_zfmisc_1(k2_zfmisc_1(A_608, B_609))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.54/2.28  tff(c_7356, plain, (![B_616]: (m1_subset_1('#skF_1'('#skF_4', B_616), k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6818, c_7265])).
% 6.54/2.28  tff(c_7370, plain, (![B_617]: (r1_tarski('#skF_1'('#skF_4', B_617), '#skF_4'))), inference(resolution, [status(thm)], [c_7356, c_16])).
% 6.54/2.28  tff(c_6844, plain, (![A_575]: (r1_tarski('#skF_4', A_575))), inference(demodulation, [status(thm), theory('equality')], [c_6814, c_8])).
% 6.54/2.28  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.54/2.28  tff(c_6847, plain, (![A_575]: (A_575='#skF_4' | ~r1_tarski(A_575, '#skF_4'))), inference(resolution, [status(thm)], [c_6844, c_2])).
% 6.54/2.28  tff(c_7394, plain, (![B_618]: ('#skF_1'('#skF_4', B_618)='#skF_4')), inference(resolution, [status(thm)], [c_7370, c_6847])).
% 6.54/2.28  tff(c_50, plain, (![A_23, B_24]: (v1_funct_2('#skF_1'(A_23, B_24), A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.54/2.28  tff(c_7405, plain, (![B_618]: (v1_funct_2('#skF_4', '#skF_4', B_618))), inference(superposition, [status(thm), theory('equality')], [c_7394, c_50])).
% 6.54/2.28  tff(c_6815, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4462])).
% 6.54/2.28  tff(c_6825, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6814, c_6815])).
% 6.54/2.28  tff(c_7547, plain, (![A_633, B_634, C_635]: (k2_relset_1(A_633, B_634, C_635)=k2_relat_1(C_635) | ~m1_subset_1(C_635, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.54/2.28  tff(c_7566, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_7547])).
% 6.54/2.28  tff(c_7572, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6825, c_7566])).
% 6.54/2.28  tff(c_7202, plain, (![A_607]: (k1_relat_1(k2_funct_1(A_607))=k2_relat_1(A_607) | ~v2_funct_1(A_607) | ~v1_funct_1(A_607) | ~v1_relat_1(A_607))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.54/2.28  tff(c_6973, plain, (![A_589]: (k1_relat_1(A_589)!='#skF_4' | A_589='#skF_4' | ~v1_relat_1(A_589))), inference(demodulation, [status(thm), theory('equality')], [c_6814, c_6814, c_22])).
% 6.54/2.28  tff(c_6990, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_4453, c_6973])).
% 6.54/2.28  tff(c_6996, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_6990])).
% 6.54/2.28  tff(c_7211, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7202, c_6996])).
% 6.54/2.28  tff(c_7218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4455, c_78, c_72, c_6825, c_7211])).
% 6.54/2.28  tff(c_7219, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_6990])).
% 6.54/2.28  tff(c_6949, plain, (![A_588]: (k2_relat_1(A_588)!='#skF_4' | A_588='#skF_4' | ~v1_relat_1(A_588))), inference(demodulation, [status(thm), theory('equality')], [c_6814, c_6814, c_20])).
% 6.54/2.28  tff(c_6966, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_4453, c_6949])).
% 6.54/2.28  tff(c_6995, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_6966])).
% 6.54/2.28  tff(c_7221, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7219, c_6995])).
% 6.54/2.28  tff(c_7229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6825, c_7221])).
% 6.54/2.28  tff(c_7230, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_6966])).
% 6.54/2.28  tff(c_7235, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7230, c_4432])).
% 6.54/2.28  tff(c_7574, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7572, c_7235])).
% 6.54/2.28  tff(c_7581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7405, c_7574])).
% 6.54/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.54/2.28  
% 6.54/2.28  Inference rules
% 6.54/2.28  ----------------------
% 6.54/2.28  #Ref     : 0
% 6.54/2.28  #Sup     : 1635
% 6.54/2.28  #Fact    : 0
% 6.54/2.28  #Define  : 0
% 6.54/2.28  #Split   : 28
% 6.54/2.28  #Chain   : 0
% 6.54/2.28  #Close   : 0
% 6.54/2.28  
% 6.54/2.28  Ordering : KBO
% 6.54/2.28  
% 6.54/2.28  Simplification rules
% 6.54/2.28  ----------------------
% 6.54/2.28  #Subsume      : 138
% 6.54/2.28  #Demod        : 1679
% 6.54/2.28  #Tautology    : 1056
% 6.54/2.28  #SimpNegUnit  : 23
% 6.54/2.28  #BackRed      : 146
% 6.54/2.28  
% 6.54/2.28  #Partial instantiations: 0
% 6.54/2.28  #Strategies tried      : 1
% 6.54/2.28  
% 6.54/2.28  Timing (in seconds)
% 6.54/2.28  ----------------------
% 6.54/2.28  Preprocessing        : 0.34
% 6.54/2.28  Parsing              : 0.18
% 6.54/2.28  CNF conversion       : 0.02
% 6.54/2.28  Main loop            : 1.16
% 6.54/2.28  Inferencing          : 0.41
% 6.54/2.28  Reduction            : 0.42
% 6.54/2.28  Demodulation         : 0.31
% 6.54/2.28  BG Simplification    : 0.04
% 6.54/2.28  Subsumption          : 0.19
% 6.54/2.28  Abstraction          : 0.05
% 6.54/2.28  MUC search           : 0.00
% 6.54/2.28  Cooper               : 0.00
% 6.54/2.28  Total                : 1.56
% 6.54/2.28  Index Insertion      : 0.00
% 6.54/2.28  Index Deletion       : 0.00
% 6.54/2.28  Index Matching       : 0.00
% 6.54/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
