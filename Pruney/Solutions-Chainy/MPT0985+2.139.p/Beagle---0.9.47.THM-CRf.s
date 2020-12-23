%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:49 EST 2020

% Result     : Theorem 5.79s
% Output     : CNFRefutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 734 expanded)
%              Number of leaves         :   41 ( 252 expanded)
%              Depth                    :   14
%              Number of atoms          :  334 (1982 expanded)
%              Number of equality atoms :   80 ( 355 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,A)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(k2_zfmisc_1(A_5,B_6))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3860,plain,(
    ! [B_358,A_359] :
      ( v1_xboole_0(B_358)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(A_359))
      | ~ v1_xboole_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3868,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_3860])).

tff(c_3869,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3868])).

tff(c_3876,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_3869])).

tff(c_16,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3887,plain,(
    ! [B_360,A_361] :
      ( v1_relat_1(B_360)
      | ~ m1_subset_1(B_360,k1_zfmisc_1(A_361))
      | ~ v1_relat_1(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3893,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_3887])).

tff(c_3899,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3893])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4316,plain,(
    ! [A_383,B_384,C_385] :
      ( k2_relset_1(A_383,B_384,C_385) = k2_relat_1(C_385)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4343,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_4316])).

tff(c_4347,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4343])).

tff(c_28,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_234,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_237,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_234])).

tff(c_240,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_237])).

tff(c_24,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_183,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_186,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_183])).

tff(c_189,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_186])).

tff(c_176,plain,(
    ! [A_46] :
      ( v1_funct_1(k2_funct_1(A_46))
      | ~ v1_funct_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_137,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_179,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_137])).

tff(c_182,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_179])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_182])).

tff(c_193,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_xboole_0(k2_zfmisc_1(A_3,B_4))
      | ~ v1_xboole_0(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_241,plain,(
    ! [B_56,A_57] :
      ( v1_xboole_0(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_245,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_241])).

tff(c_246,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_254,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_246])).

tff(c_192,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_194,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_607,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_relset_1(A_74,B_75,C_76) = k2_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_631,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_607])).

tff(c_634,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_631])).

tff(c_543,plain,(
    ! [A_71] :
      ( k1_relat_1(k2_funct_1(A_71)) = k2_relat_1(A_71)
      | ~ v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_56,plain,(
    ! [A_27] :
      ( v1_funct_2(A_27,k1_relat_1(A_27),k2_relat_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1798,plain,(
    ! [A_188] :
      ( v1_funct_2(k2_funct_1(A_188),k2_relat_1(A_188),k2_relat_1(k2_funct_1(A_188)))
      | ~ v1_funct_1(k2_funct_1(A_188))
      | ~ v1_relat_1(k2_funct_1(A_188))
      | ~ v2_funct_1(A_188)
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_56])).

tff(c_1801,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_1798])).

tff(c_1812,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_76,c_70,c_193,c_1801])).

tff(c_1815,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1812])).

tff(c_1818,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1815])).

tff(c_1822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_76,c_1818])).

tff(c_1824,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1812])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_635,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_661,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_635])).

tff(c_1323,plain,(
    ! [B_148,A_149,C_150] :
      ( k1_xboole_0 = B_148
      | k1_relset_1(A_149,B_148,C_150) = A_149
      | ~ v1_funct_2(C_150,A_149,B_148)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1353,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1323])).

tff(c_1362,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_661,c_1353])).

tff(c_1363,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1362])).

tff(c_26,plain,(
    ! [A_16] :
      ( k2_relat_1(k2_funct_1(A_16)) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_567,plain,(
    ! [A_73] :
      ( m1_subset_1(A_73,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_73),k2_relat_1(A_73))))
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2057,plain,(
    ! [A_208] :
      ( m1_subset_1(k2_funct_1(A_208),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_208)),k1_relat_1(A_208))))
      | ~ v1_funct_1(k2_funct_1(A_208))
      | ~ v1_relat_1(k2_funct_1(A_208))
      | ~ v2_funct_1(A_208)
      | ~ v1_funct_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_567])).

tff(c_2078,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1363,c_2057])).

tff(c_2097,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_76,c_70,c_1824,c_193,c_2078])).

tff(c_2120,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2097])).

tff(c_2133,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_76,c_70,c_634,c_2120])).

tff(c_2135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_2133])).

tff(c_2136,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1362])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2181,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_2])).

tff(c_2184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_2181])).

tff(c_2185,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2196,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2185,c_4])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2212,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2196,c_6])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2214,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2196,c_2196,c_20])).

tff(c_98,plain,(
    ! [A_35,B_36] :
      ( v1_xboole_0(k2_zfmisc_1(A_35,B_36))
      | ~ v1_xboole_0(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_102,plain,(
    ! [A_35,B_36] :
      ( k2_zfmisc_1(A_35,B_36) = k1_xboole_0
      | ~ v1_xboole_0(B_36) ) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_2195,plain,(
    ! [A_35] : k2_zfmisc_1(A_35,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2185,c_102])).

tff(c_2248,plain,(
    ! [A_35] : k2_zfmisc_1(A_35,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2196,c_2195])).

tff(c_3232,plain,(
    ! [B_297,A_298] :
      ( m1_subset_1(B_297,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_297),A_298)))
      | ~ r1_tarski(k2_relat_1(B_297),A_298)
      | ~ v1_funct_1(B_297)
      | ~ v1_relat_1(B_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3271,plain,(
    ! [B_299] :
      ( m1_subset_1(B_299,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(k2_relat_1(B_299),'#skF_3')
      | ~ v1_funct_1(B_299)
      | ~ v1_relat_1(B_299) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2248,c_3232])).

tff(c_3754,plain,(
    ! [A_352] :
      ( m1_subset_1(k2_funct_1(A_352),k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(k1_relat_1(A_352),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(A_352))
      | ~ v1_relat_1(k2_funct_1(A_352))
      | ~ v2_funct_1(A_352)
      | ~ v1_funct_1(A_352)
      | ~ v1_relat_1(A_352) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_3271])).

tff(c_103,plain,(
    ! [A_37,B_38] :
      ( v1_xboole_0(k2_zfmisc_1(A_37,B_38))
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_107,plain,(
    ! [A_37,B_38] :
      ( k2_zfmisc_1(A_37,B_38) = k1_xboole_0
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_103,c_4])).

tff(c_2194,plain,(
    ! [B_38] : k2_zfmisc_1('#skF_3',B_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2185,c_107])).

tff(c_2305,plain,(
    ! [B_38] : k2_zfmisc_1('#skF_3',B_38) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2196,c_2194])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2215,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2196,c_2196,c_18])).

tff(c_2186,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_2206,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2186,c_4])).

tff(c_2286,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2196,c_2206])).

tff(c_2288,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2286,c_72])).

tff(c_2693,plain,(
    ! [A_233,B_234,C_235] :
      ( k2_relset_1(A_233,B_234,C_235) = k2_relat_1(C_235)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2814,plain,(
    ! [C_253] :
      ( k2_relset_1('#skF_1','#skF_2',C_253) = k2_relat_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2286,c_2693])).

tff(c_2817,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2288,c_2814])).

tff(c_2819,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2215,c_68,c_2817])).

tff(c_2824,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_194])).

tff(c_2829,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2305,c_2824])).

tff(c_3775,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3754,c_2829])).

tff(c_3801,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_76,c_70,c_193,c_2212,c_2214,c_3775])).

tff(c_3814,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_3801])).

tff(c_3818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_76,c_3814])).

tff(c_3819,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_3820,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_4285,plain,(
    ! [A_380,B_381,C_382] :
      ( k1_relset_1(A_380,B_381,C_382) = k1_relat_1(C_382)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_380,B_381))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4314,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3820,c_4285])).

tff(c_4798,plain,(
    ! [B_418,C_419,A_420] :
      ( k1_xboole_0 = B_418
      | v1_funct_2(C_419,A_420,B_418)
      | k1_relset_1(A_420,B_418,C_419) != A_420
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_420,B_418))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4819,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_3820,c_4798])).

tff(c_4832,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4314,c_4819])).

tff(c_4833,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3819,c_4832])).

tff(c_4838,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4833])).

tff(c_4841,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_4838])).

tff(c_4844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3899,c_76,c_70,c_4347,c_4841])).

tff(c_4845,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4833])).

tff(c_4880,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4845,c_2])).

tff(c_4883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3876,c_4880])).

tff(c_4884,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3868])).

tff(c_4895,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4884,c_4])).

tff(c_30,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4905,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4895,c_30])).

tff(c_4901,plain,(
    ! [A_2] : r1_tarski('#skF_3',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4895,c_6])).

tff(c_4904,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4895,c_4895,c_18])).

tff(c_4903,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4895,c_4895,c_20])).

tff(c_6100,plain,(
    ! [B_491,A_492] :
      ( v1_funct_2(B_491,k1_relat_1(B_491),A_492)
      | ~ r1_tarski(k2_relat_1(B_491),A_492)
      | ~ v1_funct_1(B_491)
      | ~ v1_relat_1(B_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6106,plain,(
    ! [A_492] :
      ( v1_funct_2('#skF_3','#skF_3',A_492)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_492)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4903,c_6100])).

tff(c_6108,plain,(
    ! [A_492] : v1_funct_2('#skF_3','#skF_3',A_492) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4905,c_76,c_4901,c_4904,c_6106])).

tff(c_4885,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3868])).

tff(c_4938,plain,(
    ! [A_425] :
      ( A_425 = '#skF_3'
      | ~ v1_xboole_0(A_425) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4895,c_4])).

tff(c_4951,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4885,c_4938])).

tff(c_5018,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4951,c_72])).

tff(c_5967,plain,(
    ! [A_477,B_478,C_479] :
      ( k2_relset_1(A_477,B_478,C_479) = k2_relat_1(C_479)
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(A_477,B_478))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6031,plain,(
    ! [C_487] :
      ( k2_relset_1('#skF_1','#skF_2',C_487) = k2_relat_1(C_487)
      | ~ m1_subset_1(C_487,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4951,c_5967])).

tff(c_6034,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5018,c_6031])).

tff(c_6036,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4904,c_6034])).

tff(c_5399,plain,(
    ! [A_447,B_448,C_449] :
      ( k2_relset_1(A_447,B_448,C_449) = k2_relat_1(C_449)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5429,plain,(
    ! [C_450] :
      ( k2_relset_1('#skF_1','#skF_2',C_450) = k2_relat_1(C_450)
      | ~ m1_subset_1(C_450,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4951,c_5399])).

tff(c_5432,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5018,c_5429])).

tff(c_5434,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4904,c_68,c_5432])).

tff(c_3867,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3820,c_3860])).

tff(c_5070,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3867])).

tff(c_5089,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_5070])).

tff(c_5437,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5434,c_5089])).

tff(c_5446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4884,c_5437])).

tff(c_5447,plain,(
    v1_xboole_0(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3867])).

tff(c_4900,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4895,c_4])).

tff(c_5458,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5447,c_4900])).

tff(c_5462,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5458,c_3819])).

tff(c_6043,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6036,c_5462])).

tff(c_6112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6108,c_6043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 21:03:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.79/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.17  
% 5.79/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.17  %$ v1_funct_2 > v5_relat_1 > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.79/2.17  
% 5.79/2.17  %Foreground sorts:
% 5.79/2.17  
% 5.79/2.17  
% 5.79/2.17  %Background operators:
% 5.79/2.17  
% 5.79/2.17  
% 5.79/2.17  %Foreground operators:
% 5.79/2.17  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.79/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.79/2.17  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.79/2.17  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.79/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.79/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.79/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.79/2.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.79/2.17  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 5.79/2.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.79/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.79/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.79/2.17  tff('#skF_1', type, '#skF_1': $i).
% 5.79/2.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.79/2.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.79/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.79/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.79/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.79/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.79/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.79/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.79/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.79/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.79/2.17  
% 5.79/2.20  tff(f_40, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 5.79/2.20  tff(f_150, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 5.79/2.20  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.79/2.20  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.79/2.20  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.79/2.20  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.79/2.20  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.79/2.20  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.79/2.20  tff(f_36, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 5.79/2.20  tff(f_121, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 5.79/2.20  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.79/2.20  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.79/2.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.79/2.20  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.79/2.20  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.79/2.20  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.79/2.20  tff(f_133, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.79/2.20  tff(f_85, axiom, (![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 5.79/2.20  tff(c_10, plain, (![A_5, B_6]: (v1_xboole_0(k2_zfmisc_1(A_5, B_6)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.79/2.20  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.79/2.20  tff(c_3860, plain, (![B_358, A_359]: (v1_xboole_0(B_358) | ~m1_subset_1(B_358, k1_zfmisc_1(A_359)) | ~v1_xboole_0(A_359))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.79/2.20  tff(c_3868, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_3860])).
% 5.79/2.20  tff(c_3869, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3868])).
% 5.79/2.20  tff(c_3876, plain, (~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_3869])).
% 5.79/2.20  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.79/2.20  tff(c_3887, plain, (![B_360, A_361]: (v1_relat_1(B_360) | ~m1_subset_1(B_360, k1_zfmisc_1(A_361)) | ~v1_relat_1(A_361))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.79/2.20  tff(c_3893, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_3887])).
% 5.79/2.20  tff(c_3899, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3893])).
% 5.79/2.20  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.79/2.20  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.79/2.20  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.79/2.20  tff(c_4316, plain, (![A_383, B_384, C_385]: (k2_relset_1(A_383, B_384, C_385)=k2_relat_1(C_385) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.79/2.20  tff(c_4343, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_4316])).
% 5.79/2.20  tff(c_4347, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4343])).
% 5.79/2.20  tff(c_28, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.79/2.20  tff(c_234, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.79/2.20  tff(c_237, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_234])).
% 5.79/2.20  tff(c_240, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_237])).
% 5.79/2.20  tff(c_24, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.79/2.20  tff(c_183, plain, (![B_47, A_48]: (v1_relat_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.79/2.20  tff(c_186, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_183])).
% 5.79/2.20  tff(c_189, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_186])).
% 5.79/2.20  tff(c_176, plain, (![A_46]: (v1_funct_1(k2_funct_1(A_46)) | ~v1_funct_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.79/2.20  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.79/2.20  tff(c_137, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 5.79/2.20  tff(c_179, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_176, c_137])).
% 5.79/2.20  tff(c_182, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_179])).
% 5.79/2.20  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_182])).
% 5.79/2.20  tff(c_193, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 5.79/2.20  tff(c_8, plain, (![A_3, B_4]: (v1_xboole_0(k2_zfmisc_1(A_3, B_4)) | ~v1_xboole_0(B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.79/2.20  tff(c_241, plain, (![B_56, A_57]: (v1_xboole_0(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.79/2.20  tff(c_245, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_241])).
% 5.79/2.20  tff(c_246, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_245])).
% 5.79/2.20  tff(c_254, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_246])).
% 5.79/2.20  tff(c_192, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_66])).
% 5.79/2.20  tff(c_194, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_192])).
% 5.79/2.20  tff(c_607, plain, (![A_74, B_75, C_76]: (k2_relset_1(A_74, B_75, C_76)=k2_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.79/2.20  tff(c_631, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_607])).
% 5.79/2.20  tff(c_634, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_631])).
% 5.79/2.20  tff(c_543, plain, (![A_71]: (k1_relat_1(k2_funct_1(A_71))=k2_relat_1(A_71) | ~v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.79/2.20  tff(c_56, plain, (![A_27]: (v1_funct_2(A_27, k1_relat_1(A_27), k2_relat_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.79/2.20  tff(c_1798, plain, (![A_188]: (v1_funct_2(k2_funct_1(A_188), k2_relat_1(A_188), k2_relat_1(k2_funct_1(A_188))) | ~v1_funct_1(k2_funct_1(A_188)) | ~v1_relat_1(k2_funct_1(A_188)) | ~v2_funct_1(A_188) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188))), inference(superposition, [status(thm), theory('equality')], [c_543, c_56])).
% 5.79/2.20  tff(c_1801, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_634, c_1798])).
% 5.79/2.20  tff(c_1812, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_76, c_70, c_193, c_1801])).
% 5.79/2.20  tff(c_1815, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1812])).
% 5.79/2.20  tff(c_1818, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1815])).
% 5.79/2.20  tff(c_1822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_76, c_1818])).
% 5.79/2.20  tff(c_1824, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1812])).
% 5.79/2.20  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.79/2.20  tff(c_635, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.79/2.20  tff(c_661, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_635])).
% 5.79/2.20  tff(c_1323, plain, (![B_148, A_149, C_150]: (k1_xboole_0=B_148 | k1_relset_1(A_149, B_148, C_150)=A_149 | ~v1_funct_2(C_150, A_149, B_148) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.79/2.20  tff(c_1353, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_1323])).
% 5.79/2.20  tff(c_1362, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_661, c_1353])).
% 5.79/2.20  tff(c_1363, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1362])).
% 5.79/2.20  tff(c_26, plain, (![A_16]: (k2_relat_1(k2_funct_1(A_16))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.79/2.20  tff(c_567, plain, (![A_73]: (m1_subset_1(A_73, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_73), k2_relat_1(A_73)))) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.79/2.20  tff(c_2057, plain, (![A_208]: (m1_subset_1(k2_funct_1(A_208), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_208)), k1_relat_1(A_208)))) | ~v1_funct_1(k2_funct_1(A_208)) | ~v1_relat_1(k2_funct_1(A_208)) | ~v2_funct_1(A_208) | ~v1_funct_1(A_208) | ~v1_relat_1(A_208))), inference(superposition, [status(thm), theory('equality')], [c_26, c_567])).
% 5.79/2.20  tff(c_2078, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1363, c_2057])).
% 5.79/2.20  tff(c_2097, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_76, c_70, c_1824, c_193, c_2078])).
% 5.79/2.20  tff(c_2120, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_2097])).
% 5.79/2.20  tff(c_2133, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_76, c_70, c_634, c_2120])).
% 5.79/2.20  tff(c_2135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_2133])).
% 5.79/2.20  tff(c_2136, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1362])).
% 5.79/2.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.79/2.20  tff(c_2181, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2136, c_2])).
% 5.79/2.20  tff(c_2184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_2181])).
% 5.79/2.20  tff(c_2185, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_245])).
% 5.79/2.20  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.79/2.20  tff(c_2196, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2185, c_4])).
% 5.79/2.20  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.79/2.20  tff(c_2212, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_2196, c_6])).
% 5.79/2.20  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.79/2.20  tff(c_2214, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2196, c_2196, c_20])).
% 5.79/2.20  tff(c_98, plain, (![A_35, B_36]: (v1_xboole_0(k2_zfmisc_1(A_35, B_36)) | ~v1_xboole_0(B_36))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.79/2.20  tff(c_102, plain, (![A_35, B_36]: (k2_zfmisc_1(A_35, B_36)=k1_xboole_0 | ~v1_xboole_0(B_36))), inference(resolution, [status(thm)], [c_98, c_4])).
% 5.79/2.20  tff(c_2195, plain, (![A_35]: (k2_zfmisc_1(A_35, '#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2185, c_102])).
% 5.79/2.20  tff(c_2248, plain, (![A_35]: (k2_zfmisc_1(A_35, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2196, c_2195])).
% 5.79/2.20  tff(c_3232, plain, (![B_297, A_298]: (m1_subset_1(B_297, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_297), A_298))) | ~r1_tarski(k2_relat_1(B_297), A_298) | ~v1_funct_1(B_297) | ~v1_relat_1(B_297))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.79/2.20  tff(c_3271, plain, (![B_299]: (m1_subset_1(B_299, k1_zfmisc_1('#skF_3')) | ~r1_tarski(k2_relat_1(B_299), '#skF_3') | ~v1_funct_1(B_299) | ~v1_relat_1(B_299))), inference(superposition, [status(thm), theory('equality')], [c_2248, c_3232])).
% 5.79/2.20  tff(c_3754, plain, (![A_352]: (m1_subset_1(k2_funct_1(A_352), k1_zfmisc_1('#skF_3')) | ~r1_tarski(k1_relat_1(A_352), '#skF_3') | ~v1_funct_1(k2_funct_1(A_352)) | ~v1_relat_1(k2_funct_1(A_352)) | ~v2_funct_1(A_352) | ~v1_funct_1(A_352) | ~v1_relat_1(A_352))), inference(superposition, [status(thm), theory('equality')], [c_26, c_3271])).
% 5.79/2.20  tff(c_103, plain, (![A_37, B_38]: (v1_xboole_0(k2_zfmisc_1(A_37, B_38)) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.79/2.20  tff(c_107, plain, (![A_37, B_38]: (k2_zfmisc_1(A_37, B_38)=k1_xboole_0 | ~v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_103, c_4])).
% 5.79/2.20  tff(c_2194, plain, (![B_38]: (k2_zfmisc_1('#skF_3', B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2185, c_107])).
% 5.79/2.20  tff(c_2305, plain, (![B_38]: (k2_zfmisc_1('#skF_3', B_38)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2196, c_2194])).
% 5.79/2.20  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.79/2.20  tff(c_2215, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2196, c_2196, c_18])).
% 5.79/2.20  tff(c_2186, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_245])).
% 5.79/2.20  tff(c_2206, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2186, c_4])).
% 5.79/2.20  tff(c_2286, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2196, c_2206])).
% 5.79/2.20  tff(c_2288, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2286, c_72])).
% 5.79/2.20  tff(c_2693, plain, (![A_233, B_234, C_235]: (k2_relset_1(A_233, B_234, C_235)=k2_relat_1(C_235) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.79/2.20  tff(c_2814, plain, (![C_253]: (k2_relset_1('#skF_1', '#skF_2', C_253)=k2_relat_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2286, c_2693])).
% 5.79/2.20  tff(c_2817, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2288, c_2814])).
% 5.79/2.20  tff(c_2819, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2215, c_68, c_2817])).
% 5.79/2.20  tff(c_2824, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_194])).
% 5.79/2.20  tff(c_2829, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2305, c_2824])).
% 5.79/2.20  tff(c_3775, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3754, c_2829])).
% 5.79/2.20  tff(c_3801, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_76, c_70, c_193, c_2212, c_2214, c_3775])).
% 5.79/2.20  tff(c_3814, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_3801])).
% 5.79/2.20  tff(c_3818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_76, c_3814])).
% 5.79/2.20  tff(c_3819, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_192])).
% 5.79/2.20  tff(c_3820, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_192])).
% 5.79/2.20  tff(c_4285, plain, (![A_380, B_381, C_382]: (k1_relset_1(A_380, B_381, C_382)=k1_relat_1(C_382) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_380, B_381))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.79/2.20  tff(c_4314, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3820, c_4285])).
% 5.79/2.20  tff(c_4798, plain, (![B_418, C_419, A_420]: (k1_xboole_0=B_418 | v1_funct_2(C_419, A_420, B_418) | k1_relset_1(A_420, B_418, C_419)!=A_420 | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_420, B_418))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.79/2.20  tff(c_4819, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_3820, c_4798])).
% 5.79/2.20  tff(c_4832, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4314, c_4819])).
% 5.79/2.20  tff(c_4833, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3819, c_4832])).
% 5.79/2.20  tff(c_4838, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_4833])).
% 5.79/2.20  tff(c_4841, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_4838])).
% 5.79/2.20  tff(c_4844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3899, c_76, c_70, c_4347, c_4841])).
% 5.79/2.20  tff(c_4845, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_4833])).
% 5.79/2.20  tff(c_4880, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4845, c_2])).
% 5.79/2.20  tff(c_4883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3876, c_4880])).
% 5.79/2.20  tff(c_4884, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_3868])).
% 5.79/2.20  tff(c_4895, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4884, c_4])).
% 5.79/2.20  tff(c_30, plain, (v1_relat_1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.79/2.20  tff(c_4905, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4895, c_30])).
% 5.79/2.20  tff(c_4901, plain, (![A_2]: (r1_tarski('#skF_3', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_4895, c_6])).
% 5.79/2.20  tff(c_4904, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4895, c_4895, c_18])).
% 5.79/2.20  tff(c_4903, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4895, c_4895, c_20])).
% 5.79/2.20  tff(c_6100, plain, (![B_491, A_492]: (v1_funct_2(B_491, k1_relat_1(B_491), A_492) | ~r1_tarski(k2_relat_1(B_491), A_492) | ~v1_funct_1(B_491) | ~v1_relat_1(B_491))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.79/2.20  tff(c_6106, plain, (![A_492]: (v1_funct_2('#skF_3', '#skF_3', A_492) | ~r1_tarski(k2_relat_1('#skF_3'), A_492) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4903, c_6100])).
% 5.79/2.20  tff(c_6108, plain, (![A_492]: (v1_funct_2('#skF_3', '#skF_3', A_492))), inference(demodulation, [status(thm), theory('equality')], [c_4905, c_76, c_4901, c_4904, c_6106])).
% 5.79/2.20  tff(c_4885, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_3868])).
% 5.79/2.20  tff(c_4938, plain, (![A_425]: (A_425='#skF_3' | ~v1_xboole_0(A_425))), inference(demodulation, [status(thm), theory('equality')], [c_4895, c_4])).
% 5.79/2.20  tff(c_4951, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_4885, c_4938])).
% 5.79/2.20  tff(c_5018, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4951, c_72])).
% 5.79/2.20  tff(c_5967, plain, (![A_477, B_478, C_479]: (k2_relset_1(A_477, B_478, C_479)=k2_relat_1(C_479) | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(A_477, B_478))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.79/2.20  tff(c_6031, plain, (![C_487]: (k2_relset_1('#skF_1', '#skF_2', C_487)=k2_relat_1(C_487) | ~m1_subset_1(C_487, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4951, c_5967])).
% 5.79/2.20  tff(c_6034, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5018, c_6031])).
% 5.79/2.20  tff(c_6036, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4904, c_6034])).
% 5.79/2.20  tff(c_5399, plain, (![A_447, B_448, C_449]: (k2_relset_1(A_447, B_448, C_449)=k2_relat_1(C_449) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.79/2.20  tff(c_5429, plain, (![C_450]: (k2_relset_1('#skF_1', '#skF_2', C_450)=k2_relat_1(C_450) | ~m1_subset_1(C_450, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4951, c_5399])).
% 5.79/2.20  tff(c_5432, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5018, c_5429])).
% 5.79/2.20  tff(c_5434, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4904, c_68, c_5432])).
% 5.79/2.20  tff(c_3867, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_3820, c_3860])).
% 5.79/2.20  tff(c_5070, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_3867])).
% 5.79/2.20  tff(c_5089, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_10, c_5070])).
% 5.79/2.20  tff(c_5437, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5434, c_5089])).
% 5.79/2.20  tff(c_5446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4884, c_5437])).
% 5.79/2.20  tff(c_5447, plain, (v1_xboole_0(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3867])).
% 5.79/2.20  tff(c_4900, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4895, c_4])).
% 5.79/2.20  tff(c_5458, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_5447, c_4900])).
% 5.79/2.20  tff(c_5462, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5458, c_3819])).
% 5.79/2.20  tff(c_6043, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6036, c_5462])).
% 5.79/2.20  tff(c_6112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6108, c_6043])).
% 5.79/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.20  
% 5.79/2.20  Inference rules
% 5.79/2.20  ----------------------
% 5.79/2.20  #Ref     : 0
% 5.79/2.20  #Sup     : 1411
% 5.79/2.20  #Fact    : 0
% 5.79/2.20  #Define  : 0
% 5.79/2.20  #Split   : 17
% 5.79/2.20  #Chain   : 0
% 5.79/2.20  #Close   : 0
% 5.79/2.20  
% 5.79/2.20  Ordering : KBO
% 5.79/2.20  
% 5.79/2.20  Simplification rules
% 5.79/2.20  ----------------------
% 5.79/2.20  #Subsume      : 151
% 5.79/2.20  #Demod        : 1416
% 5.79/2.20  #Tautology    : 946
% 5.79/2.20  #SimpNegUnit  : 5
% 5.79/2.20  #BackRed      : 157
% 5.79/2.20  
% 5.79/2.20  #Partial instantiations: 0
% 5.79/2.20  #Strategies tried      : 1
% 5.79/2.20  
% 5.79/2.20  Timing (in seconds)
% 5.79/2.20  ----------------------
% 5.79/2.21  Preprocessing        : 0.35
% 5.79/2.21  Parsing              : 0.18
% 5.79/2.21  CNF conversion       : 0.02
% 5.79/2.21  Main loop            : 1.03
% 5.79/2.21  Inferencing          : 0.36
% 5.79/2.21  Reduction            : 0.35
% 5.79/2.21  Demodulation         : 0.26
% 5.79/2.21  BG Simplification    : 0.04
% 5.79/2.21  Subsumption          : 0.19
% 5.79/2.21  Abstraction          : 0.05
% 5.79/2.21  MUC search           : 0.00
% 5.79/2.21  Cooper               : 0.00
% 5.79/2.21  Total                : 1.45
% 5.79/2.21  Index Insertion      : 0.00
% 5.79/2.21  Index Deletion       : 0.00
% 5.79/2.21  Index Matching       : 0.00
% 5.79/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
