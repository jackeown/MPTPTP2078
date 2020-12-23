%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:34 EST 2020

% Result     : Theorem 9.14s
% Output     : CNFRefutation 9.55s
% Verified   : 
% Statistics : Number of formulae       :  416 (4129 expanded)
%              Number of leaves         :   41 (1303 expanded)
%              Depth                    :   19
%              Number of atoms          :  800 (11021 expanded)
%              Number of equality atoms :  238 (3627 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_150,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_128,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_13294,plain,(
    ! [C_1076,A_1077,B_1078] :
      ( v1_relat_1(C_1076)
      | ~ m1_subset_1(C_1076,k1_zfmisc_1(k2_zfmisc_1(A_1077,B_1078))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13319,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_13294])).

tff(c_88,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_82,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_80,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_13563,plain,(
    ! [A_1111,B_1112,C_1113] :
      ( k2_relset_1(A_1111,B_1112,C_1113) = k2_relat_1(C_1113)
      | ~ m1_subset_1(C_1113,k1_zfmisc_1(k2_zfmisc_1(A_1111,B_1112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_13576,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_13563])).

tff(c_13591,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13576])).

tff(c_38,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    ! [A_47] :
      ( v1_funct_1(k2_funct_1(A_47))
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_78,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_153,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_169,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_166,c_153])).

tff(c_172,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_169])).

tff(c_244,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_254,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_244])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_254])).

tff(c_269,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_272,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_294,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_272])).

tff(c_306,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_327,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_306])).

tff(c_86,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3065,plain,(
    ! [A_275,B_276,C_277] :
      ( k1_relset_1(A_275,B_276,C_277) = k1_relat_1(C_277)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3096,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_3065])).

tff(c_4477,plain,(
    ! [B_394,A_395,C_396] :
      ( k1_xboole_0 = B_394
      | k1_relset_1(A_395,B_394,C_396) = A_395
      | ~ v1_funct_2(C_396,A_395,B_394)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_395,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4496,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_4477])).

tff(c_4514,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3096,c_4496])).

tff(c_4518,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4514])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_764,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_795,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_764])).

tff(c_1615,plain,(
    ! [B_195,A_196,C_197] :
      ( k1_xboole_0 = B_195
      | k1_relset_1(A_196,B_195,C_197) = A_196
      | ~ v1_funct_2(C_197,A_196,B_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1634,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1615])).

tff(c_1655,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_795,c_1634])).

tff(c_1659,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1655])).

tff(c_36,plain,(
    ! [A_16] :
      ( k2_relat_1(k2_funct_1(A_16)) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_270,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_608,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_621,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_608])).

tff(c_636,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_621])).

tff(c_552,plain,(
    ! [A_99] :
      ( k1_relat_1(k2_funct_1(A_99)) = k2_relat_1(A_99)
      | ~ v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_68,plain,(
    ! [A_33] :
      ( v1_funct_2(A_33,k1_relat_1(A_33),k2_relat_1(A_33))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2475,plain,(
    ! [A_257] :
      ( v1_funct_2(k2_funct_1(A_257),k2_relat_1(A_257),k2_relat_1(k2_funct_1(A_257)))
      | ~ v1_funct_1(k2_funct_1(A_257))
      | ~ v1_relat_1(k2_funct_1(A_257))
      | ~ v2_funct_1(A_257)
      | ~ v1_funct_1(A_257)
      | ~ v1_relat_1(A_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_68])).

tff(c_2478,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_2475])).

tff(c_2486,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_82,c_270,c_2478])).

tff(c_2487,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2486])).

tff(c_2490,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_2487])).

tff(c_2494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_2490])).

tff(c_2496,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2486])).

tff(c_584,plain,(
    ! [A_101] :
      ( m1_subset_1(A_101,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_101),k2_relat_1(A_101))))
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2638,plain,(
    ! [A_269] :
      ( m1_subset_1(k2_funct_1(A_269),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_269),k2_relat_1(k2_funct_1(A_269)))))
      | ~ v1_funct_1(k2_funct_1(A_269))
      | ~ v1_relat_1(k2_funct_1(A_269))
      | ~ v2_funct_1(A_269)
      | ~ v1_funct_1(A_269)
      | ~ v1_relat_1(A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_584])).

tff(c_2667,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_2638])).

tff(c_2686,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_82,c_2496,c_270,c_2667])).

tff(c_2715,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2686])).

tff(c_2734,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_82,c_1659,c_2715])).

tff(c_2736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_2734])).

tff(c_2737,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1655])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1400,plain,(
    ! [B_182,A_183] :
      ( m1_subset_1(B_182,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_182),A_183)))
      | ~ r1_tarski(k2_relat_1(B_182),A_183)
      | ~ v1_funct_1(B_182)
      | ~ v1_relat_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1605,plain,(
    ! [B_194] :
      ( m1_subset_1(B_194,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_194),k1_xboole_0)
      | ~ v1_funct_1(B_194)
      | ~ v1_relat_1(B_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1400])).

tff(c_1608,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_1605])).

tff(c_1613,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_1608])).

tff(c_1614,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1613])).

tff(c_2740,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_1614])).

tff(c_2778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2740])).

tff(c_2780,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1613])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2799,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_2780,c_2])).

tff(c_2811,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2799])).

tff(c_2883,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2811,c_8])).

tff(c_2881,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2811,c_2811,c_12])).

tff(c_66,plain,(
    ! [A_33] :
      ( m1_subset_1(A_33,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33),k2_relat_1(A_33))))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_641,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_66])).

tff(c_648,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_641])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_681,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_648,c_18])).

tff(c_706,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_681,c_2])).

tff(c_721,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_706])).

tff(c_3052,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2881,c_721])).

tff(c_3062,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2883,c_3052])).

tff(c_3063,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_4526,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4518,c_3063])).

tff(c_126,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_84,c_126])).

tff(c_329,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_344,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_329])).

tff(c_429,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_4571,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_429])).

tff(c_4576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4571])).

tff(c_4577,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4514])).

tff(c_4076,plain,(
    ! [B_365,A_366] :
      ( m1_subset_1(B_365,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_365),A_366)))
      | ~ r1_tarski(k2_relat_1(B_365),A_366)
      | ~ v1_funct_1(B_365)
      | ~ v1_relat_1(B_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4295,plain,(
    ! [B_380] :
      ( m1_subset_1(B_380,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_380),k1_xboole_0)
      | ~ v1_funct_1(B_380)
      | ~ v1_relat_1(B_380) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4076])).

tff(c_4298,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_4295])).

tff(c_4303,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_4298])).

tff(c_4304,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_4303])).

tff(c_4585,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4577,c_4304])).

tff(c_4620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4585])).

tff(c_4622,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4303])).

tff(c_349,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_329])).

tff(c_4650,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4622,c_349])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3117,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = k1_xboole_0
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3063,c_10])).

tff(c_3800,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3117])).

tff(c_4665,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4650,c_3800])).

tff(c_4686,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4650,c_8])).

tff(c_4621,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_4303])).

tff(c_4786,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4650,c_4621])).

tff(c_4799,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4786,c_18])).

tff(c_4840,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_4799,c_2])).

tff(c_4846,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4686,c_4840])).

tff(c_4848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4665,c_4846])).

tff(c_4850,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3117])).

tff(c_4871,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4850,c_8])).

tff(c_4869,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4850,c_4850,c_12])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4870,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4850,c_4850,c_14])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3097,plain,(
    ! [A_275,B_276] : k1_relset_1(A_275,B_276,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_3065])).

tff(c_54,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3179,plain,(
    ! [C_283,B_284] :
      ( v1_funct_2(C_283,k1_xboole_0,B_284)
      | k1_relset_1(k1_xboole_0,B_284,C_283) != k1_xboole_0
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_54])).

tff(c_3185,plain,(
    ! [B_284] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_284)
      | k1_relset_1(k1_xboole_0,B_284,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_3179])).

tff(c_3188,plain,(
    ! [B_284] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_284)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3097,c_3185])).

tff(c_3189,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3188])).

tff(c_136,plain,(
    ! [A_45] : m1_subset_1(k6_partfun1(A_45),k1_zfmisc_1(k2_zfmisc_1(A_45,A_45))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_143,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_136])).

tff(c_152,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_143,c_18])).

tff(c_333,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_152,c_329])).

tff(c_343,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_333])).

tff(c_62,plain,(
    ! [A_32] : v1_partfun1(k6_partfun1(A_32),A_32) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_366,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_62])).

tff(c_386,plain,(
    ! [B_73,A_74] :
      ( v1_funct_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_403,plain,(
    ! [A_6] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_16,c_386])).

tff(c_431,plain,(
    ! [A_77] :
      ( ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(splitLeft,[status(thm)],[c_403])).

tff(c_440,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_327,c_431])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_440])).

tff(c_450,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_403])).

tff(c_3696,plain,(
    ! [C_328,A_329,B_330] :
      ( v1_funct_2(C_328,A_329,B_330)
      | ~ v1_partfun1(C_328,A_329)
      | ~ v1_funct_1(C_328)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3719,plain,(
    ! [A_329,B_330] :
      ( v1_funct_2(k1_xboole_0,A_329,B_330)
      | ~ v1_partfun1(k1_xboole_0,A_329)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_3696])).

tff(c_3738,plain,(
    ! [A_331,B_332] :
      ( v1_funct_2(k1_xboole_0,A_331,B_332)
      | ~ v1_partfun1(k1_xboole_0,A_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_3719])).

tff(c_58,plain,(
    ! [B_30,C_31] :
      ( k1_relset_1(k1_xboole_0,B_30,C_31) = k1_xboole_0
      | ~ v1_funct_2(C_31,k1_xboole_0,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_91,plain,(
    ! [B_30,C_31] :
      ( k1_relset_1(k1_xboole_0,B_30,C_31) = k1_xboole_0
      | ~ v1_funct_2(C_31,k1_xboole_0,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_3741,plain,(
    ! [B_332] :
      ( k1_relset_1(k1_xboole_0,B_332,k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3738,c_91])).

tff(c_3747,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_16,c_3097,c_3741])).

tff(c_3749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3189,c_3747])).

tff(c_3751,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3188])).

tff(c_3752,plain,(
    ! [A_275,B_276] : k1_relset_1(A_275,B_276,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3751,c_3097])).

tff(c_4852,plain,(
    ! [A_275,B_276] : k1_relset_1(A_275,B_276,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4850,c_4850,c_3752])).

tff(c_4868,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4850,c_16])).

tff(c_60,plain,(
    ! [B_30,A_29,C_31] :
      ( k1_xboole_0 = B_30
      | k1_relset_1(A_29,B_30,C_31) = A_29
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5242,plain,(
    ! [B_422,A_423,C_424] :
      ( B_422 = '#skF_4'
      | k1_relset_1(A_423,B_422,C_424) = A_423
      | ~ v1_funct_2(C_424,A_423,B_422)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(A_423,B_422))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4850,c_60])).

tff(c_5255,plain,(
    ! [B_422,A_423] :
      ( B_422 = '#skF_4'
      | k1_relset_1(A_423,B_422,'#skF_4') = A_423
      | ~ v1_funct_2('#skF_4',A_423,B_422) ) ),
    inference(resolution,[status(thm)],[c_4868,c_5242])).

tff(c_5318,plain,(
    ! [B_432,A_433] :
      ( B_432 = '#skF_4'
      | A_433 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_433,B_432) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4852,c_5255])).

tff(c_5350,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_86,c_5318])).

tff(c_5351,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5350])).

tff(c_5352,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5351,c_429])).

tff(c_5358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4870,c_5352])).

tff(c_5359,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5350])).

tff(c_5398,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5359,c_429])).

tff(c_5404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4871,c_4869,c_5398])).

tff(c_5405,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_5408,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5405,c_84])).

tff(c_5590,plain,(
    ! [A_462,B_463,C_464] :
      ( k1_relset_1(A_462,B_463,C_464) = k1_relat_1(C_464)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(k2_zfmisc_1(A_462,B_463))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5704,plain,(
    ! [C_477] :
      ( k1_relset_1('#skF_2','#skF_3',C_477) = k1_relat_1(C_477)
      | ~ m1_subset_1(C_477,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5405,c_5590])).

tff(c_5716,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5408,c_5704])).

tff(c_7735,plain,(
    ! [B_615,A_616,C_617] :
      ( k1_xboole_0 = B_615
      | k1_relset_1(A_616,B_615,C_617) = A_616
      | ~ v1_funct_2(C_617,A_616,B_615)
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(A_616,B_615))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7747,plain,(
    ! [C_617] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_617) = '#skF_2'
      | ~ v1_funct_2(C_617,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_617,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5405,c_7735])).

tff(c_7840,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7747])).

tff(c_5835,plain,(
    ! [A_488,B_489,C_490] :
      ( k2_relset_1(A_488,B_489,C_490) = k2_relat_1(C_490)
      | ~ m1_subset_1(C_490,k1_zfmisc_1(k2_zfmisc_1(A_488,B_489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5883,plain,(
    ! [C_494] :
      ( k2_relset_1('#skF_2','#skF_3',C_494) = k2_relat_1(C_494)
      | ~ m1_subset_1(C_494,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5405,c_5835])).

tff(c_5886,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5408,c_5883])).

tff(c_5896,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5886])).

tff(c_7639,plain,(
    ! [B_603,A_604] :
      ( m1_subset_1(B_603,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_603),A_604)))
      | ~ r1_tarski(k2_relat_1(B_603),A_604)
      | ~ v1_funct_1(B_603)
      | ~ v1_relat_1(B_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_7686,plain,(
    ! [B_605] :
      ( m1_subset_1(B_605,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(B_605),k1_xboole_0)
      | ~ v1_funct_1(B_605)
      | ~ v1_relat_1(B_605) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_7639])).

tff(c_7689,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0)
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5896,c_7686])).

tff(c_7694,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_7689])).

tff(c_7695,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7694])).

tff(c_7848,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7840,c_7695])).

tff(c_7884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7848])).

tff(c_8014,plain,(
    ! [C_629] :
      ( k1_relset_1('#skF_2','#skF_3',C_629) = '#skF_2'
      | ~ v1_funct_2(C_629,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_629,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_7747])).

tff(c_8017,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_5408,c_8014])).

tff(c_8028,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_5716,c_8017])).

tff(c_5578,plain,(
    ! [A_461] :
      ( k1_relat_1(k2_funct_1(A_461)) = k2_relat_1(A_461)
      | ~ v2_funct_1(A_461)
      | ~ v1_funct_1(A_461)
      | ~ v1_relat_1(A_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8937,plain,(
    ! [A_688] :
      ( v1_funct_2(k2_funct_1(A_688),k2_relat_1(A_688),k2_relat_1(k2_funct_1(A_688)))
      | ~ v1_funct_1(k2_funct_1(A_688))
      | ~ v1_relat_1(k2_funct_1(A_688))
      | ~ v2_funct_1(A_688)
      | ~ v1_funct_1(A_688)
      | ~ v1_relat_1(A_688) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5578,c_68])).

tff(c_8940,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5896,c_8937])).

tff(c_8948,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_82,c_270,c_8940])).

tff(c_8949,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8948])).

tff(c_8952,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_8949])).

tff(c_8956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_8952])).

tff(c_8958,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8948])).

tff(c_5665,plain,(
    ! [A_474] :
      ( m1_subset_1(A_474,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_474),k2_relat_1(A_474))))
      | ~ v1_funct_1(A_474)
      | ~ v1_relat_1(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5786,plain,(
    ! [A_484] :
      ( r1_tarski(A_484,k2_zfmisc_1(k1_relat_1(A_484),k2_relat_1(A_484)))
      | ~ v1_funct_1(A_484)
      | ~ v1_relat_1(A_484) ) ),
    inference(resolution,[status(thm)],[c_5665,c_18])).

tff(c_9034,plain,(
    ! [A_692] :
      ( r1_tarski(k2_funct_1(A_692),k2_zfmisc_1(k2_relat_1(A_692),k2_relat_1(k2_funct_1(A_692))))
      | ~ v1_funct_1(k2_funct_1(A_692))
      | ~ v1_relat_1(k2_funct_1(A_692))
      | ~ v2_funct_1(A_692)
      | ~ v1_funct_1(A_692)
      | ~ v1_relat_1(A_692) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_5786])).

tff(c_9060,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5896,c_9034])).

tff(c_9078,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_82,c_8958,c_270,c_9060])).

tff(c_9104,plain,
    ( r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_9078])).

tff(c_9122,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_82,c_8028,c_9104])).

tff(c_9124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_294,c_9122])).

tff(c_9126,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7694])).

tff(c_9154,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_9126,c_349])).

tff(c_5415,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5405,c_10])).

tff(c_5452,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5415])).

tff(c_9217,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9154,c_5452])).

tff(c_9230,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9154,c_8])).

tff(c_9125,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_7694])).

tff(c_9357,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9154,c_9125])).

tff(c_9370,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_9357,c_18])).

tff(c_9403,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_9370,c_2])).

tff(c_9409,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9230,c_9403])).

tff(c_9411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9217,c_9409])).

tff(c_9413,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5415])).

tff(c_9426,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9413,c_8])).

tff(c_9423,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9413,c_16])).

tff(c_11780,plain,(
    ! [A_936,B_937,C_938] :
      ( k1_relset_1(A_936,B_937,C_938) = k1_relat_1(C_938)
      | ~ m1_subset_1(C_938,k1_zfmisc_1(k2_zfmisc_1(A_936,B_937))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_11798,plain,(
    ! [A_936,B_937] : k1_relset_1(A_936,B_937,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9423,c_11780])).

tff(c_9729,plain,(
    ! [A_734,B_735,C_736] :
      ( k2_relset_1(A_734,B_735,C_736) = k2_relat_1(C_736)
      | ~ m1_subset_1(C_736,k1_zfmisc_1(k2_zfmisc_1(A_734,B_735))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_9750,plain,(
    ! [A_737,B_738] : k2_relset_1(A_737,B_738,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9423,c_9729])).

tff(c_9412,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5415])).

tff(c_9465,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9413,c_9413,c_9412])).

tff(c_9466,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9465])).

tff(c_9470,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9466,c_9466,c_80])).

tff(c_9754,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9750,c_9470])).

tff(c_9649,plain,(
    ! [A_722] :
      ( k1_relat_1(k2_funct_1(A_722)) = k2_relat_1(A_722)
      | ~ v2_funct_1(A_722)
      | ~ v1_funct_1(A_722)
      | ~ v1_relat_1(A_722) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11389,plain,(
    ! [A_894] :
      ( v1_funct_2(k2_funct_1(A_894),k2_relat_1(A_894),k2_relat_1(k2_funct_1(A_894)))
      | ~ v1_funct_1(k2_funct_1(A_894))
      | ~ v1_relat_1(k2_funct_1(A_894))
      | ~ v2_funct_1(A_894)
      | ~ v1_funct_1(A_894)
      | ~ v1_relat_1(A_894) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9649,c_68])).

tff(c_11392,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9754,c_11389])).

tff(c_11400,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_82,c_270,c_11392])).

tff(c_11401,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11400])).

tff(c_11404,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_11401])).

tff(c_11408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_11404])).

tff(c_11410,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_11400])).

tff(c_9874,plain,(
    ! [A_751,B_752,C_753] :
      ( k1_relset_1(A_751,B_752,C_753) = k1_relat_1(C_753)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(k2_zfmisc_1(A_751,B_752))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9896,plain,(
    ! [A_751,B_752] : k1_relset_1(A_751,B_752,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9423,c_9874])).

tff(c_92,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_54])).

tff(c_9951,plain,(
    ! [C_763,B_764] :
      ( v1_funct_2(C_763,'#skF_4',B_764)
      | k1_relset_1('#skF_4',B_764,C_763) != '#skF_4'
      | ~ m1_subset_1(C_763,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9413,c_9413,c_9413,c_9413,c_92])).

tff(c_9954,plain,(
    ! [B_764] :
      ( v1_funct_2('#skF_4','#skF_4',B_764)
      | k1_relset_1('#skF_4',B_764,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_9423,c_9951])).

tff(c_9959,plain,(
    ! [B_764] :
      ( v1_funct_2('#skF_4','#skF_4',B_764)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9896,c_9954])).

tff(c_9961,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9959])).

tff(c_9418,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9413,c_9413,c_366])).

tff(c_10261,plain,(
    ! [C_793,A_794,B_795] :
      ( v1_funct_2(C_793,A_794,B_795)
      | ~ v1_partfun1(C_793,A_794)
      | ~ v1_funct_1(C_793)
      | ~ m1_subset_1(C_793,k1_zfmisc_1(k2_zfmisc_1(A_794,B_795))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10274,plain,(
    ! [A_794,B_795] :
      ( v1_funct_2('#skF_4',A_794,B_795)
      | ~ v1_partfun1('#skF_4',A_794)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9423,c_10261])).

tff(c_10294,plain,(
    ! [A_796,B_797] :
      ( v1_funct_2('#skF_4',A_796,B_797)
      | ~ v1_partfun1('#skF_4',A_796) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_10274])).

tff(c_10094,plain,(
    ! [B_30,C_31] :
      ( k1_relset_1('#skF_4',B_30,C_31) = '#skF_4'
      | ~ v1_funct_2(C_31,'#skF_4',B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9413,c_9413,c_9413,c_9413,c_91])).

tff(c_10297,plain,(
    ! [B_797] :
      ( k1_relset_1('#skF_4',B_797,'#skF_4') = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
      | ~ v1_partfun1('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10294,c_10094])).

tff(c_10303,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9418,c_9423,c_9896,c_10297])).

tff(c_10305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9961,c_10303])).

tff(c_10307,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9959])).

tff(c_9424,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9413,c_9413,c_12])).

tff(c_10652,plain,(
    ! [B_830,A_831] :
      ( m1_subset_1(B_830,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_830),A_831)))
      | ~ r1_tarski(k2_relat_1(B_830),A_831)
      | ~ v1_funct_1(B_830)
      | ~ v1_relat_1(B_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_10976,plain,(
    ! [B_856,A_857] :
      ( r1_tarski(B_856,k2_zfmisc_1(k1_relat_1(B_856),A_857))
      | ~ r1_tarski(k2_relat_1(B_856),A_857)
      | ~ v1_funct_1(B_856)
      | ~ v1_relat_1(B_856) ) ),
    inference(resolution,[status(thm)],[c_10652,c_18])).

tff(c_11433,plain,(
    ! [B_895,A_896] :
      ( k2_zfmisc_1(k1_relat_1(B_895),A_896) = B_895
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(B_895),A_896),B_895)
      | ~ r1_tarski(k2_relat_1(B_895),A_896)
      | ~ v1_funct_1(B_895)
      | ~ v1_relat_1(B_895) ) ),
    inference(resolution,[status(thm)],[c_10976,c_2])).

tff(c_11443,plain,(
    ! [B_895] :
      ( k2_zfmisc_1(k1_relat_1(B_895),'#skF_4') = B_895
      | ~ r1_tarski('#skF_4',B_895)
      | ~ r1_tarski(k2_relat_1(B_895),'#skF_4')
      | ~ v1_funct_1(B_895)
      | ~ v1_relat_1(B_895) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9424,c_11433])).

tff(c_11448,plain,(
    ! [B_897] :
      ( B_897 = '#skF_4'
      | ~ r1_tarski(k2_relat_1(B_897),'#skF_4')
      | ~ v1_funct_1(B_897)
      | ~ v1_relat_1(B_897) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9426,c_9424,c_11443])).

tff(c_11458,plain,(
    ! [A_898] :
      ( k2_funct_1(A_898) = '#skF_4'
      | ~ r1_tarski(k1_relat_1(A_898),'#skF_4')
      | ~ v1_funct_1(k2_funct_1(A_898))
      | ~ v1_relat_1(k2_funct_1(A_898))
      | ~ v2_funct_1(A_898)
      | ~ v1_funct_1(A_898)
      | ~ v1_relat_1(A_898) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_11448])).

tff(c_11461,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10307,c_11458])).

tff(c_11466,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_82,c_11410,c_270,c_9426,c_11461])).

tff(c_9425,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9413,c_9413,c_14])).

tff(c_9469,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9466,c_272])).

tff(c_9590,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9425,c_9469])).

tff(c_9594,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_9590])).

tff(c_11482,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11466,c_9594])).

tff(c_11490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9426,c_11482])).

tff(c_11491,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9465])).

tff(c_11497,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11491,c_86])).

tff(c_12085,plain,(
    ! [B_975,C_976] :
      ( k1_relset_1('#skF_4',B_975,C_976) = '#skF_4'
      | ~ v1_funct_2(C_976,'#skF_4',B_975)
      | ~ m1_subset_1(C_976,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9413,c_9413,c_9413,c_9413,c_91])).

tff(c_12090,plain,
    ( k1_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_11497,c_12085])).

tff(c_12097,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9423,c_11798,c_12090])).

tff(c_11630,plain,(
    ! [A_912] :
      ( k2_relat_1(k2_funct_1(A_912)) = k1_relat_1(A_912)
      | ~ v2_funct_1(A_912)
      | ~ v1_funct_1(A_912)
      | ~ v1_relat_1(A_912) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_13039,plain,(
    ! [A_1054] :
      ( v1_funct_2(k2_funct_1(A_1054),k1_relat_1(k2_funct_1(A_1054)),k1_relat_1(A_1054))
      | ~ v1_funct_1(k2_funct_1(A_1054))
      | ~ v1_relat_1(k2_funct_1(A_1054))
      | ~ v2_funct_1(A_1054)
      | ~ v1_funct_1(A_1054)
      | ~ v1_relat_1(A_1054) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11630,c_68])).

tff(c_13042,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12097,c_13039])).

tff(c_13050,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_82,c_270,c_13042])).

tff(c_13051,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_13050])).

tff(c_13054,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_13051])).

tff(c_13058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_13054])).

tff(c_13060,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13050])).

tff(c_12338,plain,(
    ! [B_992,A_993] :
      ( m1_subset_1(B_992,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_992),A_993)))
      | ~ r1_tarski(k2_relat_1(B_992),A_993)
      | ~ v1_funct_1(B_992)
      | ~ v1_relat_1(B_992) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_12693,plain,(
    ! [B_1024,A_1025] :
      ( r1_tarski(B_1024,k2_zfmisc_1(k1_relat_1(B_1024),A_1025))
      | ~ r1_tarski(k2_relat_1(B_1024),A_1025)
      | ~ v1_funct_1(B_1024)
      | ~ v1_relat_1(B_1024) ) ),
    inference(resolution,[status(thm)],[c_12338,c_18])).

tff(c_13167,plain,(
    ! [B_1064,A_1065] :
      ( k2_zfmisc_1(k1_relat_1(B_1064),A_1065) = B_1064
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(B_1064),A_1065),B_1064)
      | ~ r1_tarski(k2_relat_1(B_1064),A_1065)
      | ~ v1_funct_1(B_1064)
      | ~ v1_relat_1(B_1064) ) ),
    inference(resolution,[status(thm)],[c_12693,c_2])).

tff(c_13177,plain,(
    ! [B_1064] :
      ( k2_zfmisc_1(k1_relat_1(B_1064),'#skF_4') = B_1064
      | ~ r1_tarski('#skF_4',B_1064)
      | ~ r1_tarski(k2_relat_1(B_1064),'#skF_4')
      | ~ v1_funct_1(B_1064)
      | ~ v1_relat_1(B_1064) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9424,c_13167])).

tff(c_13182,plain,(
    ! [B_1066] :
      ( B_1066 = '#skF_4'
      | ~ r1_tarski(k2_relat_1(B_1066),'#skF_4')
      | ~ v1_funct_1(B_1066)
      | ~ v1_relat_1(B_1066) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9426,c_9424,c_13177])).

tff(c_13192,plain,(
    ! [A_1067] :
      ( k2_funct_1(A_1067) = '#skF_4'
      | ~ r1_tarski(k1_relat_1(A_1067),'#skF_4')
      | ~ v1_funct_1(k2_funct_1(A_1067))
      | ~ v1_relat_1(k2_funct_1(A_1067))
      | ~ v2_funct_1(A_1067)
      | ~ v1_funct_1(A_1067)
      | ~ v1_relat_1(A_1067) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_13182])).

tff(c_13195,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12097,c_13192])).

tff(c_13200,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_88,c_82,c_13060,c_270,c_9426,c_13195])).

tff(c_11495,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11491,c_272])).

tff(c_11619,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9424,c_11495])).

tff(c_11623,plain,(
    ~ r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_11619])).

tff(c_13205,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13200,c_11623])).

tff(c_13213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9426,c_13205])).

tff(c_13214,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_13215,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_13828,plain,(
    ! [A_1133,B_1134,C_1135] :
      ( k1_relset_1(A_1133,B_1134,C_1135) = k1_relat_1(C_1135)
      | ~ m1_subset_1(C_1135,k1_zfmisc_1(k2_zfmisc_1(A_1133,B_1134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_13861,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_13215,c_13828])).

tff(c_14412,plain,(
    ! [B_1189,C_1190,A_1191] :
      ( k1_xboole_0 = B_1189
      | v1_funct_2(C_1190,A_1191,B_1189)
      | k1_relset_1(A_1191,B_1189,C_1190) != A_1191
      | ~ m1_subset_1(C_1190,k1_zfmisc_1(k2_zfmisc_1(A_1191,B_1189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_14428,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_13215,c_14412])).

tff(c_14452,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13861,c_14428])).

tff(c_14453,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_13214,c_14452])).

tff(c_14461,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14453])).

tff(c_14464,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_14461])).

tff(c_14467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13319,c_88,c_82,c_13591,c_14464])).

tff(c_14468,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14453])).

tff(c_14504,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14468,c_8])).

tff(c_14503,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14468,c_14468,c_14])).

tff(c_13238,plain,(
    ! [B_1073,A_1074] :
      ( B_1073 = A_1074
      | ~ r1_tarski(B_1073,A_1074)
      | ~ r1_tarski(A_1074,B_1073) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13256,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_13238])).

tff(c_13332,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_13256])).

tff(c_14752,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14503,c_13332])).

tff(c_14757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14504,c_14752])).

tff(c_14758,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13256])).

tff(c_14765,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14758,c_84])).

tff(c_15214,plain,(
    ! [A_1252,B_1253,C_1254] :
      ( k2_relset_1(A_1252,B_1253,C_1254) = k2_relat_1(C_1254)
      | ~ m1_subset_1(C_1254,k1_zfmisc_1(k2_zfmisc_1(A_1252,B_1253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_15308,plain,(
    ! [C_1261] :
      ( k2_relset_1('#skF_2','#skF_3',C_1261) = k2_relat_1(C_1261)
      | ~ m1_subset_1(C_1261,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14758,c_15214])).

tff(c_15311,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14765,c_15308])).

tff(c_15321,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_15311])).

tff(c_15007,plain,(
    ! [A_1228,B_1229,C_1230] :
      ( k1_relset_1(A_1228,B_1229,C_1230) = k1_relat_1(C_1230)
      | ~ m1_subset_1(C_1230,k1_zfmisc_1(k2_zfmisc_1(A_1228,B_1229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_15032,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_13215,c_15007])).

tff(c_16214,plain,(
    ! [B_1329,C_1330,A_1331] :
      ( k1_xboole_0 = B_1329
      | v1_funct_2(C_1330,A_1331,B_1329)
      | k1_relset_1(A_1331,B_1329,C_1330) != A_1331
      | ~ m1_subset_1(C_1330,k1_zfmisc_1(k2_zfmisc_1(A_1331,B_1329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_16233,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_13215,c_16214])).

tff(c_16254,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15032,c_16233])).

tff(c_16255,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_13214,c_16254])).

tff(c_16261,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_16255])).

tff(c_16264,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_16261])).

tff(c_16267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13319,c_88,c_82,c_15321,c_16264])).

tff(c_16268,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16255])).

tff(c_14770,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_14758,c_10])).

tff(c_14884,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14770])).

tff(c_16299,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16268,c_14884])).

tff(c_16449,plain,(
    ! [B_1333] : k2_zfmisc_1('#skF_2',B_1333) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16268,c_16268,c_14])).

tff(c_16486,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_16449,c_14758])).

tff(c_16510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16299,c_16486])).

tff(c_16512,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14770])).

tff(c_16525,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16512,c_8])).

tff(c_16524,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16512,c_16512,c_14])).

tff(c_16511,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14770])).

tff(c_16858,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16512,c_16512,c_16511])).

tff(c_16859,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16858])).

tff(c_13231,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_13215,c_18])).

tff(c_16861,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16859,c_13231])).

tff(c_16867,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16524,c_16861])).

tff(c_16904,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_16867,c_2])).

tff(c_16909,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16525,c_16904])).

tff(c_16953,plain,(
    ! [A_1357] :
      ( k1_relat_1(k2_funct_1(A_1357)) = k2_relat_1(A_1357)
      | ~ v2_funct_1(A_1357)
      | ~ v1_funct_1(A_1357)
      | ~ v1_relat_1(A_1357) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16965,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16909,c_16953])).

tff(c_16969,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13319,c_88,c_82,c_16965])).

tff(c_16522,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16512,c_16])).

tff(c_17135,plain,(
    ! [A_1387,B_1388,C_1389] :
      ( k2_relset_1(A_1387,B_1388,C_1389) = k2_relat_1(C_1389)
      | ~ m1_subset_1(C_1389,k1_zfmisc_1(k2_zfmisc_1(A_1387,B_1388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_17139,plain,(
    ! [A_1387,B_1388] : k2_relset_1(A_1387,B_1388,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16522,c_17135])).

tff(c_17157,plain,(
    ! [A_1390,B_1391] : k2_relset_1(A_1390,B_1391,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16969,c_17139])).

tff(c_16864,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16859,c_16859,c_80])).

tff(c_17161,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_17157,c_16864])).

tff(c_17069,plain,(
    ! [A_1375,B_1376,C_1377] :
      ( k1_relset_1(A_1375,B_1376,C_1377) = k1_relat_1(C_1377)
      | ~ m1_subset_1(C_1377,k1_zfmisc_1(k2_zfmisc_1(A_1375,B_1376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_17087,plain,(
    ! [A_1375,B_1376] : k1_relset_1(A_1375,B_1376,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16522,c_17069])).

tff(c_17169,plain,(
    ! [A_1375,B_1376] : k1_relset_1(A_1375,B_1376,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17161,c_17087])).

tff(c_17348,plain,(
    ! [C_1412,B_1413] :
      ( v1_funct_2(C_1412,'#skF_4',B_1413)
      | k1_relset_1('#skF_4',B_1413,C_1412) != '#skF_4'
      | ~ m1_subset_1(C_1412,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16512,c_16512,c_16512,c_16512,c_92])).

tff(c_17351,plain,(
    ! [B_1413] :
      ( v1_funct_2('#skF_4','#skF_4',B_1413)
      | k1_relset_1('#skF_4',B_1413,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_16522,c_17348])).

tff(c_17357,plain,(
    ! [B_1413] : v1_funct_2('#skF_4','#skF_4',B_1413) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17169,c_17351])).

tff(c_16863,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16859,c_13214])).

tff(c_16950,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16909,c_16863])).

tff(c_17362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17357,c_16950])).

tff(c_17364,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16858])).

tff(c_50,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_29,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_90,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_17459,plain,(
    ! [A_1417] :
      ( v1_funct_2('#skF_4',A_1417,'#skF_4')
      | A_1417 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16512,c_16512,c_16512,c_90])).

tff(c_16523,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16512,c_16512,c_12])).

tff(c_17363,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16858])).

tff(c_17366,plain,(
    r1_tarski(k2_funct_1('#skF_4'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17363,c_13231])).

tff(c_17372,plain,(
    r1_tarski(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16523,c_17366])).

tff(c_17409,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_17372,c_2])).

tff(c_17414,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16525,c_17409])).

tff(c_17368,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17363,c_13214])).

tff(c_17451,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17414,c_17368])).

tff(c_17462,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17459,c_17451])).

tff(c_17466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17364,c_17462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.14/3.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.46  
% 9.41/3.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.47  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.41/3.47  
% 9.41/3.47  %Foreground sorts:
% 9.41/3.47  
% 9.41/3.47  
% 9.41/3.47  %Background operators:
% 9.41/3.47  
% 9.41/3.47  
% 9.41/3.47  %Foreground operators:
% 9.41/3.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.41/3.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.41/3.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.41/3.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.41/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.41/3.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.41/3.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.41/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.41/3.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.41/3.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.41/3.47  tff('#skF_2', type, '#skF_2': $i).
% 9.41/3.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.41/3.47  tff('#skF_3', type, '#skF_3': $i).
% 9.41/3.47  tff('#skF_1', type, '#skF_1': $i).
% 9.41/3.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.41/3.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.41/3.47  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.41/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.41/3.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.41/3.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.41/3.47  tff('#skF_4', type, '#skF_4': $i).
% 9.41/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.41/3.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.41/3.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.41/3.47  
% 9.55/3.51  tff(f_167, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 9.55/3.51  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.55/3.51  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.55/3.51  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.55/3.51  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.55/3.51  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.55/3.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.55/3.51  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.55/3.51  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.55/3.51  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.55/3.51  tff(f_138, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 9.55/3.51  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.55/3.51  tff(f_150, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 9.55/3.51  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.55/3.51  tff(f_128, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.55/3.51  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 9.55/3.51  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 9.55/3.51  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.55/3.51  tff(c_13294, plain, (![C_1076, A_1077, B_1078]: (v1_relat_1(C_1076) | ~m1_subset_1(C_1076, k1_zfmisc_1(k2_zfmisc_1(A_1077, B_1078))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.55/3.51  tff(c_13319, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_13294])).
% 9.55/3.51  tff(c_88, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.55/3.51  tff(c_82, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.55/3.51  tff(c_80, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.55/3.51  tff(c_13563, plain, (![A_1111, B_1112, C_1113]: (k2_relset_1(A_1111, B_1112, C_1113)=k2_relat_1(C_1113) | ~m1_subset_1(C_1113, k1_zfmisc_1(k2_zfmisc_1(A_1111, B_1112))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.55/3.51  tff(c_13576, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_13563])).
% 9.55/3.51  tff(c_13591, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_13576])).
% 9.55/3.51  tff(c_38, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.55/3.51  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.55/3.51  tff(c_166, plain, (![A_47]: (v1_funct_1(k2_funct_1(A_47)) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.55/3.51  tff(c_78, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.55/3.51  tff(c_153, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_78])).
% 9.55/3.51  tff(c_169, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_166, c_153])).
% 9.55/3.51  tff(c_172, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_169])).
% 9.55/3.51  tff(c_244, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.55/3.51  tff(c_254, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_244])).
% 9.55/3.51  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_254])).
% 9.55/3.51  tff(c_269, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_78])).
% 9.55/3.51  tff(c_272, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_269])).
% 9.55/3.51  tff(c_294, plain, (~r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_272])).
% 9.55/3.51  tff(c_306, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.55/3.51  tff(c_327, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_306])).
% 9.55/3.51  tff(c_86, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 9.55/3.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.55/3.51  tff(c_3065, plain, (![A_275, B_276, C_277]: (k1_relset_1(A_275, B_276, C_277)=k1_relat_1(C_277) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.55/3.51  tff(c_3096, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_3065])).
% 9.55/3.51  tff(c_4477, plain, (![B_394, A_395, C_396]: (k1_xboole_0=B_394 | k1_relset_1(A_395, B_394, C_396)=A_395 | ~v1_funct_2(C_396, A_395, B_394) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_395, B_394))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.55/3.51  tff(c_4496, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_84, c_4477])).
% 9.55/3.51  tff(c_4514, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_3096, c_4496])).
% 9.55/3.51  tff(c_4518, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_4514])).
% 9.55/3.51  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.55/3.51  tff(c_764, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.55/3.51  tff(c_795, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_764])).
% 9.55/3.51  tff(c_1615, plain, (![B_195, A_196, C_197]: (k1_xboole_0=B_195 | k1_relset_1(A_196, B_195, C_197)=A_196 | ~v1_funct_2(C_197, A_196, B_195) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.55/3.51  tff(c_1634, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_84, c_1615])).
% 9.55/3.51  tff(c_1655, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_795, c_1634])).
% 9.55/3.51  tff(c_1659, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1655])).
% 9.55/3.51  tff(c_36, plain, (![A_16]: (k2_relat_1(k2_funct_1(A_16))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.55/3.51  tff(c_28, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.55/3.51  tff(c_270, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_78])).
% 9.55/3.51  tff(c_608, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.55/3.51  tff(c_621, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_608])).
% 9.55/3.51  tff(c_636, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_621])).
% 9.55/3.51  tff(c_552, plain, (![A_99]: (k1_relat_1(k2_funct_1(A_99))=k2_relat_1(A_99) | ~v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.55/3.51  tff(c_68, plain, (![A_33]: (v1_funct_2(A_33, k1_relat_1(A_33), k2_relat_1(A_33)) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.55/3.51  tff(c_2475, plain, (![A_257]: (v1_funct_2(k2_funct_1(A_257), k2_relat_1(A_257), k2_relat_1(k2_funct_1(A_257))) | ~v1_funct_1(k2_funct_1(A_257)) | ~v1_relat_1(k2_funct_1(A_257)) | ~v2_funct_1(A_257) | ~v1_funct_1(A_257) | ~v1_relat_1(A_257))), inference(superposition, [status(thm), theory('equality')], [c_552, c_68])).
% 9.55/3.51  tff(c_2478, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_636, c_2475])).
% 9.55/3.51  tff(c_2486, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_82, c_270, c_2478])).
% 9.55/3.51  tff(c_2487, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2486])).
% 9.55/3.51  tff(c_2490, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_2487])).
% 9.55/3.51  tff(c_2494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_2490])).
% 9.55/3.51  tff(c_2496, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2486])).
% 9.55/3.51  tff(c_584, plain, (![A_101]: (m1_subset_1(A_101, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_101), k2_relat_1(A_101)))) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.55/3.51  tff(c_2638, plain, (![A_269]: (m1_subset_1(k2_funct_1(A_269), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_269), k2_relat_1(k2_funct_1(A_269))))) | ~v1_funct_1(k2_funct_1(A_269)) | ~v1_relat_1(k2_funct_1(A_269)) | ~v2_funct_1(A_269) | ~v1_funct_1(A_269) | ~v1_relat_1(A_269))), inference(superposition, [status(thm), theory('equality')], [c_38, c_584])).
% 9.55/3.51  tff(c_2667, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_636, c_2638])).
% 9.55/3.51  tff(c_2686, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_82, c_2496, c_270, c_2667])).
% 9.55/3.51  tff(c_2715, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_2686])).
% 9.55/3.51  tff(c_2734, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_82, c_1659, c_2715])).
% 9.55/3.51  tff(c_2736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_2734])).
% 9.55/3.51  tff(c_2737, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1655])).
% 9.55/3.51  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.55/3.51  tff(c_1400, plain, (![B_182, A_183]: (m1_subset_1(B_182, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_182), A_183))) | ~r1_tarski(k2_relat_1(B_182), A_183) | ~v1_funct_1(B_182) | ~v1_relat_1(B_182))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.55/3.51  tff(c_1605, plain, (![B_194]: (m1_subset_1(B_194, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_194), k1_xboole_0) | ~v1_funct_1(B_194) | ~v1_relat_1(B_194))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1400])).
% 9.55/3.51  tff(c_1608, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_636, c_1605])).
% 9.55/3.51  tff(c_1613, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_1608])).
% 9.55/3.51  tff(c_1614, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1613])).
% 9.55/3.51  tff(c_2740, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_1614])).
% 9.55/3.51  tff(c_2778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2740])).
% 9.55/3.51  tff(c_2780, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1613])).
% 9.55/3.51  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.55/3.51  tff(c_2799, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_2780, c_2])).
% 9.55/3.51  tff(c_2811, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2799])).
% 9.55/3.51  tff(c_2883, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2811, c_8])).
% 9.55/3.51  tff(c_2881, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2811, c_2811, c_12])).
% 9.55/3.51  tff(c_66, plain, (![A_33]: (m1_subset_1(A_33, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_33), k2_relat_1(A_33)))) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.55/3.51  tff(c_641, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_636, c_66])).
% 9.55/3.51  tff(c_648, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_641])).
% 9.55/3.51  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.55/3.51  tff(c_681, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_648, c_18])).
% 9.55/3.51  tff(c_706, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_681, c_2])).
% 9.55/3.51  tff(c_721, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_706])).
% 9.55/3.51  tff(c_3052, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2881, c_721])).
% 9.55/3.51  tff(c_3062, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2883, c_3052])).
% 9.55/3.51  tff(c_3063, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_706])).
% 9.55/3.51  tff(c_4526, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4518, c_3063])).
% 9.55/3.51  tff(c_126, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.55/3.51  tff(c_133, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_84, c_126])).
% 9.55/3.51  tff(c_329, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.55/3.51  tff(c_344, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_133, c_329])).
% 9.55/3.51  tff(c_429, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_344])).
% 9.55/3.51  tff(c_4571, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_429])).
% 9.55/3.51  tff(c_4576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4571])).
% 9.55/3.51  tff(c_4577, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4514])).
% 9.55/3.51  tff(c_4076, plain, (![B_365, A_366]: (m1_subset_1(B_365, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_365), A_366))) | ~r1_tarski(k2_relat_1(B_365), A_366) | ~v1_funct_1(B_365) | ~v1_relat_1(B_365))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.55/3.51  tff(c_4295, plain, (![B_380]: (m1_subset_1(B_380, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_380), k1_xboole_0) | ~v1_funct_1(B_380) | ~v1_relat_1(B_380))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4076])).
% 9.55/3.51  tff(c_4298, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_636, c_4295])).
% 9.55/3.51  tff(c_4303, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_4298])).
% 9.55/3.51  tff(c_4304, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_4303])).
% 9.55/3.51  tff(c_4585, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4577, c_4304])).
% 9.55/3.51  tff(c_4620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4585])).
% 9.55/3.51  tff(c_4622, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_4303])).
% 9.55/3.51  tff(c_349, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_329])).
% 9.55/3.51  tff(c_4650, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4622, c_349])).
% 9.55/3.51  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.55/3.51  tff(c_3117, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')=k1_xboole_0 | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3063, c_10])).
% 9.55/3.51  tff(c_3800, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_3117])).
% 9.55/3.51  tff(c_4665, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4650, c_3800])).
% 9.55/3.51  tff(c_4686, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4650, c_8])).
% 9.55/3.51  tff(c_4621, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_4303])).
% 9.55/3.51  tff(c_4786, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4650, c_4621])).
% 9.55/3.51  tff(c_4799, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4786, c_18])).
% 9.55/3.51  tff(c_4840, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_4799, c_2])).
% 9.55/3.51  tff(c_4846, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4686, c_4840])).
% 9.55/3.51  tff(c_4848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4665, c_4846])).
% 9.55/3.51  tff(c_4850, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3117])).
% 9.55/3.51  tff(c_4871, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4850, c_8])).
% 9.55/3.51  tff(c_4869, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4850, c_4850, c_12])).
% 9.55/3.51  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.55/3.51  tff(c_4870, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4850, c_4850, c_14])).
% 9.55/3.51  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.55/3.51  tff(c_3097, plain, (![A_275, B_276]: (k1_relset_1(A_275, B_276, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_3065])).
% 9.55/3.51  tff(c_54, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.55/3.51  tff(c_3179, plain, (![C_283, B_284]: (v1_funct_2(C_283, k1_xboole_0, B_284) | k1_relset_1(k1_xboole_0, B_284, C_283)!=k1_xboole_0 | ~m1_subset_1(C_283, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_54])).
% 9.55/3.51  tff(c_3185, plain, (![B_284]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_284) | k1_relset_1(k1_xboole_0, B_284, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_3179])).
% 9.55/3.51  tff(c_3188, plain, (![B_284]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_284) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3097, c_3185])).
% 9.55/3.51  tff(c_3189, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3188])).
% 9.55/3.51  tff(c_136, plain, (![A_45]: (m1_subset_1(k6_partfun1(A_45), k1_zfmisc_1(k2_zfmisc_1(A_45, A_45))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.55/3.51  tff(c_143, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_136])).
% 9.55/3.51  tff(c_152, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_143, c_18])).
% 9.55/3.51  tff(c_333, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_152, c_329])).
% 9.55/3.51  tff(c_343, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_333])).
% 9.55/3.51  tff(c_62, plain, (![A_32]: (v1_partfun1(k6_partfun1(A_32), A_32))), inference(cnfTransformation, [status(thm)], [f_128])).
% 9.55/3.51  tff(c_366, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_343, c_62])).
% 9.55/3.51  tff(c_386, plain, (![B_73, A_74]: (v1_funct_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.55/3.51  tff(c_403, plain, (![A_6]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_16, c_386])).
% 9.55/3.51  tff(c_431, plain, (![A_77]: (~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(splitLeft, [status(thm)], [c_403])).
% 9.55/3.51  tff(c_440, plain, (~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_327, c_431])).
% 9.55/3.51  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_440])).
% 9.55/3.51  tff(c_450, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_403])).
% 9.55/3.51  tff(c_3696, plain, (![C_328, A_329, B_330]: (v1_funct_2(C_328, A_329, B_330) | ~v1_partfun1(C_328, A_329) | ~v1_funct_1(C_328) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.55/3.51  tff(c_3719, plain, (![A_329, B_330]: (v1_funct_2(k1_xboole_0, A_329, B_330) | ~v1_partfun1(k1_xboole_0, A_329) | ~v1_funct_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_3696])).
% 9.55/3.51  tff(c_3738, plain, (![A_331, B_332]: (v1_funct_2(k1_xboole_0, A_331, B_332) | ~v1_partfun1(k1_xboole_0, A_331))), inference(demodulation, [status(thm), theory('equality')], [c_450, c_3719])).
% 9.55/3.51  tff(c_58, plain, (![B_30, C_31]: (k1_relset_1(k1_xboole_0, B_30, C_31)=k1_xboole_0 | ~v1_funct_2(C_31, k1_xboole_0, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.55/3.51  tff(c_91, plain, (![B_30, C_31]: (k1_relset_1(k1_xboole_0, B_30, C_31)=k1_xboole_0 | ~v1_funct_2(C_31, k1_xboole_0, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_58])).
% 9.55/3.51  tff(c_3741, plain, (![B_332]: (k1_relset_1(k1_xboole_0, B_332, k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_3738, c_91])).
% 9.55/3.51  tff(c_3747, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_366, c_16, c_3097, c_3741])).
% 9.55/3.51  tff(c_3749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3189, c_3747])).
% 9.55/3.51  tff(c_3751, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_3188])).
% 9.55/3.51  tff(c_3752, plain, (![A_275, B_276]: (k1_relset_1(A_275, B_276, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3751, c_3097])).
% 9.55/3.51  tff(c_4852, plain, (![A_275, B_276]: (k1_relset_1(A_275, B_276, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4850, c_4850, c_3752])).
% 9.55/3.51  tff(c_4868, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_4850, c_16])).
% 9.55/3.51  tff(c_60, plain, (![B_30, A_29, C_31]: (k1_xboole_0=B_30 | k1_relset_1(A_29, B_30, C_31)=A_29 | ~v1_funct_2(C_31, A_29, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.55/3.51  tff(c_5242, plain, (![B_422, A_423, C_424]: (B_422='#skF_4' | k1_relset_1(A_423, B_422, C_424)=A_423 | ~v1_funct_2(C_424, A_423, B_422) | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(A_423, B_422))))), inference(demodulation, [status(thm), theory('equality')], [c_4850, c_60])).
% 9.55/3.51  tff(c_5255, plain, (![B_422, A_423]: (B_422='#skF_4' | k1_relset_1(A_423, B_422, '#skF_4')=A_423 | ~v1_funct_2('#skF_4', A_423, B_422))), inference(resolution, [status(thm)], [c_4868, c_5242])).
% 9.55/3.51  tff(c_5318, plain, (![B_432, A_433]: (B_432='#skF_4' | A_433='#skF_4' | ~v1_funct_2('#skF_4', A_433, B_432))), inference(demodulation, [status(thm), theory('equality')], [c_4852, c_5255])).
% 9.55/3.51  tff(c_5350, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_86, c_5318])).
% 9.55/3.51  tff(c_5351, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_5350])).
% 9.55/3.51  tff(c_5352, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5351, c_429])).
% 9.55/3.51  tff(c_5358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4870, c_5352])).
% 9.55/3.51  tff(c_5359, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_5350])).
% 9.55/3.51  tff(c_5398, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5359, c_429])).
% 9.55/3.51  tff(c_5404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4871, c_4869, c_5398])).
% 9.55/3.51  tff(c_5405, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_344])).
% 9.55/3.51  tff(c_5408, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5405, c_84])).
% 9.55/3.51  tff(c_5590, plain, (![A_462, B_463, C_464]: (k1_relset_1(A_462, B_463, C_464)=k1_relat_1(C_464) | ~m1_subset_1(C_464, k1_zfmisc_1(k2_zfmisc_1(A_462, B_463))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.55/3.51  tff(c_5704, plain, (![C_477]: (k1_relset_1('#skF_2', '#skF_3', C_477)=k1_relat_1(C_477) | ~m1_subset_1(C_477, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5405, c_5590])).
% 9.55/3.51  tff(c_5716, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5408, c_5704])).
% 9.55/3.51  tff(c_7735, plain, (![B_615, A_616, C_617]: (k1_xboole_0=B_615 | k1_relset_1(A_616, B_615, C_617)=A_616 | ~v1_funct_2(C_617, A_616, B_615) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(A_616, B_615))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.55/3.51  tff(c_7747, plain, (![C_617]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_617)='#skF_2' | ~v1_funct_2(C_617, '#skF_2', '#skF_3') | ~m1_subset_1(C_617, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5405, c_7735])).
% 9.55/3.51  tff(c_7840, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_7747])).
% 9.55/3.51  tff(c_5835, plain, (![A_488, B_489, C_490]: (k2_relset_1(A_488, B_489, C_490)=k2_relat_1(C_490) | ~m1_subset_1(C_490, k1_zfmisc_1(k2_zfmisc_1(A_488, B_489))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.55/3.51  tff(c_5883, plain, (![C_494]: (k2_relset_1('#skF_2', '#skF_3', C_494)=k2_relat_1(C_494) | ~m1_subset_1(C_494, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5405, c_5835])).
% 9.55/3.51  tff(c_5886, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_5408, c_5883])).
% 9.55/3.51  tff(c_5896, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5886])).
% 9.55/3.51  tff(c_7639, plain, (![B_603, A_604]: (m1_subset_1(B_603, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_603), A_604))) | ~r1_tarski(k2_relat_1(B_603), A_604) | ~v1_funct_1(B_603) | ~v1_relat_1(B_603))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.55/3.51  tff(c_7686, plain, (![B_605]: (m1_subset_1(B_605, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(B_605), k1_xboole_0) | ~v1_funct_1(B_605) | ~v1_relat_1(B_605))), inference(superposition, [status(thm), theory('equality')], [c_12, c_7639])).
% 9.55/3.51  tff(c_7689, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5896, c_7686])).
% 9.55/3.51  tff(c_7694, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_7689])).
% 9.55/3.51  tff(c_7695, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7694])).
% 9.55/3.51  tff(c_7848, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7840, c_7695])).
% 9.55/3.51  tff(c_7884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7848])).
% 9.55/3.51  tff(c_8014, plain, (![C_629]: (k1_relset_1('#skF_2', '#skF_3', C_629)='#skF_2' | ~v1_funct_2(C_629, '#skF_2', '#skF_3') | ~m1_subset_1(C_629, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_7747])).
% 9.55/3.51  tff(c_8017, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_5408, c_8014])).
% 9.55/3.51  tff(c_8028, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_5716, c_8017])).
% 9.55/3.51  tff(c_5578, plain, (![A_461]: (k1_relat_1(k2_funct_1(A_461))=k2_relat_1(A_461) | ~v2_funct_1(A_461) | ~v1_funct_1(A_461) | ~v1_relat_1(A_461))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.55/3.51  tff(c_8937, plain, (![A_688]: (v1_funct_2(k2_funct_1(A_688), k2_relat_1(A_688), k2_relat_1(k2_funct_1(A_688))) | ~v1_funct_1(k2_funct_1(A_688)) | ~v1_relat_1(k2_funct_1(A_688)) | ~v2_funct_1(A_688) | ~v1_funct_1(A_688) | ~v1_relat_1(A_688))), inference(superposition, [status(thm), theory('equality')], [c_5578, c_68])).
% 9.55/3.51  tff(c_8940, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5896, c_8937])).
% 9.55/3.51  tff(c_8948, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_82, c_270, c_8940])).
% 9.55/3.51  tff(c_8949, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8948])).
% 9.55/3.51  tff(c_8952, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_8949])).
% 9.55/3.51  tff(c_8956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_8952])).
% 9.55/3.51  tff(c_8958, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8948])).
% 9.55/3.51  tff(c_5665, plain, (![A_474]: (m1_subset_1(A_474, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_474), k2_relat_1(A_474)))) | ~v1_funct_1(A_474) | ~v1_relat_1(A_474))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.55/3.51  tff(c_5786, plain, (![A_484]: (r1_tarski(A_484, k2_zfmisc_1(k1_relat_1(A_484), k2_relat_1(A_484))) | ~v1_funct_1(A_484) | ~v1_relat_1(A_484))), inference(resolution, [status(thm)], [c_5665, c_18])).
% 9.55/3.51  tff(c_9034, plain, (![A_692]: (r1_tarski(k2_funct_1(A_692), k2_zfmisc_1(k2_relat_1(A_692), k2_relat_1(k2_funct_1(A_692)))) | ~v1_funct_1(k2_funct_1(A_692)) | ~v1_relat_1(k2_funct_1(A_692)) | ~v2_funct_1(A_692) | ~v1_funct_1(A_692) | ~v1_relat_1(A_692))), inference(superposition, [status(thm), theory('equality')], [c_38, c_5786])).
% 9.55/3.51  tff(c_9060, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5896, c_9034])).
% 9.55/3.51  tff(c_9078, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_82, c_8958, c_270, c_9060])).
% 9.55/3.51  tff(c_9104, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36, c_9078])).
% 9.55/3.51  tff(c_9122, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_82, c_8028, c_9104])).
% 9.55/3.51  tff(c_9124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_294, c_9122])).
% 9.55/3.51  tff(c_9126, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_7694])).
% 9.55/3.51  tff(c_9154, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_9126, c_349])).
% 9.55/3.51  tff(c_5415, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5405, c_10])).
% 9.55/3.51  tff(c_5452, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_5415])).
% 9.55/3.51  tff(c_9217, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9154, c_5452])).
% 9.55/3.51  tff(c_9230, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9154, c_8])).
% 9.55/3.51  tff(c_9125, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_7694])).
% 9.55/3.51  tff(c_9357, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9154, c_9125])).
% 9.55/3.51  tff(c_9370, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_9357, c_18])).
% 9.55/3.51  tff(c_9403, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_9370, c_2])).
% 9.55/3.51  tff(c_9409, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9230, c_9403])).
% 9.55/3.51  tff(c_9411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9217, c_9409])).
% 9.55/3.51  tff(c_9413, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5415])).
% 9.55/3.51  tff(c_9426, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9413, c_8])).
% 9.55/3.51  tff(c_9423, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_9413, c_16])).
% 9.55/3.51  tff(c_11780, plain, (![A_936, B_937, C_938]: (k1_relset_1(A_936, B_937, C_938)=k1_relat_1(C_938) | ~m1_subset_1(C_938, k1_zfmisc_1(k2_zfmisc_1(A_936, B_937))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.55/3.51  tff(c_11798, plain, (![A_936, B_937]: (k1_relset_1(A_936, B_937, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9423, c_11780])).
% 9.55/3.51  tff(c_9729, plain, (![A_734, B_735, C_736]: (k2_relset_1(A_734, B_735, C_736)=k2_relat_1(C_736) | ~m1_subset_1(C_736, k1_zfmisc_1(k2_zfmisc_1(A_734, B_735))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.55/3.51  tff(c_9750, plain, (![A_737, B_738]: (k2_relset_1(A_737, B_738, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9423, c_9729])).
% 9.55/3.51  tff(c_9412, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5415])).
% 9.55/3.51  tff(c_9465, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9413, c_9413, c_9412])).
% 9.55/3.51  tff(c_9466, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_9465])).
% 9.55/3.51  tff(c_9470, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9466, c_9466, c_80])).
% 9.55/3.51  tff(c_9754, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_9750, c_9470])).
% 9.55/3.51  tff(c_9649, plain, (![A_722]: (k1_relat_1(k2_funct_1(A_722))=k2_relat_1(A_722) | ~v2_funct_1(A_722) | ~v1_funct_1(A_722) | ~v1_relat_1(A_722))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.55/3.51  tff(c_11389, plain, (![A_894]: (v1_funct_2(k2_funct_1(A_894), k2_relat_1(A_894), k2_relat_1(k2_funct_1(A_894))) | ~v1_funct_1(k2_funct_1(A_894)) | ~v1_relat_1(k2_funct_1(A_894)) | ~v2_funct_1(A_894) | ~v1_funct_1(A_894) | ~v1_relat_1(A_894))), inference(superposition, [status(thm), theory('equality')], [c_9649, c_68])).
% 9.55/3.51  tff(c_11392, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9754, c_11389])).
% 9.55/3.51  tff(c_11400, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_82, c_270, c_11392])).
% 9.55/3.51  tff(c_11401, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_11400])).
% 9.55/3.51  tff(c_11404, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_11401])).
% 9.55/3.51  tff(c_11408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_11404])).
% 9.55/3.51  tff(c_11410, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_11400])).
% 9.55/3.51  tff(c_9874, plain, (![A_751, B_752, C_753]: (k1_relset_1(A_751, B_752, C_753)=k1_relat_1(C_753) | ~m1_subset_1(C_753, k1_zfmisc_1(k2_zfmisc_1(A_751, B_752))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.55/3.51  tff(c_9896, plain, (![A_751, B_752]: (k1_relset_1(A_751, B_752, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9423, c_9874])).
% 9.55/3.51  tff(c_92, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_54])).
% 9.55/3.51  tff(c_9951, plain, (![C_763, B_764]: (v1_funct_2(C_763, '#skF_4', B_764) | k1_relset_1('#skF_4', B_764, C_763)!='#skF_4' | ~m1_subset_1(C_763, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9413, c_9413, c_9413, c_9413, c_92])).
% 9.55/3.51  tff(c_9954, plain, (![B_764]: (v1_funct_2('#skF_4', '#skF_4', B_764) | k1_relset_1('#skF_4', B_764, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_9423, c_9951])).
% 9.55/3.51  tff(c_9959, plain, (![B_764]: (v1_funct_2('#skF_4', '#skF_4', B_764) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9896, c_9954])).
% 9.55/3.51  tff(c_9961, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_9959])).
% 9.55/3.51  tff(c_9418, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9413, c_9413, c_366])).
% 9.55/3.51  tff(c_10261, plain, (![C_793, A_794, B_795]: (v1_funct_2(C_793, A_794, B_795) | ~v1_partfun1(C_793, A_794) | ~v1_funct_1(C_793) | ~m1_subset_1(C_793, k1_zfmisc_1(k2_zfmisc_1(A_794, B_795))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.55/3.51  tff(c_10274, plain, (![A_794, B_795]: (v1_funct_2('#skF_4', A_794, B_795) | ~v1_partfun1('#skF_4', A_794) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_9423, c_10261])).
% 9.55/3.51  tff(c_10294, plain, (![A_796, B_797]: (v1_funct_2('#skF_4', A_796, B_797) | ~v1_partfun1('#skF_4', A_796))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_10274])).
% 9.55/3.51  tff(c_10094, plain, (![B_30, C_31]: (k1_relset_1('#skF_4', B_30, C_31)='#skF_4' | ~v1_funct_2(C_31, '#skF_4', B_30) | ~m1_subset_1(C_31, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9413, c_9413, c_9413, c_9413, c_91])).
% 9.55/3.51  tff(c_10297, plain, (![B_797]: (k1_relset_1('#skF_4', B_797, '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_partfun1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_10294, c_10094])).
% 9.55/3.51  tff(c_10303, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9418, c_9423, c_9896, c_10297])).
% 9.55/3.51  tff(c_10305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9961, c_10303])).
% 9.55/3.51  tff(c_10307, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_9959])).
% 9.55/3.51  tff(c_9424, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9413, c_9413, c_12])).
% 9.55/3.51  tff(c_10652, plain, (![B_830, A_831]: (m1_subset_1(B_830, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_830), A_831))) | ~r1_tarski(k2_relat_1(B_830), A_831) | ~v1_funct_1(B_830) | ~v1_relat_1(B_830))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.55/3.51  tff(c_10976, plain, (![B_856, A_857]: (r1_tarski(B_856, k2_zfmisc_1(k1_relat_1(B_856), A_857)) | ~r1_tarski(k2_relat_1(B_856), A_857) | ~v1_funct_1(B_856) | ~v1_relat_1(B_856))), inference(resolution, [status(thm)], [c_10652, c_18])).
% 9.55/3.51  tff(c_11433, plain, (![B_895, A_896]: (k2_zfmisc_1(k1_relat_1(B_895), A_896)=B_895 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(B_895), A_896), B_895) | ~r1_tarski(k2_relat_1(B_895), A_896) | ~v1_funct_1(B_895) | ~v1_relat_1(B_895))), inference(resolution, [status(thm)], [c_10976, c_2])).
% 9.55/3.51  tff(c_11443, plain, (![B_895]: (k2_zfmisc_1(k1_relat_1(B_895), '#skF_4')=B_895 | ~r1_tarski('#skF_4', B_895) | ~r1_tarski(k2_relat_1(B_895), '#skF_4') | ~v1_funct_1(B_895) | ~v1_relat_1(B_895))), inference(superposition, [status(thm), theory('equality')], [c_9424, c_11433])).
% 9.55/3.51  tff(c_11448, plain, (![B_897]: (B_897='#skF_4' | ~r1_tarski(k2_relat_1(B_897), '#skF_4') | ~v1_funct_1(B_897) | ~v1_relat_1(B_897))), inference(demodulation, [status(thm), theory('equality')], [c_9426, c_9424, c_11443])).
% 9.55/3.51  tff(c_11458, plain, (![A_898]: (k2_funct_1(A_898)='#skF_4' | ~r1_tarski(k1_relat_1(A_898), '#skF_4') | ~v1_funct_1(k2_funct_1(A_898)) | ~v1_relat_1(k2_funct_1(A_898)) | ~v2_funct_1(A_898) | ~v1_funct_1(A_898) | ~v1_relat_1(A_898))), inference(superposition, [status(thm), theory('equality')], [c_36, c_11448])).
% 9.55/3.51  tff(c_11461, plain, (k2_funct_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10307, c_11458])).
% 9.55/3.51  tff(c_11466, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_82, c_11410, c_270, c_9426, c_11461])).
% 9.55/3.51  tff(c_9425, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9413, c_9413, c_14])).
% 9.55/3.51  tff(c_9469, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9466, c_272])).
% 9.55/3.51  tff(c_9590, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9425, c_9469])).
% 9.55/3.51  tff(c_9594, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_20, c_9590])).
% 9.55/3.51  tff(c_11482, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11466, c_9594])).
% 9.55/3.51  tff(c_11490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9426, c_11482])).
% 9.55/3.51  tff(c_11491, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_9465])).
% 9.55/3.51  tff(c_11497, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11491, c_86])).
% 9.55/3.51  tff(c_12085, plain, (![B_975, C_976]: (k1_relset_1('#skF_4', B_975, C_976)='#skF_4' | ~v1_funct_2(C_976, '#skF_4', B_975) | ~m1_subset_1(C_976, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9413, c_9413, c_9413, c_9413, c_91])).
% 9.55/3.51  tff(c_12090, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_11497, c_12085])).
% 9.55/3.51  tff(c_12097, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9423, c_11798, c_12090])).
% 9.55/3.51  tff(c_11630, plain, (![A_912]: (k2_relat_1(k2_funct_1(A_912))=k1_relat_1(A_912) | ~v2_funct_1(A_912) | ~v1_funct_1(A_912) | ~v1_relat_1(A_912))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.55/3.51  tff(c_13039, plain, (![A_1054]: (v1_funct_2(k2_funct_1(A_1054), k1_relat_1(k2_funct_1(A_1054)), k1_relat_1(A_1054)) | ~v1_funct_1(k2_funct_1(A_1054)) | ~v1_relat_1(k2_funct_1(A_1054)) | ~v2_funct_1(A_1054) | ~v1_funct_1(A_1054) | ~v1_relat_1(A_1054))), inference(superposition, [status(thm), theory('equality')], [c_11630, c_68])).
% 9.55/3.51  tff(c_13042, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12097, c_13039])).
% 9.55/3.51  tff(c_13050, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_82, c_270, c_13042])).
% 9.55/3.51  tff(c_13051, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_13050])).
% 9.55/3.51  tff(c_13054, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_13051])).
% 9.55/3.51  tff(c_13058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_13054])).
% 9.55/3.51  tff(c_13060, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_13050])).
% 9.55/3.51  tff(c_12338, plain, (![B_992, A_993]: (m1_subset_1(B_992, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_992), A_993))) | ~r1_tarski(k2_relat_1(B_992), A_993) | ~v1_funct_1(B_992) | ~v1_relat_1(B_992))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.55/3.51  tff(c_12693, plain, (![B_1024, A_1025]: (r1_tarski(B_1024, k2_zfmisc_1(k1_relat_1(B_1024), A_1025)) | ~r1_tarski(k2_relat_1(B_1024), A_1025) | ~v1_funct_1(B_1024) | ~v1_relat_1(B_1024))), inference(resolution, [status(thm)], [c_12338, c_18])).
% 9.55/3.51  tff(c_13167, plain, (![B_1064, A_1065]: (k2_zfmisc_1(k1_relat_1(B_1064), A_1065)=B_1064 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(B_1064), A_1065), B_1064) | ~r1_tarski(k2_relat_1(B_1064), A_1065) | ~v1_funct_1(B_1064) | ~v1_relat_1(B_1064))), inference(resolution, [status(thm)], [c_12693, c_2])).
% 9.55/3.51  tff(c_13177, plain, (![B_1064]: (k2_zfmisc_1(k1_relat_1(B_1064), '#skF_4')=B_1064 | ~r1_tarski('#skF_4', B_1064) | ~r1_tarski(k2_relat_1(B_1064), '#skF_4') | ~v1_funct_1(B_1064) | ~v1_relat_1(B_1064))), inference(superposition, [status(thm), theory('equality')], [c_9424, c_13167])).
% 9.55/3.51  tff(c_13182, plain, (![B_1066]: (B_1066='#skF_4' | ~r1_tarski(k2_relat_1(B_1066), '#skF_4') | ~v1_funct_1(B_1066) | ~v1_relat_1(B_1066))), inference(demodulation, [status(thm), theory('equality')], [c_9426, c_9424, c_13177])).
% 9.55/3.51  tff(c_13192, plain, (![A_1067]: (k2_funct_1(A_1067)='#skF_4' | ~r1_tarski(k1_relat_1(A_1067), '#skF_4') | ~v1_funct_1(k2_funct_1(A_1067)) | ~v1_relat_1(k2_funct_1(A_1067)) | ~v2_funct_1(A_1067) | ~v1_funct_1(A_1067) | ~v1_relat_1(A_1067))), inference(superposition, [status(thm), theory('equality')], [c_36, c_13182])).
% 9.55/3.51  tff(c_13195, plain, (k2_funct_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12097, c_13192])).
% 9.55/3.51  tff(c_13200, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_327, c_88, c_82, c_13060, c_270, c_9426, c_13195])).
% 9.55/3.51  tff(c_11495, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11491, c_272])).
% 9.55/3.51  tff(c_11619, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9424, c_11495])).
% 9.55/3.51  tff(c_11623, plain, (~r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_20, c_11619])).
% 9.55/3.51  tff(c_13205, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13200, c_11623])).
% 9.55/3.51  tff(c_13213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9426, c_13205])).
% 9.55/3.51  tff(c_13214, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_269])).
% 9.55/3.51  tff(c_13215, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_269])).
% 9.55/3.51  tff(c_13828, plain, (![A_1133, B_1134, C_1135]: (k1_relset_1(A_1133, B_1134, C_1135)=k1_relat_1(C_1135) | ~m1_subset_1(C_1135, k1_zfmisc_1(k2_zfmisc_1(A_1133, B_1134))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.55/3.51  tff(c_13861, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_13215, c_13828])).
% 9.55/3.51  tff(c_14412, plain, (![B_1189, C_1190, A_1191]: (k1_xboole_0=B_1189 | v1_funct_2(C_1190, A_1191, B_1189) | k1_relset_1(A_1191, B_1189, C_1190)!=A_1191 | ~m1_subset_1(C_1190, k1_zfmisc_1(k2_zfmisc_1(A_1191, B_1189))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.55/3.51  tff(c_14428, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_13215, c_14412])).
% 9.55/3.51  tff(c_14452, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13861, c_14428])).
% 9.55/3.51  tff(c_14453, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_13214, c_14452])).
% 9.55/3.51  tff(c_14461, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_14453])).
% 9.55/3.51  tff(c_14464, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_14461])).
% 9.55/3.51  tff(c_14467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13319, c_88, c_82, c_13591, c_14464])).
% 9.55/3.51  tff(c_14468, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14453])).
% 9.55/3.51  tff(c_14504, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_14468, c_8])).
% 9.55/3.51  tff(c_14503, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14468, c_14468, c_14])).
% 9.55/3.51  tff(c_13238, plain, (![B_1073, A_1074]: (B_1073=A_1074 | ~r1_tarski(B_1073, A_1074) | ~r1_tarski(A_1074, B_1073))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.55/3.51  tff(c_13256, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_133, c_13238])).
% 9.55/3.51  tff(c_13332, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_13256])).
% 9.55/3.51  tff(c_14752, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14503, c_13332])).
% 9.55/3.51  tff(c_14757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14504, c_14752])).
% 9.55/3.51  tff(c_14758, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_13256])).
% 9.55/3.51  tff(c_14765, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14758, c_84])).
% 9.55/3.51  tff(c_15214, plain, (![A_1252, B_1253, C_1254]: (k2_relset_1(A_1252, B_1253, C_1254)=k2_relat_1(C_1254) | ~m1_subset_1(C_1254, k1_zfmisc_1(k2_zfmisc_1(A_1252, B_1253))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.55/3.51  tff(c_15308, plain, (![C_1261]: (k2_relset_1('#skF_2', '#skF_3', C_1261)=k2_relat_1(C_1261) | ~m1_subset_1(C_1261, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_14758, c_15214])).
% 9.55/3.51  tff(c_15311, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14765, c_15308])).
% 9.55/3.51  tff(c_15321, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_15311])).
% 9.55/3.51  tff(c_15007, plain, (![A_1228, B_1229, C_1230]: (k1_relset_1(A_1228, B_1229, C_1230)=k1_relat_1(C_1230) | ~m1_subset_1(C_1230, k1_zfmisc_1(k2_zfmisc_1(A_1228, B_1229))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.55/3.51  tff(c_15032, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_13215, c_15007])).
% 9.55/3.51  tff(c_16214, plain, (![B_1329, C_1330, A_1331]: (k1_xboole_0=B_1329 | v1_funct_2(C_1330, A_1331, B_1329) | k1_relset_1(A_1331, B_1329, C_1330)!=A_1331 | ~m1_subset_1(C_1330, k1_zfmisc_1(k2_zfmisc_1(A_1331, B_1329))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.55/3.51  tff(c_16233, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_13215, c_16214])).
% 9.55/3.51  tff(c_16254, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15032, c_16233])).
% 9.55/3.51  tff(c_16255, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_13214, c_16254])).
% 9.55/3.51  tff(c_16261, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_16255])).
% 9.55/3.51  tff(c_16264, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_16261])).
% 9.55/3.51  tff(c_16267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13319, c_88, c_82, c_15321, c_16264])).
% 9.55/3.51  tff(c_16268, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_16255])).
% 9.55/3.51  tff(c_14770, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_14758, c_10])).
% 9.55/3.51  tff(c_14884, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_14770])).
% 9.55/3.51  tff(c_16299, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16268, c_14884])).
% 9.55/3.51  tff(c_16449, plain, (![B_1333]: (k2_zfmisc_1('#skF_2', B_1333)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16268, c_16268, c_14])).
% 9.55/3.51  tff(c_16486, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_16449, c_14758])).
% 9.55/3.51  tff(c_16510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16299, c_16486])).
% 9.55/3.51  tff(c_16512, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_14770])).
% 9.55/3.51  tff(c_16525, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_16512, c_8])).
% 9.55/3.51  tff(c_16524, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16512, c_16512, c_14])).
% 9.55/3.51  tff(c_16511, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_14770])).
% 9.55/3.51  tff(c_16858, plain, ('#skF_2'='#skF_4' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16512, c_16512, c_16511])).
% 9.55/3.51  tff(c_16859, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_16858])).
% 9.55/3.51  tff(c_13231, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_13215, c_18])).
% 9.55/3.51  tff(c_16861, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16859, c_13231])).
% 9.55/3.51  tff(c_16867, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16524, c_16861])).
% 9.55/3.51  tff(c_16904, plain, (k2_funct_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_16867, c_2])).
% 9.55/3.51  tff(c_16909, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16525, c_16904])).
% 9.55/3.51  tff(c_16953, plain, (![A_1357]: (k1_relat_1(k2_funct_1(A_1357))=k2_relat_1(A_1357) | ~v2_funct_1(A_1357) | ~v1_funct_1(A_1357) | ~v1_relat_1(A_1357))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.55/3.51  tff(c_16965, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16909, c_16953])).
% 9.55/3.51  tff(c_16969, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13319, c_88, c_82, c_16965])).
% 9.55/3.51  tff(c_16522, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_16512, c_16])).
% 9.55/3.51  tff(c_17135, plain, (![A_1387, B_1388, C_1389]: (k2_relset_1(A_1387, B_1388, C_1389)=k2_relat_1(C_1389) | ~m1_subset_1(C_1389, k1_zfmisc_1(k2_zfmisc_1(A_1387, B_1388))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.55/3.51  tff(c_17139, plain, (![A_1387, B_1388]: (k2_relset_1(A_1387, B_1388, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_16522, c_17135])).
% 9.55/3.51  tff(c_17157, plain, (![A_1390, B_1391]: (k2_relset_1(A_1390, B_1391, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16969, c_17139])).
% 9.55/3.51  tff(c_16864, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16859, c_16859, c_80])).
% 9.55/3.51  tff(c_17161, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_17157, c_16864])).
% 9.55/3.51  tff(c_17069, plain, (![A_1375, B_1376, C_1377]: (k1_relset_1(A_1375, B_1376, C_1377)=k1_relat_1(C_1377) | ~m1_subset_1(C_1377, k1_zfmisc_1(k2_zfmisc_1(A_1375, B_1376))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.55/3.51  tff(c_17087, plain, (![A_1375, B_1376]: (k1_relset_1(A_1375, B_1376, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_16522, c_17069])).
% 9.55/3.51  tff(c_17169, plain, (![A_1375, B_1376]: (k1_relset_1(A_1375, B_1376, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17161, c_17087])).
% 9.55/3.51  tff(c_17348, plain, (![C_1412, B_1413]: (v1_funct_2(C_1412, '#skF_4', B_1413) | k1_relset_1('#skF_4', B_1413, C_1412)!='#skF_4' | ~m1_subset_1(C_1412, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16512, c_16512, c_16512, c_16512, c_92])).
% 9.55/3.51  tff(c_17351, plain, (![B_1413]: (v1_funct_2('#skF_4', '#skF_4', B_1413) | k1_relset_1('#skF_4', B_1413, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_16522, c_17348])).
% 9.55/3.51  tff(c_17357, plain, (![B_1413]: (v1_funct_2('#skF_4', '#skF_4', B_1413))), inference(demodulation, [status(thm), theory('equality')], [c_17169, c_17351])).
% 9.55/3.51  tff(c_16863, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16859, c_13214])).
% 9.55/3.51  tff(c_16950, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16909, c_16863])).
% 9.55/3.51  tff(c_17362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17357, c_16950])).
% 9.55/3.51  tff(c_17364, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_16858])).
% 9.55/3.51  tff(c_50, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_29, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 9.55/3.51  tff(c_90, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 9.55/3.51  tff(c_17459, plain, (![A_1417]: (v1_funct_2('#skF_4', A_1417, '#skF_4') | A_1417='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16512, c_16512, c_16512, c_90])).
% 9.55/3.51  tff(c_16523, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16512, c_16512, c_12])).
% 9.55/3.51  tff(c_17363, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_16858])).
% 9.55/3.51  tff(c_17366, plain, (r1_tarski(k2_funct_1('#skF_4'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17363, c_13231])).
% 9.55/3.51  tff(c_17372, plain, (r1_tarski(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16523, c_17366])).
% 9.55/3.51  tff(c_17409, plain, (k2_funct_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_17372, c_2])).
% 9.55/3.51  tff(c_17414, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16525, c_17409])).
% 9.55/3.51  tff(c_17368, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17363, c_13214])).
% 9.55/3.51  tff(c_17451, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17414, c_17368])).
% 9.55/3.51  tff(c_17462, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_17459, c_17451])).
% 9.55/3.51  tff(c_17466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17364, c_17462])).
% 9.55/3.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.55/3.51  
% 9.55/3.51  Inference rules
% 9.55/3.51  ----------------------
% 9.55/3.51  #Ref     : 0
% 9.55/3.51  #Sup     : 3519
% 9.55/3.51  #Fact    : 0
% 9.55/3.51  #Define  : 0
% 9.55/3.51  #Split   : 65
% 9.55/3.51  #Chain   : 0
% 9.55/3.51  #Close   : 0
% 9.55/3.51  
% 9.55/3.51  Ordering : KBO
% 9.55/3.51  
% 9.55/3.51  Simplification rules
% 9.55/3.51  ----------------------
% 9.55/3.51  #Subsume      : 527
% 9.55/3.51  #Demod        : 5108
% 9.55/3.51  #Tautology    : 1905
% 9.55/3.51  #SimpNegUnit  : 47
% 9.55/3.51  #BackRed      : 596
% 9.55/3.51  
% 9.55/3.51  #Partial instantiations: 0
% 9.55/3.51  #Strategies tried      : 1
% 9.55/3.51  
% 9.55/3.51  Timing (in seconds)
% 9.55/3.51  ----------------------
% 9.55/3.51  Preprocessing        : 0.39
% 9.55/3.51  Parsing              : 0.20
% 9.55/3.52  CNF conversion       : 0.03
% 9.55/3.52  Main loop            : 2.19
% 9.55/3.52  Inferencing          : 0.74
% 9.55/3.52  Reduction            : 0.81
% 9.55/3.52  Demodulation         : 0.59
% 9.55/3.52  BG Simplification    : 0.07
% 9.55/3.52  Subsumption          : 0.39
% 9.55/3.52  Abstraction          : 0.09
% 9.55/3.52  MUC search           : 0.00
% 9.55/3.52  Cooper               : 0.00
% 9.55/3.52  Total                : 2.71
% 9.55/3.52  Index Insertion      : 0.00
% 9.55/3.52  Index Deletion       : 0.00
% 9.55/3.52  Index Matching       : 0.00
% 9.55/3.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
