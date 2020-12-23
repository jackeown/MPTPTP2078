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
% DateTime   : Thu Dec  3 10:12:45 EST 2020

% Result     : Theorem 10.17s
% Output     : CNFRefutation 10.58s
% Verified   : 
% Statistics : Number of formulae       :  462 (6372 expanded)
%              Number of leaves         :   38 (1933 expanded)
%              Depth                    :   23
%              Number of atoms          :  769 (16634 expanded)
%              Number of equality atoms :  290 (5986 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_143,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_160,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_143])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_12] :
      ( v1_funct_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_162,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_165,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_162])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_165])).

tff(c_170,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_197,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_201,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_197])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_403,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_430,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_403])).

tff(c_4334,plain,(
    ! [B_343,A_344,C_345] :
      ( k1_xboole_0 = B_343
      | k1_relset_1(A_344,B_343,C_345) = A_344
      | ~ v1_funct_2(C_345,A_344,B_343)
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(A_344,B_343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4351,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_4334])).

tff(c_4367,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_430,c_4351])).

tff(c_4371,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4367])).

tff(c_3849,plain,(
    ! [A_307,B_308,C_309] :
      ( m1_subset_1(k1_relset_1(A_307,B_308,C_309),k1_zfmisc_1(A_307))
      | ~ m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_307,B_308))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3892,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_3849])).

tff(c_3912,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3892])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3965,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3912,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4030,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3965,c_2])).

tff(c_4082,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4030])).

tff(c_4375,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4371,c_4082])).

tff(c_4387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4375])).

tff(c_4388,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4367])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_121,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_109])).

tff(c_4416,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4388,c_121])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4418,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4388,c_4388,c_10])).

tff(c_120,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_109])).

tff(c_230,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_237,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_230])).

tff(c_268,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_4573,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4418,c_268])).

tff(c_4579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4416,c_4573])).

tff(c_4580,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4030])).

tff(c_298,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_305,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_298])).

tff(c_318,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_305])).

tff(c_32,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_271,plain,(
    ! [A_70] :
      ( k1_relat_1(k2_funct_1(A_70)) = k2_relat_1(A_70)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    ! [A_11] :
      ( k9_relat_1(A_11,k1_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3475,plain,(
    ! [A_290] :
      ( k9_relat_1(k2_funct_1(A_290),k2_relat_1(A_290)) = k2_relat_1(k2_funct_1(A_290))
      | ~ v1_relat_1(k2_funct_1(A_290))
      | ~ v2_funct_1(A_290)
      | ~ v1_funct_1(A_290)
      | ~ v1_relat_1(A_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_22])).

tff(c_3491,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_3475])).

tff(c_3498,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_3491])).

tff(c_3499,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3498])).

tff(c_3502,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_3499])).

tff(c_3506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_3502])).

tff(c_3508,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3498])).

tff(c_171,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_802,plain,(
    ! [B_118,A_119,C_120] :
      ( k1_xboole_0 = B_118
      | k1_relset_1(A_119,B_118,C_120) = A_119
      | ~ v1_funct_2(C_120,A_119,B_118)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_819,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_802])).

tff(c_838,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_430,c_819])).

tff(c_842,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_838])).

tff(c_529,plain,(
    ! [A_102,B_103,C_104] :
      ( m1_subset_1(k1_relset_1(A_102,B_103,C_104),k1_zfmisc_1(A_102))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_571,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_529])).

tff(c_592,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_571])).

tff(c_724,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_592,c_16])).

tff(c_727,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_724,c_2])).

tff(c_754,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_727])).

tff(c_844,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_754])).

tff(c_859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_844])).

tff(c_860,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_838])).

tff(c_886,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_121])).

tff(c_888,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_860,c_10])).

tff(c_336,plain,(
    ! [A_77] :
      ( m1_subset_1(A_77,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_77),k2_relat_1(A_77))))
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_350,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_336])).

tff(c_362,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_350])).

tff(c_379,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_362,c_16])).

tff(c_389,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_379,c_2])).

tff(c_447,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_953,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_447])).

tff(c_963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_953])).

tff(c_964,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_727])).

tff(c_3507,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3498])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( k9_relat_1(k2_funct_1(B_14),A_13) = k10_relat_1(B_14,A_13)
      | ~ v2_funct_1(B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3512,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3507,c_28])).

tff(c_3519,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_3512])).

tff(c_30,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3548,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3519,c_30])).

tff(c_3572,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_964,c_3548])).

tff(c_3578,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3572,c_3519])).

tff(c_360,plain,(
    ! [A_77] :
      ( r1_tarski(A_77,k2_zfmisc_1(k1_relat_1(A_77),k2_relat_1(A_77)))
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(resolution,[status(thm)],[c_336,c_16])).

tff(c_3602,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3578,c_360])).

tff(c_3628,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3508,c_171,c_3602])).

tff(c_3717,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_3628])).

tff(c_3730,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_318,c_3717])).

tff(c_3732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_3730])).

tff(c_3733,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_4586,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4580,c_3733])).

tff(c_4631,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4586,c_268])).

tff(c_4637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4631])).

tff(c_4638,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_4642,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4638,c_66])).

tff(c_4901,plain,(
    ! [A_384,B_385,C_386] :
      ( k2_relset_1(A_384,B_385,C_386) = k2_relat_1(C_386)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4991,plain,(
    ! [C_399] :
      ( k2_relset_1('#skF_1','#skF_2',C_399) = k2_relat_1(C_399)
      | ~ m1_subset_1(C_399,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4638,c_4901])).

tff(c_4994,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4642,c_4991])).

tff(c_5004,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4994])).

tff(c_4713,plain,(
    ! [A_360] :
      ( k1_relat_1(k2_funct_1(A_360)) = k2_relat_1(A_360)
      | ~ v2_funct_1(A_360)
      | ~ v1_funct_1(A_360)
      | ~ v1_relat_1(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_11099,plain,(
    ! [A_740] :
      ( k9_relat_1(k2_funct_1(A_740),k2_relat_1(A_740)) = k2_relat_1(k2_funct_1(A_740))
      | ~ v1_relat_1(k2_funct_1(A_740))
      | ~ v2_funct_1(A_740)
      | ~ v1_funct_1(A_740)
      | ~ v1_relat_1(A_740) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4713,c_22])).

tff(c_11111,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5004,c_11099])).

tff(c_11122,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_11111])).

tff(c_11123,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_11122])).

tff(c_11126,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_11123])).

tff(c_11130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_11126])).

tff(c_11132,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11122])).

tff(c_4728,plain,(
    ! [A_361,B_362,C_363] :
      ( k1_relset_1(A_361,B_362,C_363) = k1_relat_1(C_363)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_361,B_362))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4765,plain,(
    ! [C_368] :
      ( k1_relset_1('#skF_1','#skF_2',C_368) = k1_relat_1(C_368)
      | ~ m1_subset_1(C_368,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4638,c_4728])).

tff(c_4777,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4642,c_4765])).

tff(c_6878,plain,(
    ! [B_493,A_494,C_495] :
      ( k1_xboole_0 = B_493
      | k1_relset_1(A_494,B_493,C_495) = A_494
      | ~ v1_funct_2(C_495,A_494,B_493)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(A_494,B_493))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6891,plain,(
    ! [C_495] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_495) = '#skF_1'
      | ~ v1_funct_2(C_495,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_495,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4638,c_6878])).

tff(c_6915,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6891])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4653,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4638,c_8])).

tff(c_4699,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4653])).

tff(c_6933,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6915,c_4699])).

tff(c_7115,plain,(
    ! [A_502] : k2_zfmisc_1(A_502,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6915,c_6915,c_10])).

tff(c_5559,plain,(
    ! [B_423,A_424,C_425] :
      ( k1_xboole_0 = B_423
      | k1_relset_1(A_424,B_423,C_425) = A_424
      | ~ v1_funct_2(C_425,A_424,B_423)
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k2_zfmisc_1(A_424,B_423))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5572,plain,(
    ! [C_425] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_425) = '#skF_1'
      | ~ v1_funct_2(C_425,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_425,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4638,c_5559])).

tff(c_5599,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5572])).

tff(c_5624,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5599,c_121])).

tff(c_5626,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5599,c_5599,c_10])).

tff(c_54,plain,(
    ! [A_31] :
      ( m1_subset_1(A_31,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_31),k2_relat_1(A_31))))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5011,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5004,c_54])).

tff(c_5018,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_5011])).

tff(c_5042,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_5018,c_16])).

tff(c_5056,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5042,c_2])).

tff(c_5133,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5056])).

tff(c_5730,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5626,c_5133])).

tff(c_5736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5624,c_5730])).

tff(c_6433,plain,(
    ! [C_480] :
      ( k1_relset_1('#skF_1','#skF_2',C_480) = '#skF_1'
      | ~ v1_funct_2(C_480,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_480,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_5572])).

tff(c_6440,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4642,c_6433])).

tff(c_6452,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4777,c_6440])).

tff(c_5229,plain,(
    ! [A_412,B_413,C_414] :
      ( m1_subset_1(k1_relset_1(A_412,B_413,C_414),k1_zfmisc_1(A_412))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_412,B_413))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5286,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4777,c_5229])).

tff(c_5311,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_4638,c_5286])).

tff(c_5380,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5311,c_16])).

tff(c_5488,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5380,c_2])).

tff(c_5558,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5488])).

tff(c_6457,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6452,c_5558])).

tff(c_6472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6457])).

tff(c_6473,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5488])).

tff(c_6479,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6473,c_5133])).

tff(c_6490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4638,c_6479])).

tff(c_6491,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5056])).

tff(c_7125,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7115,c_6491])).

tff(c_7165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6933,c_7125])).

tff(c_8104,plain,(
    ! [C_560] :
      ( k1_relset_1('#skF_1','#skF_2',C_560) = '#skF_1'
      | ~ v1_funct_2(C_560,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_560,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_6891])).

tff(c_8111,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4642,c_8104])).

tff(c_8123,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4777,c_8111])).

tff(c_6578,plain,(
    ! [A_482,B_483,C_484] :
      ( m1_subset_1(k1_relset_1(A_482,B_483,C_484),k1_zfmisc_1(A_482))
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_482,B_483))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6632,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4777,c_6578])).

tff(c_6657,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_4638,c_6632])).

tff(c_6726,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6657,c_16])).

tff(c_6819,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6726,c_2])).

tff(c_6877,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6819])).

tff(c_8132,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8123,c_6877])).

tff(c_8145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8132])).

tff(c_8146,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6819])).

tff(c_11131,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11122])).

tff(c_11136,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11131,c_28])).

tff(c_11143,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_11136])).

tff(c_11172,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11143,c_30])).

tff(c_11196,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_8146,c_11172])).

tff(c_11202,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11196,c_11143])).

tff(c_4879,plain,(
    ! [A_383] :
      ( m1_subset_1(A_383,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_383),k2_relat_1(A_383))))
      | ~ v1_funct_1(A_383)
      | ~ v1_relat_1(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4900,plain,(
    ! [A_383] :
      ( r1_tarski(A_383,k2_zfmisc_1(k1_relat_1(A_383),k2_relat_1(A_383)))
      | ~ v1_funct_1(A_383)
      | ~ v1_relat_1(A_383) ) ),
    inference(resolution,[status(thm)],[c_4879,c_16])).

tff(c_11226,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11202,c_4900])).

tff(c_11252,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11132,c_171,c_11226])).

tff(c_11334,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_11252])).

tff(c_11349,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_5004,c_11334])).

tff(c_11351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_11349])).

tff(c_11353,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4653])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_11363,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11353,c_11353,c_12])).

tff(c_11352,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4653])).

tff(c_11386,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11353,c_11353,c_11352])).

tff(c_11387,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_11386])).

tff(c_11389,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11387,c_201])).

tff(c_11502,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11363,c_11389])).

tff(c_11364,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11353,c_14])).

tff(c_11520,plain,(
    ! [A_759,B_760,C_761] :
      ( k2_relset_1(A_759,B_760,C_761) = k2_relat_1(C_761)
      | ~ m1_subset_1(C_761,k1_zfmisc_1(k2_zfmisc_1(A_759,B_760))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_11537,plain,(
    ! [A_762,B_763] : k2_relset_1(A_762,B_763,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11364,c_11520])).

tff(c_11391,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11387,c_11387,c_62])).

tff(c_11541,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_11537,c_11391])).

tff(c_11397,plain,(
    ! [A_745] :
      ( k1_relat_1(k2_funct_1(A_745)) = k2_relat_1(A_745)
      | ~ v2_funct_1(A_745)
      | ~ v1_funct_1(A_745)
      | ~ v1_relat_1(A_745) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_13125,plain,(
    ! [A_898] :
      ( k9_relat_1(k2_funct_1(A_898),k2_relat_1(A_898)) = k2_relat_1(k2_funct_1(A_898))
      | ~ v1_relat_1(k2_funct_1(A_898))
      | ~ v2_funct_1(A_898)
      | ~ v1_funct_1(A_898)
      | ~ v1_relat_1(A_898) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11397,c_22])).

tff(c_13141,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11541,c_13125])).

tff(c_13148,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_13141])).

tff(c_13149,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_13148])).

tff(c_13152,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_13149])).

tff(c_13156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_13152])).

tff(c_13158,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_13148])).

tff(c_11362,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11353,c_11353,c_10])).

tff(c_11587,plain,(
    ! [A_768,B_769,C_770] :
      ( k1_relset_1(A_768,B_769,C_770) = k1_relat_1(C_770)
      | ~ m1_subset_1(C_770,k1_zfmisc_1(k2_zfmisc_1(A_768,B_769))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_11602,plain,(
    ! [A_768,B_769] : k1_relset_1(A_768,B_769,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11364,c_11587])).

tff(c_11823,plain,(
    ! [A_801,B_802,C_803] :
      ( m1_subset_1(k1_relset_1(A_801,B_802,C_803),k1_zfmisc_1(A_801))
      | ~ m1_subset_1(C_803,k1_zfmisc_1(k2_zfmisc_1(A_801,B_802))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_11859,plain,(
    ! [A_768,B_769] :
      ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1(A_768))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_768,B_769))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11602,c_11823])).

tff(c_11877,plain,(
    ! [A_804] : m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1(A_804)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11364,c_11859])).

tff(c_11941,plain,(
    ! [A_807] : r1_tarski(k1_relat_1('#skF_3'),A_807) ),
    inference(resolution,[status(thm)],[c_11877,c_16])).

tff(c_238,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_121,c_230])).

tff(c_11355,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ r1_tarski(A_5,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11353,c_11353,c_238])).

tff(c_11982,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_11941,c_11355])).

tff(c_13157,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_13148])).

tff(c_13162,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13157,c_28])).

tff(c_13169,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_13162])).

tff(c_13198,plain,
    ( k10_relat_1('#skF_3','#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13169,c_30])).

tff(c_13222,plain,(
    k10_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_11982,c_13198])).

tff(c_13228,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13222,c_13169])).

tff(c_11653,plain,(
    ! [A_781] :
      ( m1_subset_1(A_781,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_781),k2_relat_1(A_781))))
      | ~ v1_funct_1(A_781)
      | ~ v1_relat_1(A_781) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_11681,plain,(
    ! [A_781] :
      ( r1_tarski(A_781,k2_zfmisc_1(k1_relat_1(A_781),k2_relat_1(A_781)))
      | ~ v1_funct_1(A_781)
      | ~ v1_relat_1(A_781) ) ),
    inference(resolution,[status(thm)],[c_11653,c_16])).

tff(c_13252,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13228,c_11681])).

tff(c_13278,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13158,c_171,c_11362,c_13252])).

tff(c_13280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11502,c_13278])).

tff(c_13281,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11386])).

tff(c_13329,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13281,c_13281,c_11362])).

tff(c_13290,plain,(
    ~ r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13281,c_201])).

tff(c_13486,plain,(
    ~ r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13329,c_13290])).

tff(c_13293,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13281,c_160])).

tff(c_13297,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13281,c_70])).

tff(c_13296,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13281,c_64])).

tff(c_13406,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13281,c_11364])).

tff(c_13527,plain,(
    ! [A_921,B_922,C_923] :
      ( k2_relset_1(A_921,B_922,C_923) = k2_relat_1(C_923)
      | ~ m1_subset_1(C_923,k1_zfmisc_1(k2_zfmisc_1(A_921,B_922))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_13569,plain,(
    ! [A_927,B_928] : k2_relset_1(A_927,B_928,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_13406,c_13527])).

tff(c_13294,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13281,c_62])).

tff(c_13573,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_13569,c_13294])).

tff(c_13344,plain,(
    ! [A_902] :
      ( k1_relat_1(k2_funct_1(A_902)) = k2_relat_1(A_902)
      | ~ v2_funct_1(A_902)
      | ~ v1_funct_1(A_902)
      | ~ v1_relat_1(A_902) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_15447,plain,(
    ! [A_1077] :
      ( k9_relat_1(k2_funct_1(A_1077),k2_relat_1(A_1077)) = k2_relat_1(k2_funct_1(A_1077))
      | ~ v1_relat_1(k2_funct_1(A_1077))
      | ~ v2_funct_1(A_1077)
      | ~ v1_funct_1(A_1077)
      | ~ v1_relat_1(A_1077) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13344,c_22])).

tff(c_15463,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_13573,c_15447])).

tff(c_15470,plain,
    ( k9_relat_1(k2_funct_1('#skF_1'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13293,c_13297,c_13296,c_15463])).

tff(c_15471,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_15470])).

tff(c_15474,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_15471])).

tff(c_15478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13293,c_13297,c_15474])).

tff(c_15480,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_15470])).

tff(c_13292,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13281,c_171])).

tff(c_13548,plain,(
    ! [A_924,B_925,C_926] :
      ( k1_relset_1(A_924,B_925,C_926) = k1_relat_1(C_926)
      | ~ m1_subset_1(C_926,k1_zfmisc_1(k2_zfmisc_1(A_924,B_925))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_13567,plain,(
    ! [A_924,B_925] : k1_relset_1(A_924,B_925,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_13406,c_13548])).

tff(c_13696,plain,(
    ! [A_947,B_948,C_949] :
      ( m1_subset_1(k1_relset_1(A_947,B_948,C_949),k1_zfmisc_1(A_947))
      | ~ m1_subset_1(C_949,k1_zfmisc_1(k2_zfmisc_1(A_947,B_948))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_13729,plain,(
    ! [A_924,B_925] :
      ( m1_subset_1(k1_relat_1('#skF_1'),k1_zfmisc_1(A_924))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_924,B_925))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13567,c_13696])).

tff(c_13745,plain,(
    ! [A_950] : m1_subset_1(k1_relat_1('#skF_1'),k1_zfmisc_1(A_950)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13406,c_13729])).

tff(c_13786,plain,(
    ! [A_951] : r1_tarski(k1_relat_1('#skF_1'),A_951) ),
    inference(resolution,[status(thm)],[c_13745,c_16])).

tff(c_13436,plain,(
    ! [A_5] :
      ( A_5 = '#skF_1'
      | ~ r1_tarski(A_5,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13281,c_13281,c_11355])).

tff(c_13813,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_13786,c_13436])).

tff(c_15479,plain,(
    k9_relat_1(k2_funct_1('#skF_1'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_15470])).

tff(c_15484,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = k10_relat_1('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15479,c_28])).

tff(c_15491,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = k10_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13293,c_13297,c_13296,c_15484])).

tff(c_15520,plain,
    ( k10_relat_1('#skF_1','#skF_2') = k1_relat_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15491,c_30])).

tff(c_15544,plain,(
    k10_relat_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13293,c_13297,c_13296,c_13813,c_15520])).

tff(c_15550,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15544,c_15491])).

tff(c_13450,plain,(
    ! [A_907] :
      ( m1_subset_1(A_907,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_907),k2_relat_1(A_907))))
      | ~ v1_funct_1(A_907)
      | ~ v1_relat_1(A_907) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_13467,plain,(
    ! [A_907] :
      ( r1_tarski(A_907,k2_zfmisc_1(k1_relat_1(A_907),k2_relat_1(A_907)))
      | ~ v1_funct_1(A_907)
      | ~ v1_relat_1(A_907) ) ),
    inference(resolution,[status(thm)],[c_13450,c_16])).

tff(c_15574,plain,
    ( r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15550,c_13467])).

tff(c_15600,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15480,c_13292,c_13329,c_15574])).

tff(c_15602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13486,c_15600])).

tff(c_15603,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_15604,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_34,plain,(
    ! [C_18,A_16,B_17] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_15611,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15604,c_34])).

tff(c_16947,plain,(
    ! [A_1188,B_1189,C_1190] :
      ( k2_relset_1(A_1188,B_1189,C_1190) = k2_relat_1(C_1190)
      | ~ m1_subset_1(C_1190,k1_zfmisc_1(k2_zfmisc_1(A_1188,B_1189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16960,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_16947])).

tff(c_16974,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16960])).

tff(c_15761,plain,(
    ! [A_1103,B_1104,C_1105] :
      ( k2_relset_1(A_1103,B_1104,C_1105) = k2_relat_1(C_1105)
      | ~ m1_subset_1(C_1105,k1_zfmisc_1(k2_zfmisc_1(A_1103,B_1104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_15774,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_15761])).

tff(c_15789,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_15774])).

tff(c_15851,plain,(
    ! [A_1108,B_1109,C_1110] :
      ( k1_relset_1(A_1108,B_1109,C_1110) = k1_relat_1(C_1110)
      | ~ m1_subset_1(C_1110,k1_zfmisc_1(k2_zfmisc_1(A_1108,B_1109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_15880,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15604,c_15851])).

tff(c_16487,plain,(
    ! [B_1156,C_1157,A_1158] :
      ( k1_xboole_0 = B_1156
      | v1_funct_2(C_1157,A_1158,B_1156)
      | k1_relset_1(A_1158,B_1156,C_1157) != A_1158
      | ~ m1_subset_1(C_1157,k1_zfmisc_1(k2_zfmisc_1(A_1158,B_1156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16500,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_15604,c_16487])).

tff(c_16524,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15880,c_16500])).

tff(c_16525,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_15603,c_16524])).

tff(c_16532,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16525])).

tff(c_16535,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_16532])).

tff(c_16538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_15789,c_16535])).

tff(c_16539,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16525])).

tff(c_16563,plain,(
    ! [A_5] : r1_tarski('#skF_1',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16539,c_121])).

tff(c_16565,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16539,c_16539,c_10])).

tff(c_15612,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_15604,c_16])).

tff(c_15639,plain,(
    ! [B_1081,A_1082] :
      ( B_1081 = A_1082
      | ~ r1_tarski(B_1081,A_1082)
      | ~ r1_tarski(A_1082,B_1081) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15648,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15612,c_15639])).

tff(c_15693,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15648])).

tff(c_16675,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16565,c_15693])).

tff(c_16681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16563,c_16675])).

tff(c_16682,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_15648])).

tff(c_16686,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16682,c_15604])).

tff(c_16771,plain,(
    ! [A_1168,B_1169,C_1170] :
      ( k1_relset_1(A_1168,B_1169,C_1170) = k1_relat_1(C_1170)
      | ~ m1_subset_1(C_1170,k1_zfmisc_1(k2_zfmisc_1(A_1168,B_1169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16806,plain,(
    ! [C_1173] :
      ( k1_relset_1('#skF_2','#skF_1',C_1173) = k1_relat_1(C_1173)
      | ~ m1_subset_1(C_1173,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16682,c_16771])).

tff(c_16818,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16686,c_16806])).

tff(c_17116,plain,(
    ! [A_1206,B_1207,C_1208] :
      ( m1_subset_1(k1_relset_1(A_1206,B_1207,C_1208),k1_zfmisc_1(A_1206))
      | ~ m1_subset_1(C_1208,k1_zfmisc_1(k2_zfmisc_1(A_1206,B_1207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_17166,plain,
    ( m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16818,c_17116])).

tff(c_17193,plain,(
    m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16686,c_16682,c_17166])).

tff(c_17406,plain,(
    r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_17193,c_16])).

tff(c_17422,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_17406,c_2])).

tff(c_17954,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_17422])).

tff(c_17957,plain,
    ( ~ r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_17954])).

tff(c_17960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_6,c_16974,c_17957])).

tff(c_17961,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17422])).

tff(c_16793,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_16771])).

tff(c_17493,plain,(
    ! [B_1223,A_1224,C_1225] :
      ( k1_xboole_0 = B_1223
      | k1_relset_1(A_1224,B_1223,C_1225) = A_1224
      | ~ v1_funct_2(C_1225,A_1224,B_1223)
      | ~ m1_subset_1(C_1225,k1_zfmisc_1(k2_zfmisc_1(A_1224,B_1223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_17513,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_17493])).

tff(c_17532,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16793,c_17513])).

tff(c_17536,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_17532])).

tff(c_17172,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16793,c_17116])).

tff(c_17197,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_17172])).

tff(c_17259,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17197,c_16])).

tff(c_17347,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_17259,c_2])).

tff(c_17441,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17347])).

tff(c_17538,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17536,c_17441])).

tff(c_17552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_17538])).

tff(c_17553,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17532])).

tff(c_16697,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16682,c_8])).

tff(c_16740,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16697])).

tff(c_17572,plain,(
    k2_funct_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17553,c_16740])).

tff(c_17582,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17553,c_17553,c_12])).

tff(c_17638,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17582,c_16682])).

tff(c_17640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17572,c_17638])).

tff(c_17641,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17347])).

tff(c_17984,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17961,c_22])).

tff(c_17999,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15611,c_17984])).

tff(c_18069,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_17999])).

tff(c_18075,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_18069])).

tff(c_18237,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18075,c_30])).

tff(c_18253,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_17641,c_18237])).

tff(c_18264,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18253,c_18075])).

tff(c_56,plain,(
    ! [A_31] :
      ( v1_funct_2(A_31,k1_relat_1(A_31),k2_relat_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18285,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18264,c_56])).

tff(c_18300,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15611,c_171,c_17961,c_18285])).

tff(c_18302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15603,c_18300])).

tff(c_18303,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16697])).

tff(c_18351,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18303])).

tff(c_18362,plain,(
    ! [A_5] : r1_tarski('#skF_1',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18351,c_121])).

tff(c_18365,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18351,c_18351,c_12])).

tff(c_15649,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_15639])).

tff(c_15675,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_15649])).

tff(c_18436,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18365,c_15675])).

tff(c_18441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18362,c_18436])).

tff(c_18442,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18303])).

tff(c_18453,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18442,c_121])).

tff(c_18455,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18442,c_18442,c_10])).

tff(c_18565,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18455,c_15675])).

tff(c_18570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18453,c_18565])).

tff(c_18571,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_15649])).

tff(c_18574,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18571,c_66])).

tff(c_18691,plain,(
    ! [A_1278,B_1279,C_1280] :
      ( k2_relset_1(A_1278,B_1279,C_1280) = k2_relat_1(C_1280)
      | ~ m1_subset_1(C_1280,k1_zfmisc_1(k2_zfmisc_1(A_1278,B_1279))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18893,plain,(
    ! [C_1308] :
      ( k2_relset_1('#skF_1','#skF_2',C_1308) = k2_relat_1(C_1308)
      | ~ m1_subset_1(C_1308,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18571,c_18691])).

tff(c_18896,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18574,c_18893])).

tff(c_18906,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_18896])).

tff(c_18761,plain,(
    ! [A_1289,B_1290,C_1291] :
      ( k1_relset_1(A_1289,B_1290,C_1291) = k1_relat_1(C_1291)
      | ~ m1_subset_1(C_1291,k1_zfmisc_1(k2_zfmisc_1(A_1289,B_1290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18786,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15604,c_18761])).

tff(c_20653,plain,(
    ! [B_1388,C_1389,A_1390] :
      ( k1_xboole_0 = B_1388
      | v1_funct_2(C_1389,A_1390,B_1388)
      | k1_relset_1(A_1390,B_1388,C_1389) != A_1390
      | ~ m1_subset_1(C_1389,k1_zfmisc_1(k2_zfmisc_1(A_1390,B_1388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20666,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_15604,c_20653])).

tff(c_20684,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18786,c_20666])).

tff(c_20685,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_15603,c_20684])).

tff(c_20690,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20685])).

tff(c_20693,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_20690])).

tff(c_20696,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_18906,c_20693])).

tff(c_20697,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20685])).

tff(c_18585,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_18571,c_8])).

tff(c_18642,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18585])).

tff(c_20718,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20697,c_18642])).

tff(c_20728,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20697,c_20697,c_12])).

tff(c_20829,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20728,c_18571])).

tff(c_20831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20718,c_20829])).

tff(c_20833,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18585])).

tff(c_20844,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20833,c_20833,c_12])).

tff(c_20832,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18585])).

tff(c_21148,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20833,c_20833,c_20832])).

tff(c_21149,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_21148])).

tff(c_20841,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20833,c_121])).

tff(c_20890,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20833,c_20833,c_20832])).

tff(c_20891,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20890])).

tff(c_20889,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15648])).

tff(c_20973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20841,c_20844,c_20891,c_20889])).

tff(c_20974,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20890])).

tff(c_20977,plain,(
    ! [A_5] : r1_tarski('#skF_1',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20974,c_20841])).

tff(c_20843,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20833,c_20833,c_10])).

tff(c_21040,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20974,c_20974,c_20843])).

tff(c_21145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20977,c_21040,c_20974,c_20889])).

tff(c_21146,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_15648])).

tff(c_21165,plain,(
    k2_zfmisc_1('#skF_3','#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21149,c_21146])).

tff(c_21239,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20844,c_21165])).

tff(c_21247,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21239,c_32])).

tff(c_21257,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_70,c_64,c_21247])).

tff(c_20845,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20833,c_14])).

tff(c_21313,plain,(
    ! [A_1421,B_1422,C_1423] :
      ( k2_relset_1(A_1421,B_1422,C_1423) = k2_relat_1(C_1423)
      | ~ m1_subset_1(C_1423,k1_zfmisc_1(k2_zfmisc_1(A_1421,B_1422))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_21323,plain,(
    ! [A_1421,B_1422] : k2_relset_1(A_1421,B_1422,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20845,c_21313])).

tff(c_21345,plain,(
    ! [A_1426,B_1427] : k2_relset_1(A_1426,B_1427,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21257,c_21323])).

tff(c_21168,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21149,c_21149,c_62])).

tff(c_21349,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_21345,c_21168])).

tff(c_21400,plain,(
    ! [A_1430,B_1431,C_1432] :
      ( k1_relset_1(A_1430,B_1431,C_1432) = k1_relat_1(C_1432)
      | ~ m1_subset_1(C_1432,k1_zfmisc_1(k2_zfmisc_1(A_1430,B_1431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_21410,plain,(
    ! [A_1430,B_1431] : k1_relset_1(A_1430,B_1431,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20845,c_21400])).

tff(c_21416,plain,(
    ! [A_1430,B_1431] : k1_relset_1(A_1430,B_1431,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21349,c_21410])).

tff(c_46,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_74,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_21899,plain,(
    ! [C_1483,B_1484] :
      ( v1_funct_2(C_1483,'#skF_3',B_1484)
      | k1_relset_1('#skF_3',B_1484,C_1483) != '#skF_3'
      | ~ m1_subset_1(C_1483,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20833,c_20833,c_20833,c_20833,c_74])).

tff(c_21905,plain,(
    ! [B_1484] :
      ( v1_funct_2('#skF_3','#skF_3',B_1484)
      | k1_relset_1('#skF_3',B_1484,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_20845,c_21899])).

tff(c_21913,plain,(
    ! [B_1484] : v1_funct_2('#skF_3','#skF_3',B_1484) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21416,c_21905])).

tff(c_21167,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21149,c_15603])).

tff(c_21276,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21239,c_21167])).

tff(c_21918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21913,c_21276])).

tff(c_21919,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_21148])).

tff(c_21920,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_21148])).

tff(c_21943,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21919,c_21920])).

tff(c_42,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_72,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_42])).

tff(c_20842,plain,(
    ! [A_28] :
      ( v1_funct_2('#skF_3',A_28,'#skF_3')
      | A_28 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20833,c_20833,c_20833,c_72])).

tff(c_22147,plain,(
    ! [A_1495] :
      ( v1_funct_2('#skF_1',A_1495,'#skF_1')
      | A_1495 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21919,c_21919,c_21919,c_20842])).

tff(c_22016,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21919,c_21919,c_20843])).

tff(c_22039,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22016,c_21919,c_21146])).

tff(c_21932,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21919,c_15603])).

tff(c_22105,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22039,c_21932])).

tff(c_22150,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22147,c_22105])).

tff(c_22154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21943,c_22150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:29:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.17/3.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.25/3.81  
% 10.25/3.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.25/3.81  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.25/3.81  
% 10.25/3.81  %Foreground sorts:
% 10.25/3.81  
% 10.25/3.81  
% 10.25/3.81  %Background operators:
% 10.25/3.81  
% 10.25/3.81  
% 10.25/3.81  %Foreground operators:
% 10.25/3.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.25/3.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.25/3.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.25/3.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.25/3.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.25/3.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.25/3.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.25/3.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.25/3.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.25/3.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.25/3.81  tff('#skF_2', type, '#skF_2': $i).
% 10.25/3.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.25/3.81  tff('#skF_3', type, '#skF_3': $i).
% 10.25/3.81  tff('#skF_1', type, '#skF_1': $i).
% 10.25/3.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.25/3.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.25/3.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.25/3.81  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.25/3.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.25/3.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.25/3.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.25/3.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.25/3.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.25/3.81  
% 10.58/3.86  tff(f_140, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 10.58/3.86  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.58/3.86  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.58/3.86  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.58/3.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.58/3.86  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.58/3.86  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.58/3.86  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 10.58/3.86  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.58/3.86  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.58/3.86  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.58/3.86  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.58/3.86  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 10.58/3.86  tff(f_123, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 10.58/3.86  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 10.58/3.86  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.58/3.86  tff(c_143, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.58/3.86  tff(c_160, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_143])).
% 10.58/3.86  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.58/3.86  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.58/3.86  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.58/3.86  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.58/3.86  tff(c_24, plain, (![A_12]: (v1_funct_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.58/3.86  tff(c_60, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.58/3.86  tff(c_162, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 10.58/3.86  tff(c_165, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_162])).
% 10.58/3.86  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_165])).
% 10.58/3.86  tff(c_170, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_60])).
% 10.58/3.86  tff(c_197, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_170])).
% 10.58/3.86  tff(c_201, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_197])).
% 10.58/3.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.58/3.86  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.58/3.86  tff(c_403, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.58/3.86  tff(c_430, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_403])).
% 10.58/3.86  tff(c_4334, plain, (![B_343, A_344, C_345]: (k1_xboole_0=B_343 | k1_relset_1(A_344, B_343, C_345)=A_344 | ~v1_funct_2(C_345, A_344, B_343) | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(A_344, B_343))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.58/3.86  tff(c_4351, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_4334])).
% 10.58/3.86  tff(c_4367, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_430, c_4351])).
% 10.58/3.86  tff(c_4371, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_4367])).
% 10.58/3.86  tff(c_3849, plain, (![A_307, B_308, C_309]: (m1_subset_1(k1_relset_1(A_307, B_308, C_309), k1_zfmisc_1(A_307)) | ~m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_307, B_308))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.58/3.86  tff(c_3892, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_430, c_3849])).
% 10.58/3.86  tff(c_3912, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3892])).
% 10.58/3.86  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.58/3.86  tff(c_3965, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_3912, c_16])).
% 10.58/3.86  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.58/3.86  tff(c_4030, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3965, c_2])).
% 10.58/3.86  tff(c_4082, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4030])).
% 10.58/3.86  tff(c_4375, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4371, c_4082])).
% 10.58/3.86  tff(c_4387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4375])).
% 10.58/3.86  tff(c_4388, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4367])).
% 10.58/3.86  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.58/3.86  tff(c_109, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.58/3.86  tff(c_121, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_109])).
% 10.58/3.86  tff(c_4416, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_4388, c_121])).
% 10.58/3.86  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.58/3.86  tff(c_4418, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4388, c_4388, c_10])).
% 10.58/3.86  tff(c_120, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_109])).
% 10.58/3.86  tff(c_230, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.58/3.86  tff(c_237, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_120, c_230])).
% 10.58/3.86  tff(c_268, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_237])).
% 10.58/3.86  tff(c_4573, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4418, c_268])).
% 10.58/3.86  tff(c_4579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4416, c_4573])).
% 10.58/3.86  tff(c_4580, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_4030])).
% 10.58/3.86  tff(c_298, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.58/3.86  tff(c_305, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_298])).
% 10.58/3.86  tff(c_318, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_305])).
% 10.58/3.86  tff(c_32, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.58/3.86  tff(c_26, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.58/3.86  tff(c_271, plain, (![A_70]: (k1_relat_1(k2_funct_1(A_70))=k2_relat_1(A_70) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.58/3.86  tff(c_22, plain, (![A_11]: (k9_relat_1(A_11, k1_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.58/3.86  tff(c_3475, plain, (![A_290]: (k9_relat_1(k2_funct_1(A_290), k2_relat_1(A_290))=k2_relat_1(k2_funct_1(A_290)) | ~v1_relat_1(k2_funct_1(A_290)) | ~v2_funct_1(A_290) | ~v1_funct_1(A_290) | ~v1_relat_1(A_290))), inference(superposition, [status(thm), theory('equality')], [c_271, c_22])).
% 10.58/3.86  tff(c_3491, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_318, c_3475])).
% 10.58/3.86  tff(c_3498, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_3491])).
% 10.58/3.86  tff(c_3499, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3498])).
% 10.58/3.86  tff(c_3502, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_3499])).
% 10.58/3.86  tff(c_3506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_3502])).
% 10.58/3.86  tff(c_3508, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3498])).
% 10.58/3.86  tff(c_171, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_60])).
% 10.58/3.86  tff(c_802, plain, (![B_118, A_119, C_120]: (k1_xboole_0=B_118 | k1_relset_1(A_119, B_118, C_120)=A_119 | ~v1_funct_2(C_120, A_119, B_118) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.58/3.86  tff(c_819, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_802])).
% 10.58/3.86  tff(c_838, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_430, c_819])).
% 10.58/3.86  tff(c_842, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_838])).
% 10.58/3.86  tff(c_529, plain, (![A_102, B_103, C_104]: (m1_subset_1(k1_relset_1(A_102, B_103, C_104), k1_zfmisc_1(A_102)) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.58/3.86  tff(c_571, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_430, c_529])).
% 10.58/3.86  tff(c_592, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_571])).
% 10.58/3.86  tff(c_724, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_592, c_16])).
% 10.58/3.86  tff(c_727, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_724, c_2])).
% 10.58/3.86  tff(c_754, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_727])).
% 10.58/3.86  tff(c_844, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_842, c_754])).
% 10.58/3.86  tff(c_859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_844])).
% 10.58/3.86  tff(c_860, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_838])).
% 10.58/3.86  tff(c_886, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_860, c_121])).
% 10.58/3.86  tff(c_888, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_860, c_860, c_10])).
% 10.58/3.86  tff(c_336, plain, (![A_77]: (m1_subset_1(A_77, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_77), k2_relat_1(A_77)))) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.58/3.86  tff(c_350, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_318, c_336])).
% 10.58/3.86  tff(c_362, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_350])).
% 10.58/3.86  tff(c_379, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_362, c_16])).
% 10.58/3.86  tff(c_389, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_379, c_2])).
% 10.58/3.86  tff(c_447, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_389])).
% 10.58/3.86  tff(c_953, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_888, c_447])).
% 10.58/3.86  tff(c_963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_886, c_953])).
% 10.58/3.86  tff(c_964, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_727])).
% 10.58/3.86  tff(c_3507, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3498])).
% 10.58/3.86  tff(c_28, plain, (![B_14, A_13]: (k9_relat_1(k2_funct_1(B_14), A_13)=k10_relat_1(B_14, A_13) | ~v2_funct_1(B_14) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.58/3.86  tff(c_3512, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3507, c_28])).
% 10.58/3.86  tff(c_3519, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_3512])).
% 10.58/3.86  tff(c_30, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.58/3.86  tff(c_3548, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3519, c_30])).
% 10.58/3.86  tff(c_3572, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_964, c_3548])).
% 10.58/3.86  tff(c_3578, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3572, c_3519])).
% 10.58/3.86  tff(c_360, plain, (![A_77]: (r1_tarski(A_77, k2_zfmisc_1(k1_relat_1(A_77), k2_relat_1(A_77))) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(resolution, [status(thm)], [c_336, c_16])).
% 10.58/3.86  tff(c_3602, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3578, c_360])).
% 10.58/3.86  tff(c_3628, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3508, c_171, c_3602])).
% 10.58/3.86  tff(c_3717, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_3628])).
% 10.58/3.86  tff(c_3730, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_318, c_3717])).
% 10.58/3.86  tff(c_3732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_3730])).
% 10.58/3.86  tff(c_3733, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_389])).
% 10.58/3.86  tff(c_4586, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4580, c_3733])).
% 10.58/3.86  tff(c_4631, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4586, c_268])).
% 10.58/3.86  tff(c_4637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4631])).
% 10.58/3.86  tff(c_4638, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_237])).
% 10.58/3.86  tff(c_4642, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4638, c_66])).
% 10.58/3.86  tff(c_4901, plain, (![A_384, B_385, C_386]: (k2_relset_1(A_384, B_385, C_386)=k2_relat_1(C_386) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.58/3.86  tff(c_4991, plain, (![C_399]: (k2_relset_1('#skF_1', '#skF_2', C_399)=k2_relat_1(C_399) | ~m1_subset_1(C_399, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4638, c_4901])).
% 10.58/3.86  tff(c_4994, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4642, c_4991])).
% 10.58/3.86  tff(c_5004, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4994])).
% 10.58/3.86  tff(c_4713, plain, (![A_360]: (k1_relat_1(k2_funct_1(A_360))=k2_relat_1(A_360) | ~v2_funct_1(A_360) | ~v1_funct_1(A_360) | ~v1_relat_1(A_360))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.58/3.86  tff(c_11099, plain, (![A_740]: (k9_relat_1(k2_funct_1(A_740), k2_relat_1(A_740))=k2_relat_1(k2_funct_1(A_740)) | ~v1_relat_1(k2_funct_1(A_740)) | ~v2_funct_1(A_740) | ~v1_funct_1(A_740) | ~v1_relat_1(A_740))), inference(superposition, [status(thm), theory('equality')], [c_4713, c_22])).
% 10.58/3.86  tff(c_11111, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5004, c_11099])).
% 10.58/3.86  tff(c_11122, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_11111])).
% 10.58/3.86  tff(c_11123, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_11122])).
% 10.58/3.86  tff(c_11126, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_11123])).
% 10.58/3.86  tff(c_11130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_11126])).
% 10.58/3.86  tff(c_11132, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_11122])).
% 10.58/3.86  tff(c_4728, plain, (![A_361, B_362, C_363]: (k1_relset_1(A_361, B_362, C_363)=k1_relat_1(C_363) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_361, B_362))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.58/3.86  tff(c_4765, plain, (![C_368]: (k1_relset_1('#skF_1', '#skF_2', C_368)=k1_relat_1(C_368) | ~m1_subset_1(C_368, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4638, c_4728])).
% 10.58/3.86  tff(c_4777, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4642, c_4765])).
% 10.58/3.86  tff(c_6878, plain, (![B_493, A_494, C_495]: (k1_xboole_0=B_493 | k1_relset_1(A_494, B_493, C_495)=A_494 | ~v1_funct_2(C_495, A_494, B_493) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(A_494, B_493))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.58/3.86  tff(c_6891, plain, (![C_495]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_495)='#skF_1' | ~v1_funct_2(C_495, '#skF_1', '#skF_2') | ~m1_subset_1(C_495, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4638, c_6878])).
% 10.58/3.86  tff(c_6915, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6891])).
% 10.58/3.86  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.58/3.86  tff(c_4653, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4638, c_8])).
% 10.58/3.86  tff(c_4699, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_4653])).
% 10.58/3.86  tff(c_6933, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6915, c_4699])).
% 10.58/3.86  tff(c_7115, plain, (![A_502]: (k2_zfmisc_1(A_502, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6915, c_6915, c_10])).
% 10.58/3.86  tff(c_5559, plain, (![B_423, A_424, C_425]: (k1_xboole_0=B_423 | k1_relset_1(A_424, B_423, C_425)=A_424 | ~v1_funct_2(C_425, A_424, B_423) | ~m1_subset_1(C_425, k1_zfmisc_1(k2_zfmisc_1(A_424, B_423))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.58/3.86  tff(c_5572, plain, (![C_425]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_425)='#skF_1' | ~v1_funct_2(C_425, '#skF_1', '#skF_2') | ~m1_subset_1(C_425, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4638, c_5559])).
% 10.58/3.86  tff(c_5599, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_5572])).
% 10.58/3.86  tff(c_5624, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_5599, c_121])).
% 10.58/3.86  tff(c_5626, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5599, c_5599, c_10])).
% 10.58/3.86  tff(c_54, plain, (![A_31]: (m1_subset_1(A_31, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_31), k2_relat_1(A_31)))) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.58/3.86  tff(c_5011, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5004, c_54])).
% 10.58/3.86  tff(c_5018, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_5011])).
% 10.58/3.86  tff(c_5042, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_5018, c_16])).
% 10.58/3.86  tff(c_5056, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_5042, c_2])).
% 10.58/3.86  tff(c_5133, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5056])).
% 10.58/3.86  tff(c_5730, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5626, c_5133])).
% 10.58/3.86  tff(c_5736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5624, c_5730])).
% 10.58/3.86  tff(c_6433, plain, (![C_480]: (k1_relset_1('#skF_1', '#skF_2', C_480)='#skF_1' | ~v1_funct_2(C_480, '#skF_1', '#skF_2') | ~m1_subset_1(C_480, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_5572])).
% 10.58/3.86  tff(c_6440, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4642, c_6433])).
% 10.58/3.86  tff(c_6452, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4777, c_6440])).
% 10.58/3.86  tff(c_5229, plain, (![A_412, B_413, C_414]: (m1_subset_1(k1_relset_1(A_412, B_413, C_414), k1_zfmisc_1(A_412)) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_412, B_413))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.58/3.86  tff(c_5286, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4777, c_5229])).
% 10.58/3.86  tff(c_5311, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4642, c_4638, c_5286])).
% 10.58/3.86  tff(c_5380, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_5311, c_16])).
% 10.58/3.86  tff(c_5488, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_5380, c_2])).
% 10.58/3.86  tff(c_5558, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5488])).
% 10.58/3.86  tff(c_6457, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6452, c_5558])).
% 10.58/3.86  tff(c_6472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6457])).
% 10.58/3.86  tff(c_6473, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_5488])).
% 10.58/3.86  tff(c_6479, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6473, c_5133])).
% 10.58/3.86  tff(c_6490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4638, c_6479])).
% 10.58/3.86  tff(c_6491, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_5056])).
% 10.58/3.86  tff(c_7125, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7115, c_6491])).
% 10.58/3.86  tff(c_7165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6933, c_7125])).
% 10.58/3.86  tff(c_8104, plain, (![C_560]: (k1_relset_1('#skF_1', '#skF_2', C_560)='#skF_1' | ~v1_funct_2(C_560, '#skF_1', '#skF_2') | ~m1_subset_1(C_560, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_6891])).
% 10.58/3.86  tff(c_8111, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4642, c_8104])).
% 10.58/3.86  tff(c_8123, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4777, c_8111])).
% 10.58/3.86  tff(c_6578, plain, (![A_482, B_483, C_484]: (m1_subset_1(k1_relset_1(A_482, B_483, C_484), k1_zfmisc_1(A_482)) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_482, B_483))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.58/3.86  tff(c_6632, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4777, c_6578])).
% 10.58/3.86  tff(c_6657, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4642, c_4638, c_6632])).
% 10.58/3.86  tff(c_6726, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_6657, c_16])).
% 10.58/3.86  tff(c_6819, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6726, c_2])).
% 10.58/3.86  tff(c_6877, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6819])).
% 10.58/3.86  tff(c_8132, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8123, c_6877])).
% 10.58/3.86  tff(c_8145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8132])).
% 10.58/3.86  tff(c_8146, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_6819])).
% 10.58/3.86  tff(c_11131, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_11122])).
% 10.58/3.86  tff(c_11136, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11131, c_28])).
% 10.58/3.86  tff(c_11143, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_11136])).
% 10.58/3.86  tff(c_11172, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11143, c_30])).
% 10.58/3.86  tff(c_11196, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_8146, c_11172])).
% 10.58/3.86  tff(c_11202, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11196, c_11143])).
% 10.58/3.86  tff(c_4879, plain, (![A_383]: (m1_subset_1(A_383, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_383), k2_relat_1(A_383)))) | ~v1_funct_1(A_383) | ~v1_relat_1(A_383))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.58/3.86  tff(c_4900, plain, (![A_383]: (r1_tarski(A_383, k2_zfmisc_1(k1_relat_1(A_383), k2_relat_1(A_383))) | ~v1_funct_1(A_383) | ~v1_relat_1(A_383))), inference(resolution, [status(thm)], [c_4879, c_16])).
% 10.58/3.86  tff(c_11226, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11202, c_4900])).
% 10.58/3.86  tff(c_11252, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11132, c_171, c_11226])).
% 10.58/3.86  tff(c_11334, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_11252])).
% 10.58/3.86  tff(c_11349, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_5004, c_11334])).
% 10.58/3.86  tff(c_11351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_11349])).
% 10.58/3.86  tff(c_11353, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4653])).
% 10.58/3.86  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.58/3.86  tff(c_11363, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11353, c_11353, c_12])).
% 10.58/3.86  tff(c_11352, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4653])).
% 10.58/3.86  tff(c_11386, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11353, c_11353, c_11352])).
% 10.58/3.86  tff(c_11387, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_11386])).
% 10.58/3.86  tff(c_11389, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11387, c_201])).
% 10.58/3.86  tff(c_11502, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11363, c_11389])).
% 10.58/3.86  tff(c_11364, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_11353, c_14])).
% 10.58/3.86  tff(c_11520, plain, (![A_759, B_760, C_761]: (k2_relset_1(A_759, B_760, C_761)=k2_relat_1(C_761) | ~m1_subset_1(C_761, k1_zfmisc_1(k2_zfmisc_1(A_759, B_760))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.58/3.86  tff(c_11537, plain, (![A_762, B_763]: (k2_relset_1(A_762, B_763, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_11364, c_11520])).
% 10.58/3.86  tff(c_11391, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11387, c_11387, c_62])).
% 10.58/3.86  tff(c_11541, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_11537, c_11391])).
% 10.58/3.86  tff(c_11397, plain, (![A_745]: (k1_relat_1(k2_funct_1(A_745))=k2_relat_1(A_745) | ~v2_funct_1(A_745) | ~v1_funct_1(A_745) | ~v1_relat_1(A_745))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.58/3.86  tff(c_13125, plain, (![A_898]: (k9_relat_1(k2_funct_1(A_898), k2_relat_1(A_898))=k2_relat_1(k2_funct_1(A_898)) | ~v1_relat_1(k2_funct_1(A_898)) | ~v2_funct_1(A_898) | ~v1_funct_1(A_898) | ~v1_relat_1(A_898))), inference(superposition, [status(thm), theory('equality')], [c_11397, c_22])).
% 10.58/3.86  tff(c_13141, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11541, c_13125])).
% 10.58/3.86  tff(c_13148, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_13141])).
% 10.58/3.86  tff(c_13149, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_13148])).
% 10.58/3.86  tff(c_13152, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_13149])).
% 10.58/3.86  tff(c_13156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_13152])).
% 10.58/3.86  tff(c_13158, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_13148])).
% 10.58/3.86  tff(c_11362, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11353, c_11353, c_10])).
% 10.58/3.86  tff(c_11587, plain, (![A_768, B_769, C_770]: (k1_relset_1(A_768, B_769, C_770)=k1_relat_1(C_770) | ~m1_subset_1(C_770, k1_zfmisc_1(k2_zfmisc_1(A_768, B_769))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.58/3.86  tff(c_11602, plain, (![A_768, B_769]: (k1_relset_1(A_768, B_769, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_11364, c_11587])).
% 10.58/3.86  tff(c_11823, plain, (![A_801, B_802, C_803]: (m1_subset_1(k1_relset_1(A_801, B_802, C_803), k1_zfmisc_1(A_801)) | ~m1_subset_1(C_803, k1_zfmisc_1(k2_zfmisc_1(A_801, B_802))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.58/3.86  tff(c_11859, plain, (![A_768, B_769]: (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1(A_768)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_768, B_769))))), inference(superposition, [status(thm), theory('equality')], [c_11602, c_11823])).
% 10.58/3.86  tff(c_11877, plain, (![A_804]: (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1(A_804)))), inference(demodulation, [status(thm), theory('equality')], [c_11364, c_11859])).
% 10.58/3.86  tff(c_11941, plain, (![A_807]: (r1_tarski(k1_relat_1('#skF_3'), A_807))), inference(resolution, [status(thm)], [c_11877, c_16])).
% 10.58/3.86  tff(c_238, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_121, c_230])).
% 10.58/3.86  tff(c_11355, plain, (![A_5]: (A_5='#skF_3' | ~r1_tarski(A_5, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11353, c_11353, c_238])).
% 10.58/3.86  tff(c_11982, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_11941, c_11355])).
% 10.58/3.86  tff(c_13157, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_13148])).
% 10.58/3.86  tff(c_13162, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13157, c_28])).
% 10.58/3.86  tff(c_13169, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_13162])).
% 10.58/3.86  tff(c_13198, plain, (k10_relat_1('#skF_3', '#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13169, c_30])).
% 10.58/3.86  tff(c_13222, plain, (k10_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_11982, c_13198])).
% 10.58/3.86  tff(c_13228, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13222, c_13169])).
% 10.58/3.86  tff(c_11653, plain, (![A_781]: (m1_subset_1(A_781, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_781), k2_relat_1(A_781)))) | ~v1_funct_1(A_781) | ~v1_relat_1(A_781))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.58/3.86  tff(c_11681, plain, (![A_781]: (r1_tarski(A_781, k2_zfmisc_1(k1_relat_1(A_781), k2_relat_1(A_781))) | ~v1_funct_1(A_781) | ~v1_relat_1(A_781))), inference(resolution, [status(thm)], [c_11653, c_16])).
% 10.58/3.86  tff(c_13252, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13228, c_11681])).
% 10.58/3.86  tff(c_13278, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13158, c_171, c_11362, c_13252])).
% 10.58/3.86  tff(c_13280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11502, c_13278])).
% 10.58/3.86  tff(c_13281, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_11386])).
% 10.58/3.86  tff(c_13329, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13281, c_13281, c_11362])).
% 10.58/3.86  tff(c_13290, plain, (~r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13281, c_201])).
% 10.58/3.86  tff(c_13486, plain, (~r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13329, c_13290])).
% 10.58/3.86  tff(c_13293, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13281, c_160])).
% 10.58/3.86  tff(c_13297, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13281, c_70])).
% 10.58/3.86  tff(c_13296, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13281, c_64])).
% 10.58/3.86  tff(c_13406, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_13281, c_11364])).
% 10.58/3.86  tff(c_13527, plain, (![A_921, B_922, C_923]: (k2_relset_1(A_921, B_922, C_923)=k2_relat_1(C_923) | ~m1_subset_1(C_923, k1_zfmisc_1(k2_zfmisc_1(A_921, B_922))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.58/3.86  tff(c_13569, plain, (![A_927, B_928]: (k2_relset_1(A_927, B_928, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_13406, c_13527])).
% 10.58/3.86  tff(c_13294, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13281, c_62])).
% 10.58/3.86  tff(c_13573, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_13569, c_13294])).
% 10.58/3.86  tff(c_13344, plain, (![A_902]: (k1_relat_1(k2_funct_1(A_902))=k2_relat_1(A_902) | ~v2_funct_1(A_902) | ~v1_funct_1(A_902) | ~v1_relat_1(A_902))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.58/3.86  tff(c_15447, plain, (![A_1077]: (k9_relat_1(k2_funct_1(A_1077), k2_relat_1(A_1077))=k2_relat_1(k2_funct_1(A_1077)) | ~v1_relat_1(k2_funct_1(A_1077)) | ~v2_funct_1(A_1077) | ~v1_funct_1(A_1077) | ~v1_relat_1(A_1077))), inference(superposition, [status(thm), theory('equality')], [c_13344, c_22])).
% 10.58/3.86  tff(c_15463, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_13573, c_15447])).
% 10.58/3.86  tff(c_15470, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13293, c_13297, c_13296, c_15463])).
% 10.58/3.86  tff(c_15471, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_15470])).
% 10.58/3.86  tff(c_15474, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_15471])).
% 10.58/3.86  tff(c_15478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13293, c_13297, c_15474])).
% 10.58/3.86  tff(c_15480, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_15470])).
% 10.58/3.86  tff(c_13292, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13281, c_171])).
% 10.58/3.86  tff(c_13548, plain, (![A_924, B_925, C_926]: (k1_relset_1(A_924, B_925, C_926)=k1_relat_1(C_926) | ~m1_subset_1(C_926, k1_zfmisc_1(k2_zfmisc_1(A_924, B_925))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.58/3.86  tff(c_13567, plain, (![A_924, B_925]: (k1_relset_1(A_924, B_925, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_13406, c_13548])).
% 10.58/3.86  tff(c_13696, plain, (![A_947, B_948, C_949]: (m1_subset_1(k1_relset_1(A_947, B_948, C_949), k1_zfmisc_1(A_947)) | ~m1_subset_1(C_949, k1_zfmisc_1(k2_zfmisc_1(A_947, B_948))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.58/3.86  tff(c_13729, plain, (![A_924, B_925]: (m1_subset_1(k1_relat_1('#skF_1'), k1_zfmisc_1(A_924)) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_924, B_925))))), inference(superposition, [status(thm), theory('equality')], [c_13567, c_13696])).
% 10.58/3.86  tff(c_13745, plain, (![A_950]: (m1_subset_1(k1_relat_1('#skF_1'), k1_zfmisc_1(A_950)))), inference(demodulation, [status(thm), theory('equality')], [c_13406, c_13729])).
% 10.58/3.86  tff(c_13786, plain, (![A_951]: (r1_tarski(k1_relat_1('#skF_1'), A_951))), inference(resolution, [status(thm)], [c_13745, c_16])).
% 10.58/3.86  tff(c_13436, plain, (![A_5]: (A_5='#skF_1' | ~r1_tarski(A_5, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13281, c_13281, c_11355])).
% 10.58/3.86  tff(c_13813, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_13786, c_13436])).
% 10.58/3.86  tff(c_15479, plain, (k9_relat_1(k2_funct_1('#skF_1'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_15470])).
% 10.58/3.86  tff(c_15484, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k10_relat_1('#skF_1', '#skF_2') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15479, c_28])).
% 10.58/3.86  tff(c_15491, plain, (k2_relat_1(k2_funct_1('#skF_1'))=k10_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13293, c_13297, c_13296, c_15484])).
% 10.58/3.86  tff(c_15520, plain, (k10_relat_1('#skF_1', '#skF_2')=k1_relat_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15491, c_30])).
% 10.58/3.86  tff(c_15544, plain, (k10_relat_1('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13293, c_13297, c_13296, c_13813, c_15520])).
% 10.58/3.86  tff(c_15550, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15544, c_15491])).
% 10.58/3.86  tff(c_13450, plain, (![A_907]: (m1_subset_1(A_907, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_907), k2_relat_1(A_907)))) | ~v1_funct_1(A_907) | ~v1_relat_1(A_907))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.58/3.86  tff(c_13467, plain, (![A_907]: (r1_tarski(A_907, k2_zfmisc_1(k1_relat_1(A_907), k2_relat_1(A_907))) | ~v1_funct_1(A_907) | ~v1_relat_1(A_907))), inference(resolution, [status(thm)], [c_13450, c_16])).
% 10.58/3.86  tff(c_15574, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_1')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_15550, c_13467])).
% 10.58/3.86  tff(c_15600, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15480, c_13292, c_13329, c_15574])).
% 10.58/3.86  tff(c_15602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13486, c_15600])).
% 10.58/3.86  tff(c_15603, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_170])).
% 10.58/3.86  tff(c_15604, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_170])).
% 10.58/3.86  tff(c_34, plain, (![C_18, A_16, B_17]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.58/3.86  tff(c_15611, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_15604, c_34])).
% 10.58/3.86  tff(c_16947, plain, (![A_1188, B_1189, C_1190]: (k2_relset_1(A_1188, B_1189, C_1190)=k2_relat_1(C_1190) | ~m1_subset_1(C_1190, k1_zfmisc_1(k2_zfmisc_1(A_1188, B_1189))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.58/3.86  tff(c_16960, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_16947])).
% 10.58/3.86  tff(c_16974, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_16960])).
% 10.58/3.86  tff(c_15761, plain, (![A_1103, B_1104, C_1105]: (k2_relset_1(A_1103, B_1104, C_1105)=k2_relat_1(C_1105) | ~m1_subset_1(C_1105, k1_zfmisc_1(k2_zfmisc_1(A_1103, B_1104))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.58/3.86  tff(c_15774, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_15761])).
% 10.58/3.86  tff(c_15789, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_15774])).
% 10.58/3.86  tff(c_15851, plain, (![A_1108, B_1109, C_1110]: (k1_relset_1(A_1108, B_1109, C_1110)=k1_relat_1(C_1110) | ~m1_subset_1(C_1110, k1_zfmisc_1(k2_zfmisc_1(A_1108, B_1109))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.58/3.86  tff(c_15880, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_15604, c_15851])).
% 10.58/3.86  tff(c_16487, plain, (![B_1156, C_1157, A_1158]: (k1_xboole_0=B_1156 | v1_funct_2(C_1157, A_1158, B_1156) | k1_relset_1(A_1158, B_1156, C_1157)!=A_1158 | ~m1_subset_1(C_1157, k1_zfmisc_1(k2_zfmisc_1(A_1158, B_1156))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.58/3.86  tff(c_16500, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_15604, c_16487])).
% 10.58/3.86  tff(c_16524, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15880, c_16500])).
% 10.58/3.86  tff(c_16525, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_15603, c_16524])).
% 10.58/3.86  tff(c_16532, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_16525])).
% 10.58/3.86  tff(c_16535, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_16532])).
% 10.58/3.86  tff(c_16538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_15789, c_16535])).
% 10.58/3.86  tff(c_16539, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_16525])).
% 10.58/3.86  tff(c_16563, plain, (![A_5]: (r1_tarski('#skF_1', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_16539, c_121])).
% 10.58/3.86  tff(c_16565, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16539, c_16539, c_10])).
% 10.58/3.86  tff(c_15612, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_15604, c_16])).
% 10.58/3.86  tff(c_15639, plain, (![B_1081, A_1082]: (B_1081=A_1082 | ~r1_tarski(B_1081, A_1082) | ~r1_tarski(A_1082, B_1081))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.58/3.86  tff(c_15648, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_15612, c_15639])).
% 10.58/3.86  tff(c_15693, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_15648])).
% 10.58/3.86  tff(c_16675, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16565, c_15693])).
% 10.58/3.86  tff(c_16681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16563, c_16675])).
% 10.58/3.86  tff(c_16682, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_15648])).
% 10.58/3.86  tff(c_16686, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16682, c_15604])).
% 10.58/3.86  tff(c_16771, plain, (![A_1168, B_1169, C_1170]: (k1_relset_1(A_1168, B_1169, C_1170)=k1_relat_1(C_1170) | ~m1_subset_1(C_1170, k1_zfmisc_1(k2_zfmisc_1(A_1168, B_1169))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.58/3.86  tff(c_16806, plain, (![C_1173]: (k1_relset_1('#skF_2', '#skF_1', C_1173)=k1_relat_1(C_1173) | ~m1_subset_1(C_1173, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_16682, c_16771])).
% 10.58/3.86  tff(c_16818, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_16686, c_16806])).
% 10.58/3.86  tff(c_17116, plain, (![A_1206, B_1207, C_1208]: (m1_subset_1(k1_relset_1(A_1206, B_1207, C_1208), k1_zfmisc_1(A_1206)) | ~m1_subset_1(C_1208, k1_zfmisc_1(k2_zfmisc_1(A_1206, B_1207))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.58/3.86  tff(c_17166, plain, (m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16818, c_17116])).
% 10.58/3.86  tff(c_17193, plain, (m1_subset_1(k1_relat_1(k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16686, c_16682, c_17166])).
% 10.58/3.86  tff(c_17406, plain, (r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_17193, c_16])).
% 10.58/3.86  tff(c_17422, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_17406, c_2])).
% 10.58/3.86  tff(c_17954, plain, (~r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_17422])).
% 10.58/3.86  tff(c_17957, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_17954])).
% 10.58/3.86  tff(c_17960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_6, c_16974, c_17957])).
% 10.58/3.86  tff(c_17961, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_17422])).
% 10.58/3.86  tff(c_16793, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_16771])).
% 10.58/3.86  tff(c_17493, plain, (![B_1223, A_1224, C_1225]: (k1_xboole_0=B_1223 | k1_relset_1(A_1224, B_1223, C_1225)=A_1224 | ~v1_funct_2(C_1225, A_1224, B_1223) | ~m1_subset_1(C_1225, k1_zfmisc_1(k2_zfmisc_1(A_1224, B_1223))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.58/3.86  tff(c_17513, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_17493])).
% 10.58/3.86  tff(c_17532, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16793, c_17513])).
% 10.58/3.86  tff(c_17536, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_17532])).
% 10.58/3.86  tff(c_17172, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_16793, c_17116])).
% 10.58/3.86  tff(c_17197, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_17172])).
% 10.58/3.86  tff(c_17259, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_17197, c_16])).
% 10.58/3.86  tff(c_17347, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_17259, c_2])).
% 10.58/3.86  tff(c_17441, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_17347])).
% 10.58/3.86  tff(c_17538, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17536, c_17441])).
% 10.58/3.86  tff(c_17552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_17538])).
% 10.58/3.86  tff(c_17553, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_17532])).
% 10.58/3.86  tff(c_16697, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16682, c_8])).
% 10.58/3.86  tff(c_16740, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16697])).
% 10.58/3.86  tff(c_17572, plain, (k2_funct_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17553, c_16740])).
% 10.58/3.86  tff(c_17582, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17553, c_17553, c_12])).
% 10.58/3.86  tff(c_17638, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_17582, c_16682])).
% 10.58/3.86  tff(c_17640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17572, c_17638])).
% 10.58/3.86  tff(c_17641, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_17347])).
% 10.58/3.86  tff(c_17984, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_17961, c_22])).
% 10.58/3.86  tff(c_17999, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15611, c_17984])).
% 10.58/3.86  tff(c_18069, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_17999])).
% 10.58/3.86  tff(c_18075, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_18069])).
% 10.58/3.86  tff(c_18237, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18075, c_30])).
% 10.58/3.86  tff(c_18253, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_17641, c_18237])).
% 10.58/3.86  tff(c_18264, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18253, c_18075])).
% 10.58/3.86  tff(c_56, plain, (![A_31]: (v1_funct_2(A_31, k1_relat_1(A_31), k2_relat_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.58/3.86  tff(c_18285, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18264, c_56])).
% 10.58/3.86  tff(c_18300, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15611, c_171, c_17961, c_18285])).
% 10.58/3.86  tff(c_18302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15603, c_18300])).
% 10.58/3.86  tff(c_18303, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_16697])).
% 10.58/3.86  tff(c_18351, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_18303])).
% 10.58/3.86  tff(c_18362, plain, (![A_5]: (r1_tarski('#skF_1', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_18351, c_121])).
% 10.58/3.86  tff(c_18365, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18351, c_18351, c_12])).
% 10.58/3.86  tff(c_15649, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_120, c_15639])).
% 10.58/3.86  tff(c_15675, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_15649])).
% 10.58/3.86  tff(c_18436, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18365, c_15675])).
% 10.58/3.86  tff(c_18441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18362, c_18436])).
% 10.58/3.86  tff(c_18442, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_18303])).
% 10.58/3.86  tff(c_18453, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_18442, c_121])).
% 10.58/3.86  tff(c_18455, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18442, c_18442, c_10])).
% 10.58/3.86  tff(c_18565, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18455, c_15675])).
% 10.58/3.86  tff(c_18570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18453, c_18565])).
% 10.58/3.86  tff(c_18571, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_15649])).
% 10.58/3.86  tff(c_18574, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18571, c_66])).
% 10.58/3.86  tff(c_18691, plain, (![A_1278, B_1279, C_1280]: (k2_relset_1(A_1278, B_1279, C_1280)=k2_relat_1(C_1280) | ~m1_subset_1(C_1280, k1_zfmisc_1(k2_zfmisc_1(A_1278, B_1279))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.58/3.86  tff(c_18893, plain, (![C_1308]: (k2_relset_1('#skF_1', '#skF_2', C_1308)=k2_relat_1(C_1308) | ~m1_subset_1(C_1308, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18571, c_18691])).
% 10.58/3.86  tff(c_18896, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18574, c_18893])).
% 10.58/3.86  tff(c_18906, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_18896])).
% 10.58/3.86  tff(c_18761, plain, (![A_1289, B_1290, C_1291]: (k1_relset_1(A_1289, B_1290, C_1291)=k1_relat_1(C_1291) | ~m1_subset_1(C_1291, k1_zfmisc_1(k2_zfmisc_1(A_1289, B_1290))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.58/3.86  tff(c_18786, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_15604, c_18761])).
% 10.58/3.86  tff(c_20653, plain, (![B_1388, C_1389, A_1390]: (k1_xboole_0=B_1388 | v1_funct_2(C_1389, A_1390, B_1388) | k1_relset_1(A_1390, B_1388, C_1389)!=A_1390 | ~m1_subset_1(C_1389, k1_zfmisc_1(k2_zfmisc_1(A_1390, B_1388))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.58/3.86  tff(c_20666, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_15604, c_20653])).
% 10.58/3.86  tff(c_20684, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18786, c_20666])).
% 10.58/3.86  tff(c_20685, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_15603, c_20684])).
% 10.58/3.86  tff(c_20690, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_20685])).
% 10.58/3.86  tff(c_20693, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_20690])).
% 10.58/3.86  tff(c_20696, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_18906, c_20693])).
% 10.58/3.86  tff(c_20697, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_20685])).
% 10.58/3.86  tff(c_18585, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_18571, c_8])).
% 10.58/3.86  tff(c_18642, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_18585])).
% 10.58/3.86  tff(c_20718, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20697, c_18642])).
% 10.58/3.86  tff(c_20728, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20697, c_20697, c_12])).
% 10.58/3.86  tff(c_20829, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20728, c_18571])).
% 10.58/3.86  tff(c_20831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20718, c_20829])).
% 10.58/3.86  tff(c_20833, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_18585])).
% 10.58/3.86  tff(c_20844, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20833, c_20833, c_12])).
% 10.58/3.86  tff(c_20832, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_18585])).
% 10.58/3.86  tff(c_21148, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20833, c_20833, c_20832])).
% 10.58/3.86  tff(c_21149, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_21148])).
% 10.58/3.86  tff(c_20841, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_20833, c_121])).
% 10.58/3.86  tff(c_20890, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20833, c_20833, c_20832])).
% 10.58/3.86  tff(c_20891, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_20890])).
% 10.58/3.86  tff(c_20889, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_15648])).
% 10.58/3.86  tff(c_20973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20841, c_20844, c_20891, c_20889])).
% 10.58/3.86  tff(c_20974, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_20890])).
% 10.58/3.86  tff(c_20977, plain, (![A_5]: (r1_tarski('#skF_1', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_20974, c_20841])).
% 10.58/3.86  tff(c_20843, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20833, c_20833, c_10])).
% 10.58/3.86  tff(c_21040, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20974, c_20974, c_20843])).
% 10.58/3.86  tff(c_21145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20977, c_21040, c_20974, c_20889])).
% 10.58/3.86  tff(c_21146, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_15648])).
% 10.58/3.86  tff(c_21165, plain, (k2_zfmisc_1('#skF_3', '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21149, c_21146])).
% 10.58/3.86  tff(c_21239, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20844, c_21165])).
% 10.58/3.86  tff(c_21247, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21239, c_32])).
% 10.58/3.86  tff(c_21257, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_70, c_64, c_21247])).
% 10.58/3.86  tff(c_20845, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_20833, c_14])).
% 10.58/3.86  tff(c_21313, plain, (![A_1421, B_1422, C_1423]: (k2_relset_1(A_1421, B_1422, C_1423)=k2_relat_1(C_1423) | ~m1_subset_1(C_1423, k1_zfmisc_1(k2_zfmisc_1(A_1421, B_1422))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.58/3.86  tff(c_21323, plain, (![A_1421, B_1422]: (k2_relset_1(A_1421, B_1422, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20845, c_21313])).
% 10.58/3.86  tff(c_21345, plain, (![A_1426, B_1427]: (k2_relset_1(A_1426, B_1427, '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21257, c_21323])).
% 10.58/3.86  tff(c_21168, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21149, c_21149, c_62])).
% 10.58/3.86  tff(c_21349, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_21345, c_21168])).
% 10.58/3.86  tff(c_21400, plain, (![A_1430, B_1431, C_1432]: (k1_relset_1(A_1430, B_1431, C_1432)=k1_relat_1(C_1432) | ~m1_subset_1(C_1432, k1_zfmisc_1(k2_zfmisc_1(A_1430, B_1431))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.58/3.86  tff(c_21410, plain, (![A_1430, B_1431]: (k1_relset_1(A_1430, B_1431, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20845, c_21400])).
% 10.58/3.86  tff(c_21416, plain, (![A_1430, B_1431]: (k1_relset_1(A_1430, B_1431, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21349, c_21410])).
% 10.58/3.86  tff(c_46, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.58/3.86  tff(c_74, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 10.58/3.86  tff(c_21899, plain, (![C_1483, B_1484]: (v1_funct_2(C_1483, '#skF_3', B_1484) | k1_relset_1('#skF_3', B_1484, C_1483)!='#skF_3' | ~m1_subset_1(C_1483, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_20833, c_20833, c_20833, c_20833, c_74])).
% 10.58/3.86  tff(c_21905, plain, (![B_1484]: (v1_funct_2('#skF_3', '#skF_3', B_1484) | k1_relset_1('#skF_3', B_1484, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_20845, c_21899])).
% 10.58/3.86  tff(c_21913, plain, (![B_1484]: (v1_funct_2('#skF_3', '#skF_3', B_1484))), inference(demodulation, [status(thm), theory('equality')], [c_21416, c_21905])).
% 10.58/3.86  tff(c_21167, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21149, c_15603])).
% 10.58/3.86  tff(c_21276, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21239, c_21167])).
% 10.58/3.86  tff(c_21918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21913, c_21276])).
% 10.58/3.86  tff(c_21919, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_21148])).
% 10.58/3.86  tff(c_21920, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_21148])).
% 10.58/3.86  tff(c_21943, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21919, c_21920])).
% 10.58/3.86  tff(c_42, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.58/3.86  tff(c_72, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_42])).
% 10.58/3.86  tff(c_20842, plain, (![A_28]: (v1_funct_2('#skF_3', A_28, '#skF_3') | A_28='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20833, c_20833, c_20833, c_72])).
% 10.58/3.86  tff(c_22147, plain, (![A_1495]: (v1_funct_2('#skF_1', A_1495, '#skF_1') | A_1495='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21919, c_21919, c_21919, c_20842])).
% 10.58/3.86  tff(c_22016, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21919, c_21919, c_20843])).
% 10.58/3.86  tff(c_22039, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22016, c_21919, c_21146])).
% 10.58/3.86  tff(c_21932, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21919, c_15603])).
% 10.58/3.86  tff(c_22105, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22039, c_21932])).
% 10.58/3.86  tff(c_22150, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_22147, c_22105])).
% 10.58/3.86  tff(c_22154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21943, c_22150])).
% 10.58/3.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.58/3.86  
% 10.58/3.86  Inference rules
% 10.58/3.86  ----------------------
% 10.58/3.86  #Ref     : 0
% 10.58/3.86  #Sup     : 4652
% 10.58/3.86  #Fact    : 0
% 10.58/3.86  #Define  : 0
% 10.58/3.86  #Split   : 47
% 10.58/3.86  #Chain   : 0
% 10.58/3.86  #Close   : 0
% 10.58/3.86  
% 10.58/3.86  Ordering : KBO
% 10.58/3.86  
% 10.58/3.86  Simplification rules
% 10.58/3.86  ----------------------
% 10.58/3.86  #Subsume      : 489
% 10.58/3.86  #Demod        : 7056
% 10.58/3.86  #Tautology    : 2458
% 10.58/3.86  #SimpNegUnit  : 39
% 10.58/3.86  #BackRed      : 741
% 10.58/3.86  
% 10.58/3.86  #Partial instantiations: 0
% 10.58/3.86  #Strategies tried      : 1
% 10.58/3.86  
% 10.58/3.86  Timing (in seconds)
% 10.58/3.86  ----------------------
% 10.58/3.86  Preprocessing        : 0.35
% 10.58/3.86  Parsing              : 0.18
% 10.58/3.86  CNF conversion       : 0.02
% 10.58/3.86  Main loop            : 2.62
% 10.58/3.86  Inferencing          : 0.84
% 10.58/3.86  Reduction            : 0.99
% 10.58/3.86  Demodulation         : 0.73
% 10.58/3.86  BG Simplification    : 0.09
% 10.58/3.86  Subsumption          : 0.48
% 10.58/3.86  Abstraction          : 0.12
% 10.58/3.86  MUC search           : 0.00
% 10.58/3.86  Cooper               : 0.00
% 10.58/3.86  Total                : 3.12
% 10.58/3.86  Index Insertion      : 0.00
% 10.58/3.86  Index Deletion       : 0.00
% 10.58/3.86  Index Matching       : 0.00
% 10.58/3.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
