%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:34 EST 2020

% Result     : Theorem 10.88s
% Output     : CNFRefutation 11.00s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 589 expanded)
%              Number of leaves         :   47 ( 213 expanded)
%              Depth                    :   13
%              Number of atoms          :  281 (1525 expanded)
%              Number of equality atoms :   89 ( 384 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_216,negated_conjecture,(
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

tff(f_144,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_180,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_154,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_199,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_170,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_134,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_168,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_164,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_94,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_3136,plain,(
    ! [C_231,A_232,B_233] :
      ( v4_relat_1(C_231,A_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3152,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_3136])).

tff(c_2945,plain,(
    ! [C_213,A_214,B_215] :
      ( v1_relat_1(C_213)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2958,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_2945])).

tff(c_14,plain,(
    ! [A_5] :
      ( k1_relat_1(A_5) != k1_xboole_0
      | k1_xboole_0 = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2974,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2958,c_14])).

tff(c_2992,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2974])).

tff(c_98,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_30,plain,(
    ! [A_10] :
      ( v1_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_88,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_303,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_306,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_303])).

tff(c_309,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_306])).

tff(c_323,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_329,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_323])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_329])).

tff(c_337,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_372,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_381,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_372])).

tff(c_484,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_relat_1(C_78,A_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_492,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_484])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_589,plain,(
    ! [A_96] :
      ( k4_relat_1(A_96) = k2_funct_1(A_96)
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_592,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_589])).

tff(c_595,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_98,c_592])).

tff(c_8,plain,(
    ! [A_4] :
      ( k2_relat_1(k4_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_599,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_8])).

tff(c_609,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_599])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_605,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_6])).

tff(c_613,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_605])).

tff(c_90,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1309,plain,(
    ! [A_127,B_128,C_129] :
      ( k2_relset_1(A_127,B_128,C_129) = k2_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1324,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_1309])).

tff(c_1333,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1324])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_relat_1(k4_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_602,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_10])).

tff(c_611,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_602])).

tff(c_1339,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1333,c_611])).

tff(c_70,plain,(
    ! [A_39] :
      ( m1_subset_1(A_39,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_39),k2_relat_1(A_39))))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1368,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1339,c_70])).

tff(c_1390,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_337,c_609,c_1368])).

tff(c_58,plain,(
    ! [D_33,C_32,B_31,A_30] :
      ( m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(C_32,B_31)))
      | ~ r1_tarski(k2_relat_1(D_33),B_31)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(C_32,A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1680,plain,(
    ! [B_31] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_31)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),B_31) ) ),
    inference(resolution,[status(thm)],[c_1390,c_58])).

tff(c_2878,plain,(
    ! [B_211] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_211)))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_1680])).

tff(c_336,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_371,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_2911,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2878,c_371])).

tff(c_2917,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_2911])).

tff(c_2922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_492,c_2917])).

tff(c_2924,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_2955,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2924,c_2945])).

tff(c_3260,plain,(
    ! [A_246] :
      ( k4_relat_1(A_246) = k2_funct_1(A_246)
      | ~ v2_funct_1(A_246)
      | ~ v1_funct_1(A_246)
      | ~ v1_relat_1(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3263,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_3260])).

tff(c_3266,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2958,c_98,c_3263])).

tff(c_3270,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3266,c_8])).

tff(c_3280,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2958,c_3270])).

tff(c_3621,plain,(
    ! [A_266,B_267,C_268] :
      ( k2_relset_1(A_266,B_267,C_268) = k2_relat_1(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3633,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_3621])).

tff(c_3641,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3633])).

tff(c_3273,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3266,c_10])).

tff(c_3282,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2958,c_3273])).

tff(c_3647,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3641,c_3282])).

tff(c_72,plain,(
    ! [A_39] :
      ( v1_funct_2(A_39,k1_relat_1(A_39),k2_relat_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_3674,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3647,c_72])).

tff(c_3691,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2955,c_337,c_3280,c_3674])).

tff(c_3706,plain,(
    ! [A_269] :
      ( m1_subset_1(A_269,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_269),k2_relat_1(A_269))))
      | ~ v1_funct_1(A_269)
      | ~ v1_relat_1(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_3733,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3280,c_3706])).

tff(c_3761,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2955,c_337,c_3647,c_3733])).

tff(c_4429,plain,(
    ! [B_310,D_311,A_312,C_313] :
      ( k1_xboole_0 = B_310
      | v1_funct_2(D_311,A_312,C_313)
      | ~ r1_tarski(B_310,C_313)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(k2_zfmisc_1(A_312,B_310)))
      | ~ v1_funct_2(D_311,A_312,B_310)
      | ~ v1_funct_1(D_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_15505,plain,(
    ! [B_541,D_542,A_543,A_544] :
      ( k1_relat_1(B_541) = k1_xboole_0
      | v1_funct_2(D_542,A_543,A_544)
      | ~ m1_subset_1(D_542,k1_zfmisc_1(k2_zfmisc_1(A_543,k1_relat_1(B_541))))
      | ~ v1_funct_2(D_542,A_543,k1_relat_1(B_541))
      | ~ v1_funct_1(D_542)
      | ~ v4_relat_1(B_541,A_544)
      | ~ v1_relat_1(B_541) ) ),
    inference(resolution,[status(thm)],[c_4,c_4429])).

tff(c_15549,plain,(
    ! [A_544] :
      ( k1_relat_1('#skF_3') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_544)
      | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v4_relat_1('#skF_3',A_544)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3761,c_15505])).

tff(c_15596,plain,(
    ! [A_544] :
      ( k1_relat_1('#skF_3') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_544)
      | ~ v4_relat_1('#skF_3',A_544) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2958,c_337,c_3691,c_15549])).

tff(c_15611,plain,(
    ! [A_545] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_545)
      | ~ v4_relat_1('#skF_3',A_545) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2992,c_15596])).

tff(c_2923,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_15614,plain,(
    ~ v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_15611,c_2923])).

tff(c_15618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3152,c_15614])).

tff(c_15619,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2974])).

tff(c_15620,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2974])).

tff(c_15640,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15619,c_15620])).

tff(c_18,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) = k1_xboole_0
      | k1_relat_1(A_6) != k1_xboole_0
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2972,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2958,c_18])).

tff(c_15646,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15640,c_15619,c_15619,c_2972])).

tff(c_12,plain,(
    ! [A_5] :
      ( k2_relat_1(A_5) != k1_xboole_0
      | k1_xboole_0 = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2973,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2958,c_12])).

tff(c_2991,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2973])).

tff(c_15621,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15619,c_2991])).

tff(c_15684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15646,c_15621])).

tff(c_15685,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2973])).

tff(c_15686,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2973])).

tff(c_15730,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15685,c_15686])).

tff(c_16548,plain,(
    ! [A_604,B_605,C_606] :
      ( k2_relset_1(A_604,B_605,C_606) = k2_relat_1(C_606)
      | ~ m1_subset_1(C_606,k1_zfmisc_1(k2_zfmisc_1(A_604,B_605))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_16560,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_16548])).

tff(c_16568,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15730,c_90,c_16560])).

tff(c_114,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_120,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_26])).

tff(c_68,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_48,plain,(
    ! [A_20] : k2_funct_1(k6_relat_1(A_20)) = k6_relat_1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_178,plain,(
    ! [A_51] : k2_funct_1(k6_partfun1(A_51)) = k6_partfun1(A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_48])).

tff(c_187,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_178])).

tff(c_190,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_187])).

tff(c_15718,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15685,c_15685,c_190])).

tff(c_15742,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15718,c_2923])).

tff(c_16574,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16568,c_15742])).

tff(c_20,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    ! [A_7] : k1_relat_1(k6_partfun1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_20])).

tff(c_34,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_103,plain,(
    ! [A_11] : v1_relat_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_34])).

tff(c_206,plain,(
    ! [A_53] :
      ( k1_relat_1(A_53) != k1_xboole_0
      | k1_xboole_0 = A_53
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_218,plain,(
    ! [A_11] :
      ( k1_relat_1(k6_partfun1(A_11)) != k1_xboole_0
      | k6_partfun1(A_11) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_103,c_206])).

tff(c_229,plain,(
    ! [A_54] :
      ( k1_xboole_0 != A_54
      | k6_partfun1(A_54) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_218])).

tff(c_64,plain,(
    ! [A_37] : v1_partfun1(k6_partfun1(A_37),A_37) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_244,plain,(
    ! [A_54] :
      ( v1_partfun1(k1_xboole_0,A_54)
      | k1_xboole_0 != A_54 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_64])).

tff(c_15826,plain,(
    v1_partfun1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15685,c_15685,c_244])).

tff(c_15741,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15718,c_2924])).

tff(c_16573,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16568,c_15741])).

tff(c_16737,plain,(
    ! [C_612,A_613,B_614] :
      ( v1_funct_2(C_612,A_613,B_614)
      | ~ v1_partfun1(C_612,A_613)
      | ~ v1_funct_1(C_612)
      | ~ m1_subset_1(C_612,k1_zfmisc_1(k2_zfmisc_1(A_613,B_614))) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_16743,plain,
    ( v1_funct_2('#skF_3','#skF_3','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16573,c_16737])).

tff(c_16756,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_15826,c_16743])).

tff(c_16758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16574,c_16756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:05:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.88/4.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.00/4.49  
% 11.00/4.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.00/4.49  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.00/4.49  
% 11.00/4.49  %Foreground sorts:
% 11.00/4.49  
% 11.00/4.49  
% 11.00/4.49  %Background operators:
% 11.00/4.49  
% 11.00/4.49  
% 11.00/4.49  %Foreground operators:
% 11.00/4.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.00/4.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.00/4.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.00/4.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.00/4.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.00/4.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.00/4.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.00/4.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.00/4.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.00/4.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.00/4.49  tff('#skF_2', type, '#skF_2': $i).
% 11.00/4.49  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.00/4.49  tff('#skF_3', type, '#skF_3': $i).
% 11.00/4.49  tff('#skF_1', type, '#skF_1': $i).
% 11.00/4.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.00/4.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.00/4.49  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.00/4.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.00/4.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.00/4.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.00/4.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.00/4.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.00/4.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.00/4.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.00/4.49  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 11.00/4.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.00/4.49  
% 11.00/4.51  tff(f_216, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 11.00/4.51  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.00/4.51  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.00/4.51  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 11.00/4.51  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.00/4.51  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 11.00/4.51  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 11.00/4.51  tff(f_41, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 11.00/4.51  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 11.00/4.51  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.00/4.51  tff(f_180, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 11.00/4.51  tff(f_154, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 11.00/4.51  tff(f_199, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 11.00/4.51  tff(f_55, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 11.00/4.51  tff(f_170, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.00/4.51  tff(f_64, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 11.00/4.51  tff(f_134, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 11.00/4.51  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 11.00/4.51  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 11.00/4.51  tff(f_168, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 11.00/4.51  tff(f_164, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 11.00/4.51  tff(c_94, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.00/4.51  tff(c_3136, plain, (![C_231, A_232, B_233]: (v4_relat_1(C_231, A_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.00/4.51  tff(c_3152, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_94, c_3136])).
% 11.00/4.51  tff(c_2945, plain, (![C_213, A_214, B_215]: (v1_relat_1(C_213) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.00/4.51  tff(c_2958, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_2945])).
% 11.00/4.51  tff(c_14, plain, (![A_5]: (k1_relat_1(A_5)!=k1_xboole_0 | k1_xboole_0=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.00/4.51  tff(c_2974, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2958, c_14])).
% 11.00/4.51  tff(c_2992, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2974])).
% 11.00/4.51  tff(c_98, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.00/4.51  tff(c_30, plain, (![A_10]: (v1_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.00/4.51  tff(c_88, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.00/4.51  tff(c_303, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_88])).
% 11.00/4.51  tff(c_306, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_303])).
% 11.00/4.51  tff(c_309, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_306])).
% 11.00/4.51  tff(c_323, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.00/4.51  tff(c_329, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_323])).
% 11.00/4.51  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_329])).
% 11.00/4.51  tff(c_337, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_88])).
% 11.00/4.51  tff(c_372, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.00/4.51  tff(c_381, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_372])).
% 11.00/4.51  tff(c_484, plain, (![C_78, A_79, B_80]: (v4_relat_1(C_78, A_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.00/4.51  tff(c_492, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_94, c_484])).
% 11.00/4.51  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.00/4.51  tff(c_92, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.00/4.51  tff(c_589, plain, (![A_96]: (k4_relat_1(A_96)=k2_funct_1(A_96) | ~v2_funct_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.00/4.51  tff(c_592, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_589])).
% 11.00/4.51  tff(c_595, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_98, c_592])).
% 11.00/4.51  tff(c_8, plain, (![A_4]: (k2_relat_1(k4_relat_1(A_4))=k1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.00/4.51  tff(c_599, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_595, c_8])).
% 11.00/4.51  tff(c_609, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_599])).
% 11.00/4.51  tff(c_6, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.00/4.51  tff(c_605, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_595, c_6])).
% 11.00/4.51  tff(c_613, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_381, c_605])).
% 11.00/4.51  tff(c_90, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.00/4.51  tff(c_1309, plain, (![A_127, B_128, C_129]: (k2_relset_1(A_127, B_128, C_129)=k2_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.00/4.51  tff(c_1324, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_1309])).
% 11.00/4.51  tff(c_1333, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1324])).
% 11.00/4.51  tff(c_10, plain, (![A_4]: (k1_relat_1(k4_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.00/4.51  tff(c_602, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_595, c_10])).
% 11.00/4.51  tff(c_611, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_381, c_602])).
% 11.00/4.51  tff(c_1339, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1333, c_611])).
% 11.00/4.51  tff(c_70, plain, (![A_39]: (m1_subset_1(A_39, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_39), k2_relat_1(A_39)))) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_180])).
% 11.00/4.52  tff(c_1368, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1339, c_70])).
% 11.00/4.52  tff(c_1390, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_613, c_337, c_609, c_1368])).
% 11.00/4.52  tff(c_58, plain, (![D_33, C_32, B_31, A_30]: (m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(C_32, B_31))) | ~r1_tarski(k2_relat_1(D_33), B_31) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(C_32, A_30))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.00/4.52  tff(c_1680, plain, (![B_31]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_31))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), B_31))), inference(resolution, [status(thm)], [c_1390, c_58])).
% 11.00/4.52  tff(c_2878, plain, (![B_211]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_211))) | ~r1_tarski(k1_relat_1('#skF_3'), B_211))), inference(demodulation, [status(thm), theory('equality')], [c_609, c_1680])).
% 11.00/4.52  tff(c_336, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_88])).
% 11.00/4.52  tff(c_371, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_336])).
% 11.00/4.52  tff(c_2911, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2878, c_371])).
% 11.00/4.52  tff(c_2917, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_2911])).
% 11.00/4.52  tff(c_2922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_381, c_492, c_2917])).
% 11.00/4.52  tff(c_2924, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_336])).
% 11.00/4.52  tff(c_2955, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2924, c_2945])).
% 11.00/4.52  tff(c_3260, plain, (![A_246]: (k4_relat_1(A_246)=k2_funct_1(A_246) | ~v2_funct_1(A_246) | ~v1_funct_1(A_246) | ~v1_relat_1(A_246))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.00/4.52  tff(c_3263, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_3260])).
% 11.00/4.52  tff(c_3266, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2958, c_98, c_3263])).
% 11.00/4.52  tff(c_3270, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3266, c_8])).
% 11.00/4.52  tff(c_3280, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2958, c_3270])).
% 11.00/4.52  tff(c_3621, plain, (![A_266, B_267, C_268]: (k2_relset_1(A_266, B_267, C_268)=k2_relat_1(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.00/4.52  tff(c_3633, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_3621])).
% 11.00/4.52  tff(c_3641, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3633])).
% 11.00/4.52  tff(c_3273, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3266, c_10])).
% 11.00/4.52  tff(c_3282, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2958, c_3273])).
% 11.00/4.52  tff(c_3647, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3641, c_3282])).
% 11.00/4.52  tff(c_72, plain, (![A_39]: (v1_funct_2(A_39, k1_relat_1(A_39), k2_relat_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_180])).
% 11.00/4.52  tff(c_3674, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3647, c_72])).
% 11.00/4.52  tff(c_3691, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2955, c_337, c_3280, c_3674])).
% 11.00/4.52  tff(c_3706, plain, (![A_269]: (m1_subset_1(A_269, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_269), k2_relat_1(A_269)))) | ~v1_funct_1(A_269) | ~v1_relat_1(A_269))), inference(cnfTransformation, [status(thm)], [f_180])).
% 11.00/4.52  tff(c_3733, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3280, c_3706])).
% 11.00/4.52  tff(c_3761, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2955, c_337, c_3647, c_3733])).
% 11.00/4.52  tff(c_4429, plain, (![B_310, D_311, A_312, C_313]: (k1_xboole_0=B_310 | v1_funct_2(D_311, A_312, C_313) | ~r1_tarski(B_310, C_313) | ~m1_subset_1(D_311, k1_zfmisc_1(k2_zfmisc_1(A_312, B_310))) | ~v1_funct_2(D_311, A_312, B_310) | ~v1_funct_1(D_311))), inference(cnfTransformation, [status(thm)], [f_199])).
% 11.00/4.52  tff(c_15505, plain, (![B_541, D_542, A_543, A_544]: (k1_relat_1(B_541)=k1_xboole_0 | v1_funct_2(D_542, A_543, A_544) | ~m1_subset_1(D_542, k1_zfmisc_1(k2_zfmisc_1(A_543, k1_relat_1(B_541)))) | ~v1_funct_2(D_542, A_543, k1_relat_1(B_541)) | ~v1_funct_1(D_542) | ~v4_relat_1(B_541, A_544) | ~v1_relat_1(B_541))), inference(resolution, [status(thm)], [c_4, c_4429])).
% 11.00/4.52  tff(c_15549, plain, (![A_544]: (k1_relat_1('#skF_3')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_544) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v4_relat_1('#skF_3', A_544) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3761, c_15505])).
% 11.00/4.52  tff(c_15596, plain, (![A_544]: (k1_relat_1('#skF_3')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_544) | ~v4_relat_1('#skF_3', A_544))), inference(demodulation, [status(thm), theory('equality')], [c_2958, c_337, c_3691, c_15549])).
% 11.00/4.52  tff(c_15611, plain, (![A_545]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_545) | ~v4_relat_1('#skF_3', A_545))), inference(negUnitSimplification, [status(thm)], [c_2992, c_15596])).
% 11.00/4.52  tff(c_2923, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_336])).
% 11.00/4.52  tff(c_15614, plain, (~v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_15611, c_2923])).
% 11.00/4.52  tff(c_15618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3152, c_15614])).
% 11.00/4.52  tff(c_15619, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2974])).
% 11.00/4.52  tff(c_15620, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2974])).
% 11.00/4.52  tff(c_15640, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15619, c_15620])).
% 11.00/4.52  tff(c_18, plain, (![A_6]: (k2_relat_1(A_6)=k1_xboole_0 | k1_relat_1(A_6)!=k1_xboole_0 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.00/4.52  tff(c_2972, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2958, c_18])).
% 11.00/4.52  tff(c_15646, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15640, c_15619, c_15619, c_2972])).
% 11.00/4.52  tff(c_12, plain, (![A_5]: (k2_relat_1(A_5)!=k1_xboole_0 | k1_xboole_0=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.00/4.52  tff(c_2973, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2958, c_12])).
% 11.00/4.52  tff(c_2991, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2973])).
% 11.00/4.52  tff(c_15621, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15619, c_2991])).
% 11.00/4.52  tff(c_15684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15646, c_15621])).
% 11.00/4.52  tff(c_15685, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2973])).
% 11.00/4.52  tff(c_15686, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2973])).
% 11.00/4.52  tff(c_15730, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15685, c_15686])).
% 11.00/4.52  tff(c_16548, plain, (![A_604, B_605, C_606]: (k2_relset_1(A_604, B_605, C_606)=k2_relat_1(C_606) | ~m1_subset_1(C_606, k1_zfmisc_1(k2_zfmisc_1(A_604, B_605))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.00/4.52  tff(c_16560, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_16548])).
% 11.00/4.52  tff(c_16568, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15730, c_90, c_16560])).
% 11.00/4.52  tff(c_114, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.00/4.52  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.00/4.52  tff(c_120, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_114, c_26])).
% 11.00/4.52  tff(c_68, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_170])).
% 11.00/4.52  tff(c_48, plain, (![A_20]: (k2_funct_1(k6_relat_1(A_20))=k6_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_134])).
% 11.00/4.52  tff(c_178, plain, (![A_51]: (k2_funct_1(k6_partfun1(A_51))=k6_partfun1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_48])).
% 11.00/4.52  tff(c_187, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_120, c_178])).
% 11.00/4.52  tff(c_190, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_187])).
% 11.00/4.52  tff(c_15718, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15685, c_15685, c_190])).
% 11.00/4.52  tff(c_15742, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15718, c_2923])).
% 11.00/4.52  tff(c_16574, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16568, c_15742])).
% 11.00/4.52  tff(c_20, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.00/4.52  tff(c_106, plain, (![A_7]: (k1_relat_1(k6_partfun1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_20])).
% 11.00/4.52  tff(c_34, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.00/4.52  tff(c_103, plain, (![A_11]: (v1_relat_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_34])).
% 11.00/4.52  tff(c_206, plain, (![A_53]: (k1_relat_1(A_53)!=k1_xboole_0 | k1_xboole_0=A_53 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.00/4.52  tff(c_218, plain, (![A_11]: (k1_relat_1(k6_partfun1(A_11))!=k1_xboole_0 | k6_partfun1(A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_103, c_206])).
% 11.00/4.52  tff(c_229, plain, (![A_54]: (k1_xboole_0!=A_54 | k6_partfun1(A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_106, c_218])).
% 11.00/4.52  tff(c_64, plain, (![A_37]: (v1_partfun1(k6_partfun1(A_37), A_37))), inference(cnfTransformation, [status(thm)], [f_168])).
% 11.00/4.52  tff(c_244, plain, (![A_54]: (v1_partfun1(k1_xboole_0, A_54) | k1_xboole_0!=A_54)), inference(superposition, [status(thm), theory('equality')], [c_229, c_64])).
% 11.00/4.52  tff(c_15826, plain, (v1_partfun1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15685, c_15685, c_244])).
% 11.00/4.52  tff(c_15741, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15718, c_2924])).
% 11.00/4.52  tff(c_16573, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16568, c_15741])).
% 11.00/4.52  tff(c_16737, plain, (![C_612, A_613, B_614]: (v1_funct_2(C_612, A_613, B_614) | ~v1_partfun1(C_612, A_613) | ~v1_funct_1(C_612) | ~m1_subset_1(C_612, k1_zfmisc_1(k2_zfmisc_1(A_613, B_614))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 11.00/4.52  tff(c_16743, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16573, c_16737])).
% 11.00/4.52  tff(c_16756, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_15826, c_16743])).
% 11.00/4.52  tff(c_16758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16574, c_16756])).
% 11.00/4.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.00/4.52  
% 11.00/4.52  Inference rules
% 11.00/4.52  ----------------------
% 11.00/4.52  #Ref     : 0
% 11.00/4.52  #Sup     : 3840
% 11.00/4.52  #Fact    : 0
% 11.00/4.52  #Define  : 0
% 11.00/4.52  #Split   : 33
% 11.00/4.52  #Chain   : 0
% 11.00/4.52  #Close   : 0
% 11.00/4.52  
% 11.00/4.52  Ordering : KBO
% 11.00/4.52  
% 11.00/4.52  Simplification rules
% 11.00/4.52  ----------------------
% 11.00/4.52  #Subsume      : 1145
% 11.00/4.52  #Demod        : 5975
% 11.00/4.52  #Tautology    : 1360
% 11.00/4.52  #SimpNegUnit  : 138
% 11.00/4.52  #BackRed      : 86
% 11.00/4.52  
% 11.00/4.52  #Partial instantiations: 0
% 11.00/4.52  #Strategies tried      : 1
% 11.00/4.52  
% 11.00/4.52  Timing (in seconds)
% 11.00/4.52  ----------------------
% 11.00/4.52  Preprocessing        : 0.38
% 11.00/4.52  Parsing              : 0.20
% 11.00/4.52  CNF conversion       : 0.03
% 11.00/4.52  Main loop            : 3.34
% 11.00/4.52  Inferencing          : 0.84
% 11.00/4.52  Reduction            : 1.39
% 11.00/4.52  Demodulation         : 1.09
% 11.00/4.52  BG Simplification    : 0.09
% 11.00/4.52  Subsumption          : 0.84
% 11.00/4.52  Abstraction          : 0.12
% 11.00/4.52  MUC search           : 0.00
% 11.00/4.52  Cooper               : 0.00
% 11.00/4.52  Total                : 3.78
% 11.00/4.52  Index Insertion      : 0.00
% 11.00/4.52  Index Deletion       : 0.00
% 11.00/4.52  Index Matching       : 0.00
% 11.00/4.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
