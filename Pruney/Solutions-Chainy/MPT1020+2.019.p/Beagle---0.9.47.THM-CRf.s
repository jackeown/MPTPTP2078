%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:52 EST 2020

% Result     : Theorem 5.84s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 645 expanded)
%              Number of leaves         :   42 ( 230 expanded)
%              Depth                    :   15
%              Number of atoms          :  250 (1987 expanded)
%              Number of equality atoms :   47 ( 210 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_187,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_165,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_216,plain,(
    ! [A_68,B_69,D_70] :
      ( r2_relset_1(A_68,B_69,D_70,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_225,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_216])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_122,plain,(
    ! [C_60,B_61,A_62] :
      ( v1_xboole_0(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(B_61,A_62)))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_122])).

tff(c_136,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_72,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_70,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_81,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_81])).

tff(c_109,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_120,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_109])).

tff(c_270,plain,(
    ! [B_73,A_74] :
      ( k2_relat_1(B_73) = A_74
      | ~ v2_funct_2(B_73,A_74)
      | ~ v5_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_285,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_270])).

tff(c_300,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_285])).

tff(c_537,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_68,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_600,plain,(
    ! [C_105,B_106,A_107] :
      ( v2_funct_2(C_105,B_106)
      | ~ v3_funct_2(C_105,A_107,B_106)
      | ~ v1_funct_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_609,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_600])).

tff(c_619,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_609])).

tff(c_621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_537,c_619])).

tff(c_622,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_634,plain,(
    ! [A_108,B_109,C_110] :
      ( k2_relset_1(A_108,B_109,C_110) = k2_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_643,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_634])).

tff(c_650,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_643])).

tff(c_44,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_223,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_44,c_216])).

tff(c_676,plain,(
    ! [C_112,A_113,B_114] :
      ( v2_funct_1(C_112)
      | ~ v3_funct_2(C_112,A_113,B_114)
      | ~ v1_funct_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_685,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_676])).

tff(c_693,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_685])).

tff(c_1744,plain,(
    ! [C_169,F_172,E_171,D_174,A_173,B_170] :
      ( m1_subset_1(k1_partfun1(A_173,B_170,C_169,D_174,E_171,F_172),k1_zfmisc_1(k2_zfmisc_1(A_173,D_174)))
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(C_169,D_174)))
      | ~ v1_funct_1(F_172)
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_173,B_170)))
      | ~ v1_funct_1(E_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_760,plain,(
    ! [D_121,C_122,A_123,B_124] :
      ( D_121 = C_122
      | ~ r2_relset_1(A_123,B_124,C_122,D_121)
      | ~ m1_subset_1(D_121,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_770,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_760])).

tff(c_789,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_770])).

tff(c_861,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_789])).

tff(c_1765,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1744,c_861])).

tff(c_1802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_64,c_58,c_1765])).

tff(c_1803,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_789])).

tff(c_2843,plain,(
    ! [C_228,D_229,B_230,A_231] :
      ( k2_funct_1(C_228) = D_229
      | k1_xboole_0 = B_230
      | k1_xboole_0 = A_231
      | ~ v2_funct_1(C_228)
      | ~ r2_relset_1(A_231,A_231,k1_partfun1(A_231,B_230,B_230,A_231,C_228,D_229),k6_partfun1(A_231))
      | k2_relset_1(A_231,B_230,C_228) != B_230
      | ~ m1_subset_1(D_229,k1_zfmisc_1(k2_zfmisc_1(B_230,A_231)))
      | ~ v1_funct_2(D_229,B_230,A_231)
      | ~ v1_funct_1(D_229)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230)))
      | ~ v1_funct_2(C_228,A_231,B_230)
      | ~ v1_funct_1(C_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_2846,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1803,c_2843])).

tff(c_2854,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_58,c_650,c_223,c_693,c_2846])).

tff(c_2856,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2854])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2889,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_2])).

tff(c_2891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_2889])).

tff(c_2892,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2854])).

tff(c_2013,plain,(
    ! [A_185,B_186] :
      ( k2_funct_2(A_185,B_186) = k2_funct_1(B_186)
      | ~ m1_subset_1(B_186,k1_zfmisc_1(k2_zfmisc_1(A_185,A_185)))
      | ~ v3_funct_2(B_186,A_185,A_185)
      | ~ v1_funct_2(B_186,A_185,A_185)
      | ~ v1_funct_1(B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2025,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2013])).

tff(c_2034,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_2025])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_2039,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2034,c_54])).

tff(c_2954,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2892,c_2039])).

tff(c_2977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_2954])).

tff(c_2979,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2987,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2979,c_4])).

tff(c_2978,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_2983,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2978,c_4])).

tff(c_2995,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2987,c_2983])).

tff(c_3007,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2995,c_66])).

tff(c_3513,plain,(
    ! [A_267,B_268,D_269] :
      ( r2_relset_1(A_267,B_268,D_269,D_269)
      | ~ m1_subset_1(D_269,k1_zfmisc_1(k2_zfmisc_1(A_267,B_268))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3518,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_3007,c_3513])).

tff(c_3010,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2995,c_72])).

tff(c_3009,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2995,c_70])).

tff(c_3008,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2995,c_68])).

tff(c_4284,plain,(
    ! [A_313,B_314] :
      ( k2_funct_2(A_313,B_314) = k2_funct_1(B_314)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(k2_zfmisc_1(A_313,A_313)))
      | ~ v3_funct_2(B_314,A_313,A_313)
      | ~ v1_funct_2(B_314,A_313,A_313)
      | ~ v1_funct_1(B_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4290,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3007,c_4284])).

tff(c_4299,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3010,c_3009,c_3008,c_4290])).

tff(c_4493,plain,(
    ! [A_325,B_326] :
      ( m1_subset_1(k2_funct_2(A_325,B_326),k1_zfmisc_1(k2_zfmisc_1(A_325,A_325)))
      | ~ m1_subset_1(B_326,k1_zfmisc_1(k2_zfmisc_1(A_325,A_325)))
      | ~ v3_funct_2(B_326,A_325,A_325)
      | ~ v1_funct_2(B_326,A_325,A_325)
      | ~ v1_funct_1(B_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4529,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4299,c_4493])).

tff(c_4543,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3010,c_3009,c_3008,c_3007,c_4529])).

tff(c_12,plain,(
    ! [C_11,B_9,A_8] :
      ( v1_xboole_0(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(B_9,A_8)))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4567,plain,
    ( v1_xboole_0(k2_funct_1('#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4543,c_12])).

tff(c_4599,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2979,c_4567])).

tff(c_2988,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2983,c_4])).

tff(c_3018,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2995,c_2988])).

tff(c_4610,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4599,c_3018])).

tff(c_134,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_122])).

tff(c_3017,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2979,c_134])).

tff(c_3019,plain,(
    ! [A_235] :
      ( A_235 = '#skF_1'
      | ~ v1_xboole_0(A_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2995,c_2988])).

tff(c_3026,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3017,c_3019])).

tff(c_3006,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2995,c_54])).

tff(c_3546,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3026,c_3006])).

tff(c_4302,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4299,c_3546])).

tff(c_4617,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4610,c_4302])).

tff(c_4628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3518,c_4617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:05:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.84/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.84/2.13  
% 5.84/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.08/2.13  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.08/2.13  
% 6.08/2.13  %Foreground sorts:
% 6.08/2.13  
% 6.08/2.13  
% 6.08/2.13  %Background operators:
% 6.08/2.13  
% 6.08/2.13  
% 6.08/2.13  %Foreground operators:
% 6.08/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.08/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.08/2.13  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.08/2.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.08/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.08/2.13  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.08/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.08/2.13  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.08/2.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.08/2.13  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.08/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.08/2.13  tff('#skF_2', type, '#skF_2': $i).
% 6.08/2.13  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.08/2.13  tff('#skF_3', type, '#skF_3': $i).
% 6.08/2.13  tff('#skF_1', type, '#skF_1': $i).
% 6.08/2.13  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.08/2.13  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.08/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.08/2.13  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.08/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.08/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.08/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.08/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.08/2.13  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.08/2.13  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.08/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.08/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.08/2.13  
% 6.08/2.15  tff(f_187, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 6.08/2.15  tff(f_59, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.08/2.15  tff(f_47, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 6.08/2.15  tff(f_34, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.08/2.15  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.08/2.15  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.08/2.15  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.08/2.15  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.08/2.15  tff(f_111, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.08/2.15  tff(f_91, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.08/2.15  tff(f_165, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.08/2.15  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.08/2.15  tff(f_121, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.08/2.15  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.08/2.15  tff(f_107, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.08/2.15  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.08/2.15  tff(c_216, plain, (![A_68, B_69, D_70]: (r2_relset_1(A_68, B_69, D_70, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.08/2.15  tff(c_225, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_216])).
% 6.08/2.15  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.08/2.15  tff(c_122, plain, (![C_60, B_61, A_62]: (v1_xboole_0(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(B_61, A_62))) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.08/2.15  tff(c_133, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_122])).
% 6.08/2.15  tff(c_136, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_133])).
% 6.08/2.15  tff(c_72, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.08/2.15  tff(c_70, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.08/2.15  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.08/2.15  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.08/2.15  tff(c_81, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.08/2.15  tff(c_92, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_81])).
% 6.08/2.15  tff(c_109, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.08/2.15  tff(c_120, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_109])).
% 6.08/2.15  tff(c_270, plain, (![B_73, A_74]: (k2_relat_1(B_73)=A_74 | ~v2_funct_2(B_73, A_74) | ~v5_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.08/2.15  tff(c_285, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_120, c_270])).
% 6.08/2.15  tff(c_300, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_285])).
% 6.08/2.15  tff(c_537, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_300])).
% 6.08/2.15  tff(c_68, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.08/2.15  tff(c_600, plain, (![C_105, B_106, A_107]: (v2_funct_2(C_105, B_106) | ~v3_funct_2(C_105, A_107, B_106) | ~v1_funct_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.08/2.15  tff(c_609, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_600])).
% 6.08/2.15  tff(c_619, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_609])).
% 6.08/2.15  tff(c_621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_537, c_619])).
% 6.08/2.15  tff(c_622, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_300])).
% 6.08/2.15  tff(c_634, plain, (![A_108, B_109, C_110]: (k2_relset_1(A_108, B_109, C_110)=k2_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.08/2.15  tff(c_643, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_634])).
% 6.08/2.15  tff(c_650, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_622, c_643])).
% 6.08/2.15  tff(c_44, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.08/2.15  tff(c_223, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_44, c_216])).
% 6.08/2.15  tff(c_676, plain, (![C_112, A_113, B_114]: (v2_funct_1(C_112) | ~v3_funct_2(C_112, A_113, B_114) | ~v1_funct_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.08/2.15  tff(c_685, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_676])).
% 6.08/2.15  tff(c_693, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_685])).
% 6.08/2.15  tff(c_1744, plain, (![C_169, F_172, E_171, D_174, A_173, B_170]: (m1_subset_1(k1_partfun1(A_173, B_170, C_169, D_174, E_171, F_172), k1_zfmisc_1(k2_zfmisc_1(A_173, D_174))) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(C_169, D_174))) | ~v1_funct_1(F_172) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_173, B_170))) | ~v1_funct_1(E_171))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.08/2.15  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.08/2.15  tff(c_760, plain, (![D_121, C_122, A_123, B_124]: (D_121=C_122 | ~r2_relset_1(A_123, B_124, C_122, D_121) | ~m1_subset_1(D_121, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.08/2.15  tff(c_770, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_760])).
% 6.08/2.15  tff(c_789, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_770])).
% 6.08/2.15  tff(c_861, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_789])).
% 6.08/2.15  tff(c_1765, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_1744, c_861])).
% 6.08/2.15  tff(c_1802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_64, c_58, c_1765])).
% 6.08/2.15  tff(c_1803, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_789])).
% 6.08/2.15  tff(c_2843, plain, (![C_228, D_229, B_230, A_231]: (k2_funct_1(C_228)=D_229 | k1_xboole_0=B_230 | k1_xboole_0=A_231 | ~v2_funct_1(C_228) | ~r2_relset_1(A_231, A_231, k1_partfun1(A_231, B_230, B_230, A_231, C_228, D_229), k6_partfun1(A_231)) | k2_relset_1(A_231, B_230, C_228)!=B_230 | ~m1_subset_1(D_229, k1_zfmisc_1(k2_zfmisc_1(B_230, A_231))) | ~v1_funct_2(D_229, B_230, A_231) | ~v1_funct_1(D_229) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))) | ~v1_funct_2(C_228, A_231, B_230) | ~v1_funct_1(C_228))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.08/2.15  tff(c_2846, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1803, c_2843])).
% 6.08/2.15  tff(c_2854, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_58, c_650, c_223, c_693, c_2846])).
% 6.08/2.15  tff(c_2856, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2854])).
% 6.08/2.15  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.08/2.15  tff(c_2889, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2856, c_2])).
% 6.08/2.15  tff(c_2891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_2889])).
% 6.08/2.15  tff(c_2892, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_2854])).
% 6.08/2.15  tff(c_2013, plain, (![A_185, B_186]: (k2_funct_2(A_185, B_186)=k2_funct_1(B_186) | ~m1_subset_1(B_186, k1_zfmisc_1(k2_zfmisc_1(A_185, A_185))) | ~v3_funct_2(B_186, A_185, A_185) | ~v1_funct_2(B_186, A_185, A_185) | ~v1_funct_1(B_186))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.08/2.15  tff(c_2025, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_2013])).
% 6.08/2.15  tff(c_2034, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_2025])).
% 6.08/2.15  tff(c_54, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.08/2.15  tff(c_2039, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2034, c_54])).
% 6.08/2.15  tff(c_2954, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2892, c_2039])).
% 6.08/2.15  tff(c_2977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_225, c_2954])).
% 6.08/2.15  tff(c_2979, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_133])).
% 6.08/2.15  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.08/2.15  tff(c_2987, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_2979, c_4])).
% 6.08/2.15  tff(c_2978, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_133])).
% 6.08/2.15  tff(c_2983, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2978, c_4])).
% 6.08/2.15  tff(c_2995, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2987, c_2983])).
% 6.08/2.15  tff(c_3007, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2995, c_66])).
% 6.08/2.15  tff(c_3513, plain, (![A_267, B_268, D_269]: (r2_relset_1(A_267, B_268, D_269, D_269) | ~m1_subset_1(D_269, k1_zfmisc_1(k2_zfmisc_1(A_267, B_268))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.08/2.15  tff(c_3518, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_3007, c_3513])).
% 6.08/2.15  tff(c_3010, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2995, c_72])).
% 6.08/2.15  tff(c_3009, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2995, c_70])).
% 6.08/2.15  tff(c_3008, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2995, c_68])).
% 6.08/2.15  tff(c_4284, plain, (![A_313, B_314]: (k2_funct_2(A_313, B_314)=k2_funct_1(B_314) | ~m1_subset_1(B_314, k1_zfmisc_1(k2_zfmisc_1(A_313, A_313))) | ~v3_funct_2(B_314, A_313, A_313) | ~v1_funct_2(B_314, A_313, A_313) | ~v1_funct_1(B_314))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.08/2.15  tff(c_4290, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_3007, c_4284])).
% 6.08/2.15  tff(c_4299, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3010, c_3009, c_3008, c_4290])).
% 6.08/2.15  tff(c_4493, plain, (![A_325, B_326]: (m1_subset_1(k2_funct_2(A_325, B_326), k1_zfmisc_1(k2_zfmisc_1(A_325, A_325))) | ~m1_subset_1(B_326, k1_zfmisc_1(k2_zfmisc_1(A_325, A_325))) | ~v3_funct_2(B_326, A_325, A_325) | ~v1_funct_2(B_326, A_325, A_325) | ~v1_funct_1(B_326))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.08/2.15  tff(c_4529, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4299, c_4493])).
% 6.08/2.15  tff(c_4543, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3010, c_3009, c_3008, c_3007, c_4529])).
% 6.08/2.15  tff(c_12, plain, (![C_11, B_9, A_8]: (v1_xboole_0(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(B_9, A_8))) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.08/2.15  tff(c_4567, plain, (v1_xboole_0(k2_funct_1('#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_4543, c_12])).
% 6.08/2.15  tff(c_4599, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2979, c_4567])).
% 6.08/2.15  tff(c_2988, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2983, c_4])).
% 6.08/2.15  tff(c_3018, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2995, c_2988])).
% 6.08/2.15  tff(c_4610, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4599, c_3018])).
% 6.08/2.15  tff(c_134, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_122])).
% 6.08/2.15  tff(c_3017, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2979, c_134])).
% 6.08/2.15  tff(c_3019, plain, (![A_235]: (A_235='#skF_1' | ~v1_xboole_0(A_235))), inference(demodulation, [status(thm), theory('equality')], [c_2995, c_2988])).
% 6.08/2.15  tff(c_3026, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_3017, c_3019])).
% 6.08/2.15  tff(c_3006, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2995, c_54])).
% 6.08/2.15  tff(c_3546, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3026, c_3006])).
% 6.08/2.15  tff(c_4302, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4299, c_3546])).
% 6.08/2.15  tff(c_4617, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4610, c_4302])).
% 6.08/2.15  tff(c_4628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3518, c_4617])).
% 6.08/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.08/2.15  
% 6.08/2.15  Inference rules
% 6.08/2.15  ----------------------
% 6.08/2.15  #Ref     : 0
% 6.08/2.15  #Sup     : 1024
% 6.08/2.15  #Fact    : 0
% 6.08/2.15  #Define  : 0
% 6.08/2.15  #Split   : 15
% 6.08/2.15  #Chain   : 0
% 6.08/2.15  #Close   : 0
% 6.08/2.15  
% 6.08/2.15  Ordering : KBO
% 6.08/2.15  
% 6.08/2.15  Simplification rules
% 6.08/2.15  ----------------------
% 6.08/2.15  #Subsume      : 166
% 6.08/2.15  #Demod        : 1358
% 6.08/2.15  #Tautology    : 432
% 6.08/2.15  #SimpNegUnit  : 13
% 6.08/2.15  #BackRed      : 97
% 6.08/2.15  
% 6.08/2.15  #Partial instantiations: 0
% 6.08/2.15  #Strategies tried      : 1
% 6.08/2.15  
% 6.08/2.15  Timing (in seconds)
% 6.08/2.15  ----------------------
% 6.08/2.16  Preprocessing        : 0.36
% 6.08/2.16  Parsing              : 0.19
% 6.08/2.16  CNF conversion       : 0.02
% 6.08/2.16  Main loop            : 1.02
% 6.08/2.16  Inferencing          : 0.34
% 6.08/2.16  Reduction            : 0.38
% 6.08/2.16  Demodulation         : 0.28
% 6.08/2.16  BG Simplification    : 0.04
% 6.08/2.16  Subsumption          : 0.18
% 6.08/2.16  Abstraction          : 0.04
% 6.08/2.16  MUC search           : 0.00
% 6.08/2.16  Cooper               : 0.00
% 6.08/2.16  Total                : 1.43
% 6.08/2.16  Index Insertion      : 0.00
% 6.08/2.16  Index Deletion       : 0.00
% 6.08/2.16  Index Matching       : 0.00
% 6.08/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
