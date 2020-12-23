%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:58 EST 2020

% Result     : Theorem 6.18s
% Output     : CNFRefutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :  159 (1769 expanded)
%              Number of leaves         :   48 ( 603 expanded)
%              Depth                    :   15
%              Number of atoms          :  281 (4549 expanded)
%              Number of equality atoms :   65 ( 613 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_191,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_169,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_125,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_43,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_181,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_190,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_181])).

tff(c_199,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_190])).

tff(c_200,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_212,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_200])).

tff(c_315,plain,(
    ! [B_75,A_76] :
      ( k2_relat_1(B_75) = A_76
      | ~ v2_funct_2(B_75,A_76)
      | ~ v5_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_324,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_212,c_315])).

tff(c_336,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_324])).

tff(c_340,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_76,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_72,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_646,plain,(
    ! [C_107,B_108,A_109] :
      ( v2_funct_2(C_107,B_108)
      | ~ v3_funct_2(C_107,A_109,B_108)
      | ~ v1_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_658,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_646])).

tff(c_666,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_658])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_666])).

tff(c_669,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_687,plain,(
    ! [A_110,B_111,D_112] :
      ( r2_relset_1(A_110,B_111,D_112,D_112)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_695,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_687])).

tff(c_12,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_677,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_12])).

tff(c_683,plain,
    ( ~ v1_xboole_0('#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_677])).

tff(c_686,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_683])).

tff(c_74,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_939,plain,(
    ! [A_135,B_136,C_137] :
      ( k2_relset_1(A_135,B_136,C_137) = k2_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_948,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_939])).

tff(c_954,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_948])).

tff(c_46,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_694,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_46,c_687])).

tff(c_978,plain,(
    ! [C_139,A_140,B_141] :
      ( v2_funct_1(C_139)
      | ~ v3_funct_2(C_139,A_140,B_141)
      | ~ v1_funct_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_987,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_978])).

tff(c_994,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_987])).

tff(c_40,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1075,plain,(
    ! [D_147,C_148,A_149,B_150] :
      ( D_147 = C_148
      | ~ r2_relset_1(A_149,B_150,C_148,D_147)
      | ~ m1_subset_1(D_147,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1085,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_1075])).

tff(c_1104,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1085])).

tff(c_1971,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1104])).

tff(c_2532,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_1971])).

tff(c_2536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_68,c_62,c_2532])).

tff(c_2537,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1104])).

tff(c_4237,plain,(
    ! [C_245,D_246,B_247,A_248] :
      ( k2_funct_1(C_245) = D_246
      | k1_xboole_0 = B_247
      | k1_xboole_0 = A_248
      | ~ v2_funct_1(C_245)
      | ~ r2_relset_1(A_248,A_248,k1_partfun1(A_248,B_247,B_247,A_248,C_245,D_246),k6_partfun1(A_248))
      | k2_relset_1(A_248,B_247,C_245) != B_247
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(B_247,A_248)))
      | ~ v1_funct_2(D_246,B_247,A_248)
      | ~ v1_funct_1(D_246)
      | ~ m1_subset_1(C_245,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247)))
      | ~ v1_funct_2(C_245,A_248,B_247)
      | ~ v1_funct_1(C_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_4249,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_2537,c_4237])).

tff(c_4263,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_66,c_62,c_954,c_694,c_994,c_4249])).

tff(c_4265,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4263])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4304,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4265,c_2])).

tff(c_4306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_686,c_4304])).

tff(c_4307,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4263])).

tff(c_1141,plain,(
    ! [A_157,B_158] :
      ( k2_funct_2(A_157,B_158) = k2_funct_1(B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(k2_zfmisc_1(A_157,A_157)))
      | ~ v3_funct_2(B_158,A_157,A_157)
      | ~ v1_funct_2(B_158,A_157,A_157)
      | ~ v1_funct_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1153,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1141])).

tff(c_1163,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_1153])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1168,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_58])).

tff(c_4332,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4307,c_1168])).

tff(c_4336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_4332])).

tff(c_4337,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_120,plain,(
    ! [B_56,A_57] :
      ( ~ v1_xboole_0(B_56)
      | B_56 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_123,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_2,c_120])).

tff(c_4348,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4337,c_123])).

tff(c_50,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    ! [A_6] : v1_relat_1(k6_partfun1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_16,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    ! [A_10] : k2_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_131,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(k2_relat_1(A_60))
      | ~ v1_relat_1(A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_134,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(A_10)
      | ~ v1_relat_1(k6_partfun1(A_10))
      | v1_xboole_0(k6_partfun1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_131])).

tff(c_137,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0(A_61)
      | v1_xboole_0(k6_partfun1(A_61)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_134])).

tff(c_145,plain,(
    ! [A_62] :
      ( k6_partfun1(A_62) = k1_xboole_0
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_137,c_123])).

tff(c_153,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_145])).

tff(c_169,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_78])).

tff(c_4366,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4348,c_4348,c_169])).

tff(c_4373,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_4366])).

tff(c_4385,plain,(
    ! [A_250,B_251,D_252] :
      ( r2_relset_1(A_250,B_251,D_252,D_252)
      | ~ m1_subset_1(D_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4394,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_4385])).

tff(c_4535,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_4373,c_4394])).

tff(c_4406,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_76])).

tff(c_4405,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_74])).

tff(c_4404,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_72])).

tff(c_18,plain,(
    ! [A_11] : k2_funct_1(k6_relat_1(A_11)) = k6_relat_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_77,plain,(
    ! [A_11] : k2_funct_1(k6_partfun1(A_11)) = k6_partfun1(A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_18])).

tff(c_163,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_77])).

tff(c_179,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_163])).

tff(c_4365,plain,(
    k2_funct_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4348,c_4348,c_179])).

tff(c_4448,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_4373,c_4365])).

tff(c_4403,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_70])).

tff(c_4673,plain,(
    ! [A_269,B_270] :
      ( k2_funct_2(A_269,B_270) = k2_funct_1(B_270)
      | ~ m1_subset_1(B_270,k1_zfmisc_1(k2_zfmisc_1(A_269,A_269)))
      | ~ v3_funct_2(B_270,A_269,A_269)
      | ~ v1_funct_2(B_270,A_269,A_269)
      | ~ v1_funct_1(B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4676,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4403,c_4673])).

tff(c_4682,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4406,c_4405,c_4404,c_4448,c_4676])).

tff(c_187,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_181])).

tff(c_196,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_187])).

tff(c_4338,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_64,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_4523,plain,(
    ! [C_260,B_261,A_262] :
      ( v2_funct_2(C_260,B_261)
      | ~ v3_funct_2(C_260,A_262,B_261)
      | ~ v1_funct_1(C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_262,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4529,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_4523])).

tff(c_4533,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_4529])).

tff(c_211,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_200])).

tff(c_327,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_211,c_315])).

tff(c_339,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_327])).

tff(c_4579,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_339])).

tff(c_4587,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4579,c_12])).

tff(c_4593,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_4338,c_4587])).

tff(c_4371,plain,(
    ! [A_57] :
      ( A_57 = '#skF_2'
      | ~ v1_xboole_0(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4348,c_123])).

tff(c_4512,plain,(
    ! [A_57] :
      ( A_57 = '#skF_1'
      | ~ v1_xboole_0(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_4371])).

tff(c_4604,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4593,c_4512])).

tff(c_4402,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_58])).

tff(c_4802,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4535,c_4682,c_4604,c_4402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:12:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.18/2.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.18/2.27  
% 6.18/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.18/2.28  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.18/2.28  
% 6.18/2.28  %Foreground sorts:
% 6.18/2.28  
% 6.18/2.28  
% 6.18/2.28  %Background operators:
% 6.18/2.28  
% 6.18/2.28  
% 6.18/2.28  %Foreground operators:
% 6.18/2.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.18/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.18/2.28  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.18/2.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.18/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.18/2.28  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.18/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.18/2.28  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.18/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.18/2.28  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.18/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.18/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.18/2.28  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.18/2.28  tff('#skF_3', type, '#skF_3': $i).
% 6.18/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.18/2.28  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.18/2.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.18/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.18/2.28  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.18/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.18/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.18/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.18/2.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.18/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.18/2.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.18/2.28  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.18/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.18/2.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.18/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.18/2.28  
% 6.52/2.30  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.52/2.30  tff(f_191, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 6.52/2.30  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.52/2.30  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.52/2.30  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.52/2.30  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.52/2.30  tff(f_77, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.52/2.30  tff(f_53, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 6.52/2.30  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.52/2.30  tff(f_113, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.52/2.30  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.52/2.30  tff(f_169, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.52/2.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.52/2.30  tff(f_123, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.52/2.30  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.52/2.30  tff(f_125, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.52/2.30  tff(f_43, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 6.52/2.30  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.52/2.30  tff(f_59, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 6.52/2.30  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.52/2.30  tff(c_70, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.52/2.30  tff(c_181, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.52/2.30  tff(c_190, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_181])).
% 6.52/2.30  tff(c_199, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_190])).
% 6.52/2.30  tff(c_200, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.52/2.30  tff(c_212, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_200])).
% 6.52/2.30  tff(c_315, plain, (![B_75, A_76]: (k2_relat_1(B_75)=A_76 | ~v2_funct_2(B_75, A_76) | ~v5_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.52/2.30  tff(c_324, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_212, c_315])).
% 6.52/2.30  tff(c_336, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_324])).
% 6.52/2.30  tff(c_340, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_336])).
% 6.52/2.30  tff(c_76, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.52/2.30  tff(c_72, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.52/2.30  tff(c_646, plain, (![C_107, B_108, A_109]: (v2_funct_2(C_107, B_108) | ~v3_funct_2(C_107, A_109, B_108) | ~v1_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.52/2.30  tff(c_658, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_646])).
% 6.52/2.30  tff(c_666, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_658])).
% 6.52/2.30  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_340, c_666])).
% 6.52/2.30  tff(c_669, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_336])).
% 6.52/2.30  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.52/2.30  tff(c_687, plain, (![A_110, B_111, D_112]: (r2_relset_1(A_110, B_111, D_112, D_112) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.52/2.30  tff(c_695, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_687])).
% 6.52/2.30  tff(c_12, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.52/2.30  tff(c_677, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_669, c_12])).
% 6.52/2.30  tff(c_683, plain, (~v1_xboole_0('#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_677])).
% 6.52/2.30  tff(c_686, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_683])).
% 6.52/2.30  tff(c_74, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.52/2.30  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.52/2.30  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.52/2.30  tff(c_939, plain, (![A_135, B_136, C_137]: (k2_relset_1(A_135, B_136, C_137)=k2_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.52/2.30  tff(c_948, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_939])).
% 6.52/2.30  tff(c_954, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_669, c_948])).
% 6.52/2.30  tff(c_46, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.52/2.30  tff(c_694, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_46, c_687])).
% 6.52/2.30  tff(c_978, plain, (![C_139, A_140, B_141]: (v2_funct_1(C_139) | ~v3_funct_2(C_139, A_140, B_141) | ~v1_funct_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.52/2.30  tff(c_987, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_978])).
% 6.52/2.30  tff(c_994, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_987])).
% 6.52/2.30  tff(c_40, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.52/2.30  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.52/2.30  tff(c_1075, plain, (![D_147, C_148, A_149, B_150]: (D_147=C_148 | ~r2_relset_1(A_149, B_150, C_148, D_147) | ~m1_subset_1(D_147, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.52/2.30  tff(c_1085, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_1075])).
% 6.52/2.30  tff(c_1104, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1085])).
% 6.52/2.30  tff(c_1971, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1104])).
% 6.52/2.30  tff(c_2532, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_40, c_1971])).
% 6.52/2.30  tff(c_2536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_68, c_62, c_2532])).
% 6.52/2.30  tff(c_2537, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1104])).
% 6.52/2.30  tff(c_4237, plain, (![C_245, D_246, B_247, A_248]: (k2_funct_1(C_245)=D_246 | k1_xboole_0=B_247 | k1_xboole_0=A_248 | ~v2_funct_1(C_245) | ~r2_relset_1(A_248, A_248, k1_partfun1(A_248, B_247, B_247, A_248, C_245, D_246), k6_partfun1(A_248)) | k2_relset_1(A_248, B_247, C_245)!=B_247 | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(B_247, A_248))) | ~v1_funct_2(D_246, B_247, A_248) | ~v1_funct_1(D_246) | ~m1_subset_1(C_245, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))) | ~v1_funct_2(C_245, A_248, B_247) | ~v1_funct_1(C_245))), inference(cnfTransformation, [status(thm)], [f_169])).
% 6.52/2.30  tff(c_4249, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2537, c_4237])).
% 6.52/2.30  tff(c_4263, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_66, c_62, c_954, c_694, c_994, c_4249])).
% 6.52/2.30  tff(c_4265, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_4263])).
% 6.52/2.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.52/2.30  tff(c_4304, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4265, c_2])).
% 6.52/2.30  tff(c_4306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_686, c_4304])).
% 6.52/2.30  tff(c_4307, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_4263])).
% 6.52/2.30  tff(c_1141, plain, (![A_157, B_158]: (k2_funct_2(A_157, B_158)=k2_funct_1(B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(k2_zfmisc_1(A_157, A_157))) | ~v3_funct_2(B_158, A_157, A_157) | ~v1_funct_2(B_158, A_157, A_157) | ~v1_funct_1(B_158))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.52/2.30  tff(c_1153, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1141])).
% 6.52/2.30  tff(c_1163, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_1153])).
% 6.52/2.30  tff(c_58, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.52/2.30  tff(c_1168, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1163, c_58])).
% 6.52/2.30  tff(c_4332, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4307, c_1168])).
% 6.52/2.30  tff(c_4336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_695, c_4332])).
% 6.52/2.30  tff(c_4337, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_683])).
% 6.52/2.30  tff(c_120, plain, (![B_56, A_57]: (~v1_xboole_0(B_56) | B_56=A_57 | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.52/2.30  tff(c_123, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_2, c_120])).
% 6.52/2.30  tff(c_4348, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_4337, c_123])).
% 6.52/2.30  tff(c_50, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.52/2.30  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.52/2.30  tff(c_80, plain, (![A_6]: (v1_relat_1(k6_partfun1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8])).
% 6.52/2.30  tff(c_16, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.52/2.30  tff(c_78, plain, (![A_10]: (k2_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 6.52/2.30  tff(c_131, plain, (![A_60]: (~v1_xboole_0(k2_relat_1(A_60)) | ~v1_relat_1(A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.52/2.30  tff(c_134, plain, (![A_10]: (~v1_xboole_0(A_10) | ~v1_relat_1(k6_partfun1(A_10)) | v1_xboole_0(k6_partfun1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_131])).
% 6.52/2.30  tff(c_137, plain, (![A_61]: (~v1_xboole_0(A_61) | v1_xboole_0(k6_partfun1(A_61)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_134])).
% 6.52/2.30  tff(c_145, plain, (![A_62]: (k6_partfun1(A_62)=k1_xboole_0 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_137, c_123])).
% 6.52/2.30  tff(c_153, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_145])).
% 6.52/2.30  tff(c_169, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_153, c_78])).
% 6.52/2.30  tff(c_4366, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4348, c_4348, c_169])).
% 6.52/2.30  tff(c_4373, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_669, c_4366])).
% 6.52/2.30  tff(c_4385, plain, (![A_250, B_251, D_252]: (r2_relset_1(A_250, B_251, D_252, D_252) | ~m1_subset_1(D_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.52/2.30  tff(c_4394, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_4385])).
% 6.52/2.30  tff(c_4535, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_4373, c_4394])).
% 6.52/2.30  tff(c_4406, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_76])).
% 6.52/2.30  tff(c_4405, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_74])).
% 6.52/2.30  tff(c_4404, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_72])).
% 6.52/2.30  tff(c_18, plain, (![A_11]: (k2_funct_1(k6_relat_1(A_11))=k6_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.52/2.30  tff(c_77, plain, (![A_11]: (k2_funct_1(k6_partfun1(A_11))=k6_partfun1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_18])).
% 6.52/2.30  tff(c_163, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_153, c_77])).
% 6.52/2.30  tff(c_179, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_153, c_163])).
% 6.52/2.30  tff(c_4365, plain, (k2_funct_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4348, c_4348, c_179])).
% 6.52/2.30  tff(c_4448, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_4373, c_4365])).
% 6.52/2.30  tff(c_4403, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_70])).
% 6.52/2.30  tff(c_4673, plain, (![A_269, B_270]: (k2_funct_2(A_269, B_270)=k2_funct_1(B_270) | ~m1_subset_1(B_270, k1_zfmisc_1(k2_zfmisc_1(A_269, A_269))) | ~v3_funct_2(B_270, A_269, A_269) | ~v1_funct_2(B_270, A_269, A_269) | ~v1_funct_1(B_270))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.52/2.30  tff(c_4676, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_4403, c_4673])).
% 6.52/2.30  tff(c_4682, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4406, c_4405, c_4404, c_4448, c_4676])).
% 6.52/2.30  tff(c_187, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_181])).
% 6.52/2.30  tff(c_196, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_187])).
% 6.52/2.30  tff(c_4338, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_683])).
% 6.52/2.30  tff(c_64, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.52/2.30  tff(c_4523, plain, (![C_260, B_261, A_262]: (v2_funct_2(C_260, B_261) | ~v3_funct_2(C_260, A_262, B_261) | ~v1_funct_1(C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_262, B_261))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.52/2.30  tff(c_4529, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_4523])).
% 6.52/2.30  tff(c_4533, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_4529])).
% 6.52/2.30  tff(c_211, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_200])).
% 6.52/2.30  tff(c_327, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_211, c_315])).
% 6.52/2.30  tff(c_339, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_327])).
% 6.52/2.30  tff(c_4579, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_339])).
% 6.52/2.30  tff(c_4587, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4579, c_12])).
% 6.52/2.30  tff(c_4593, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_4338, c_4587])).
% 6.52/2.30  tff(c_4371, plain, (![A_57]: (A_57='#skF_2' | ~v1_xboole_0(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_4348, c_123])).
% 6.52/2.30  tff(c_4512, plain, (![A_57]: (A_57='#skF_1' | ~v1_xboole_0(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_4371])).
% 6.52/2.30  tff(c_4604, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_4593, c_4512])).
% 6.52/2.30  tff(c_4402, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_58])).
% 6.52/2.30  tff(c_4802, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4535, c_4682, c_4604, c_4402])).
% 6.52/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.30  
% 6.52/2.30  Inference rules
% 6.52/2.30  ----------------------
% 6.52/2.30  #Ref     : 0
% 6.52/2.30  #Sup     : 1242
% 6.52/2.30  #Fact    : 0
% 6.52/2.30  #Define  : 0
% 6.52/2.30  #Split   : 10
% 6.52/2.30  #Chain   : 0
% 6.52/2.30  #Close   : 0
% 6.52/2.30  
% 6.52/2.30  Ordering : KBO
% 6.52/2.30  
% 6.52/2.30  Simplification rules
% 6.52/2.30  ----------------------
% 6.52/2.30  #Subsume      : 325
% 6.52/2.30  #Demod        : 901
% 6.52/2.30  #Tautology    : 376
% 6.52/2.30  #SimpNegUnit  : 4
% 6.52/2.30  #BackRed      : 82
% 6.52/2.30  
% 6.52/2.30  #Partial instantiations: 0
% 6.52/2.30  #Strategies tried      : 1
% 6.52/2.30  
% 6.52/2.30  Timing (in seconds)
% 6.52/2.30  ----------------------
% 6.52/2.30  Preprocessing        : 0.40
% 6.52/2.30  Parsing              : 0.22
% 6.52/2.30  CNF conversion       : 0.03
% 6.52/2.30  Main loop            : 1.03
% 6.52/2.30  Inferencing          : 0.30
% 6.52/2.30  Reduction            : 0.36
% 6.52/2.30  Demodulation         : 0.27
% 6.52/2.30  BG Simplification    : 0.04
% 6.52/2.30  Subsumption          : 0.25
% 6.52/2.30  Abstraction          : 0.04
% 6.52/2.30  MUC search           : 0.00
% 6.52/2.30  Cooper               : 0.00
% 6.52/2.30  Total                : 1.48
% 6.52/2.30  Index Insertion      : 0.00
% 6.52/2.30  Index Deletion       : 0.00
% 6.52/2.30  Index Matching       : 0.00
% 6.52/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
