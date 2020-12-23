%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:50 EST 2020

% Result     : Theorem 10.53s
% Output     : CNFRefutation 10.70s
% Verified   : 
% Statistics : Number of formulae       :  269 (4829 expanded)
%              Number of leaves         :   55 (1730 expanded)
%              Depth                    :   23
%              Number of atoms          :  634 (16477 expanded)
%              Number of equality atoms :  173 (1621 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k11_relat_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_268,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_246,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_213,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_149,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_176,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
         => ( ! [D] :
                ( r2_hidden(D,A)
               => k11_relat_1(B,D) = k11_relat_1(C,D) )
           => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

tff(f_37,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_238,axiom,(
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

tff(f_159,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_197,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
              & v2_funct_1(E) )
           => ( C = k1_xboole_0
              | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_90,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_88,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_210,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_229,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_210])).

tff(c_11355,plain,(
    ! [A_625,B_626] :
      ( k1_relset_1(A_625,A_625,B_626) = A_625
      | ~ m1_subset_1(B_626,k1_zfmisc_1(k2_zfmisc_1(A_625,A_625)))
      | ~ v1_funct_2(B_626,A_625,A_625)
      | ~ v1_funct_1(B_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_11373,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_11355])).

tff(c_11392,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_229,c_11373])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_192,plain,(
    ! [A_111,B_112,D_113] :
      ( r2_relset_1(A_111,B_112,D_113,D_113)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_208,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_192])).

tff(c_546,plain,(
    ! [A_153,B_154] :
      ( k1_relset_1(A_153,A_153,B_154) = A_153
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k2_zfmisc_1(A_153,A_153)))
      | ~ v1_funct_2(B_154,A_153,A_153)
      | ~ v1_funct_1(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_564,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_546])).

tff(c_583,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_229,c_564])).

tff(c_307,plain,(
    ! [A_131,B_132,C_133] :
      ( m1_subset_1(k1_relset_1(A_131,B_132,C_133),k1_zfmisc_1(A_131))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_338,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_307])).

tff(c_354,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_338])).

tff(c_591,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_354])).

tff(c_82,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_80,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_260,plain,(
    ! [A_125,B_126,C_127] :
      ( k2_relset_1(A_125,B_126,C_127) = k2_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_281,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_260])).

tff(c_78,plain,(
    v3_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_455,plain,(
    ! [C_137,A_138,B_139] :
      ( v2_funct_1(C_137)
      | ~ v3_funct_2(C_137,A_138,B_139)
      | ~ v1_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_480,plain,
    ( v2_funct_1('#skF_5')
    | ~ v3_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_455])).

tff(c_495,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_480])).

tff(c_6829,plain,(
    ! [B_414,C_415,A_416] :
      ( k6_partfun1(B_414) = k5_relat_1(k2_funct_1(C_415),C_415)
      | k1_xboole_0 = B_414
      | ~ v2_funct_1(C_415)
      | k2_relset_1(A_416,B_414,C_415) != B_414
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_zfmisc_1(A_416,B_414)))
      | ~ v1_funct_2(C_415,A_416,B_414)
      | ~ v1_funct_1(C_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_6857,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_3','#skF_5') != '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_6829])).

tff(c_6881,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_281,c_495,c_6857])).

tff(c_7625,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6881])).

tff(c_56,plain,(
    ! [A_52] : m1_subset_1(k6_partfun1(A_52),k1_zfmisc_1(k2_zfmisc_1(A_52,A_52))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_205,plain,(
    ! [A_52] : r2_relset_1(A_52,A_52,k6_partfun1(A_52),k6_partfun1(A_52)) ),
    inference(resolution,[status(thm)],[c_56,c_192])).

tff(c_3890,plain,(
    ! [D_296,C_297,A_299,F_295,B_298,E_294] :
      ( m1_subset_1(k1_partfun1(A_299,B_298,C_297,D_296,E_294,F_295),k1_zfmisc_1(k2_zfmisc_1(A_299,D_296)))
      | ~ m1_subset_1(F_295,k1_zfmisc_1(k2_zfmisc_1(C_297,D_296)))
      | ~ v1_funct_1(F_295)
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(A_299,B_298)))
      | ~ v1_funct_1(E_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_74,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_625,plain,(
    ! [D_155,C_156,A_157,B_158] :
      ( D_155 = C_156
      | ~ r2_relset_1(A_157,B_158,C_156,D_155)
      | ~ m1_subset_1(D_155,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_639,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_74,c_625])).

tff(c_666,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_639])).

tff(c_677,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_666])).

tff(c_3920,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3890,c_677])).

tff(c_3965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_84,c_82,c_76,c_3920])).

tff(c_3966,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_666])).

tff(c_8087,plain,(
    ! [A_464,B_465,C_466,D_467] :
      ( k2_relset_1(A_464,B_465,C_466) = B_465
      | ~ r2_relset_1(B_465,B_465,k1_partfun1(B_465,A_464,A_464,B_465,D_467,C_466),k6_partfun1(B_465))
      | ~ m1_subset_1(D_467,k1_zfmisc_1(k2_zfmisc_1(B_465,A_464)))
      | ~ v1_funct_2(D_467,B_465,A_464)
      | ~ v1_funct_1(D_467)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_464,B_465)))
      | ~ v1_funct_2(C_466,A_464,B_465)
      | ~ v1_funct_1(C_466) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_8090,plain,
    ( k2_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3966,c_8087])).

tff(c_8092,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_90,c_88,c_84,c_205,c_281,c_8090])).

tff(c_8094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7625,c_8092])).

tff(c_8096,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6881])).

tff(c_8097,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8096,c_281])).

tff(c_8238,plain,(
    ! [A_468,C_469,B_470] :
      ( k6_partfun1(A_468) = k5_relat_1(C_469,k2_funct_1(C_469))
      | k1_xboole_0 = B_470
      | ~ v2_funct_1(C_469)
      | k2_relset_1(A_468,B_470,C_469) != B_470
      | ~ m1_subset_1(C_469,k1_zfmisc_1(k2_zfmisc_1(A_468,B_470)))
      | ~ v1_funct_2(C_469,A_468,B_470)
      | ~ v1_funct_1(C_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_8268,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_3','#skF_5') != '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_8238])).

tff(c_8295,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_8097,c_495,c_8268])).

tff(c_8298,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8295])).

tff(c_206,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_192])).

tff(c_231,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_210])).

tff(c_335,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_307])).

tff(c_352,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_335])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_366,plain,
    ( v1_xboole_0(k1_relat_1('#skF_5'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_352,c_10])).

tff(c_407,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_279,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_260])).

tff(c_86,plain,(
    v3_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_473,plain,
    ( v2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_455])).

tff(c_491,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_473])).

tff(c_4779,plain,(
    ! [B_346,C_347,A_348] :
      ( k6_partfun1(B_346) = k5_relat_1(k2_funct_1(C_347),C_347)
      | k1_xboole_0 = B_346
      | ~ v2_funct_1(C_347)
      | k2_relset_1(A_348,B_346,C_347) != B_346
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_348,B_346)))
      | ~ v1_funct_2(C_347,A_348,B_346)
      | ~ v1_funct_1(C_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_4802,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_3','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_4779])).

tff(c_4824,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_279,c_491,c_4802])).

tff(c_4847,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4824])).

tff(c_4373,plain,(
    ! [A_325,B_326,C_327] :
      ( r2_hidden('#skF_2'(A_325,B_326,C_327),A_325)
      | r2_relset_1(A_325,A_325,B_326,C_327)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,A_325)))
      | ~ m1_subset_1(B_326,k1_zfmisc_1(k2_zfmisc_1(A_325,A_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4479,plain,(
    ! [B_342] :
      ( r2_hidden('#skF_2'('#skF_3',B_342,'#skF_5'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_342,'#skF_5')
      | ~ m1_subset_1(B_342,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_76,c_4373])).

tff(c_4524,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_4479])).

tff(c_4529,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4524])).

tff(c_30,plain,(
    ! [D_33,C_32,A_30,B_31] :
      ( D_33 = C_32
      | ~ r2_relset_1(A_30,B_31,C_32,D_33)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4531,plain,
    ( '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_4529,c_30])).

tff(c_4534,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_76,c_4531])).

tff(c_4542,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4','#skF_4') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_3966])).

tff(c_5443,plain,(
    ! [A_366,B_367,C_368,D_369] :
      ( k2_relset_1(A_366,B_367,C_368) = B_367
      | ~ r2_relset_1(B_367,B_367,k1_partfun1(B_367,A_366,A_366,B_367,D_369,C_368),k6_partfun1(B_367))
      | ~ m1_subset_1(D_369,k1_zfmisc_1(k2_zfmisc_1(B_367,A_366)))
      | ~ v1_funct_2(D_369,B_367,A_366)
      | ~ v1_funct_1(D_369)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_366,B_367)))
      | ~ v1_funct_2(C_368,A_366,B_367)
      | ~ v1_funct_1(C_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_5446,plain,
    ( k2_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4542,c_5443])).

tff(c_5448,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_84,c_90,c_88,c_84,c_205,c_279,c_5446])).

tff(c_5450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4847,c_5448])).

tff(c_5452,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4824])).

tff(c_5453,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5452,c_279])).

tff(c_5527,plain,(
    ! [A_370,C_371,B_372] :
      ( k6_partfun1(A_370) = k5_relat_1(C_371,k2_funct_1(C_371))
      | k1_xboole_0 = B_372
      | ~ v2_funct_1(C_371)
      | k2_relset_1(A_370,B_372,C_371) != B_372
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_370,B_372)))
      | ~ v1_funct_2(C_371,A_370,B_372)
      | ~ v1_funct_1(C_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_5550,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_3','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_5527])).

tff(c_5572,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_5453,c_491,c_5550])).

tff(c_5582,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5572])).

tff(c_119,plain,(
    ! [B_85,A_86] :
      ( v1_xboole_0(B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86))
      | ~ v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_140,plain,(
    ! [A_7] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_142,plain,(
    ! [A_7] : ~ v1_xboole_0(A_7) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_4,plain,(
    ! [A_5] : v1_xboole_0('#skF_1'(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_4])).

tff(c_146,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_5613,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5582,c_146])).

tff(c_5617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_407,c_5613])).

tff(c_5619,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5572])).

tff(c_6443,plain,(
    ! [C_406,D_407,B_408,A_409] :
      ( k2_funct_1(C_406) = D_407
      | k1_xboole_0 = B_408
      | k1_xboole_0 = A_409
      | ~ v2_funct_1(C_406)
      | ~ r2_relset_1(A_409,A_409,k1_partfun1(A_409,B_408,B_408,A_409,C_406,D_407),k6_partfun1(A_409))
      | k2_relset_1(A_409,B_408,C_406) != B_408
      | ~ m1_subset_1(D_407,k1_zfmisc_1(k2_zfmisc_1(B_408,A_409)))
      | ~ v1_funct_2(D_407,B_408,A_409)
      | ~ v1_funct_1(D_407)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(A_409,B_408)))
      | ~ v1_funct_2(C_406,A_409,B_408)
      | ~ v1_funct_1(C_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_6446,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3'))
    | k2_relset_1('#skF_3','#skF_3','#skF_4') != '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4542,c_6443])).

tff(c_6448,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_84,c_90,c_88,c_84,c_5453,c_205,c_491,c_6446])).

tff(c_6449,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5619,c_6448])).

tff(c_4108,plain,(
    ! [A_311,B_312] :
      ( k2_funct_2(A_311,B_312) = k2_funct_1(B_312)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(k2_zfmisc_1(A_311,A_311)))
      | ~ v3_funct_2(B_312,A_311,A_311)
      | ~ v1_funct_2(B_312,A_311,A_311)
      | ~ v1_funct_1(B_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_4130,plain,
    ( k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_4108])).

tff(c_4149,plain,(
    k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_4130])).

tff(c_72,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_268])).

tff(c_4156,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4149,c_72])).

tff(c_4540,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4534,c_4156])).

tff(c_6483,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6449,c_4540])).

tff(c_6515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_6483])).

tff(c_6516,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_4524])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6575,plain,(
    ! [A_411] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4','#skF_5'),A_411)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_411)) ) ),
    inference(resolution,[status(thm)],[c_6516,c_2])).

tff(c_148,plain,(
    ! [C_90,B_91,A_92] :
      ( ~ v1_xboole_0(C_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(C_90))
      | ~ r2_hidden(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_163,plain,(
    ! [A_7,A_92] :
      ( ~ v1_xboole_0(A_7)
      | ~ r2_hidden(A_92,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_148])).

tff(c_164,plain,(
    ! [A_92] : ~ r2_hidden(A_92,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_6629,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_6575,c_164])).

tff(c_8303,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8298,c_6629])).

tff(c_8334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_8303])).

tff(c_8336,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8295])).

tff(c_7056,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6881])).

tff(c_7243,plain,(
    ! [A_430,B_431,C_432,D_433] :
      ( k2_relset_1(A_430,B_431,C_432) = B_431
      | ~ r2_relset_1(B_431,B_431,k1_partfun1(B_431,A_430,A_430,B_431,D_433,C_432),k6_partfun1(B_431))
      | ~ m1_subset_1(D_433,k1_zfmisc_1(k2_zfmisc_1(B_431,A_430)))
      | ~ v1_funct_2(D_433,B_431,A_430)
      | ~ v1_funct_1(D_433)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431)))
      | ~ v1_funct_2(C_432,A_430,B_431)
      | ~ v1_funct_1(C_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_7246,plain,
    ( k2_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3966,c_7243])).

tff(c_7248,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_90,c_88,c_84,c_205,c_281,c_7246])).

tff(c_7250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7056,c_7248])).

tff(c_7252,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6881])).

tff(c_6987,plain,(
    ! [A_417,C_418,B_419] :
      ( k6_partfun1(A_417) = k5_relat_1(C_418,k2_funct_1(C_418))
      | k1_xboole_0 = B_419
      | ~ v2_funct_1(C_418)
      | k2_relset_1(A_417,B_419,C_418) != B_419
      | ~ m1_subset_1(C_418,k1_zfmisc_1(k2_zfmisc_1(A_417,B_419)))
      | ~ v1_funct_2(C_418,A_417,B_419)
      | ~ v1_funct_1(C_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_7017,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_3','#skF_5') != '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_6987])).

tff(c_7044,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_281,c_495,c_7017])).

tff(c_7263,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7252,c_7044])).

tff(c_7264,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_7263])).

tff(c_7269,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7264,c_6629])).

tff(c_7300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_7269])).

tff(c_7302,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7263])).

tff(c_6852,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_3','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_6829])).

tff(c_6876,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_279,c_491,c_6852])).

tff(c_6900,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6876])).

tff(c_96,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_117,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_96])).

tff(c_571,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_546])).

tff(c_587,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_231,c_571])).

tff(c_7301,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7263])).

tff(c_16,plain,(
    ! [A_17] :
      ( k2_relat_1(k5_relat_1(A_17,k2_funct_1(A_17))) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7309,plain,
    ( k2_relat_1(k6_partfun1('#skF_3')) = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7301,c_16])).

tff(c_7315,plain,(
    k2_relat_1(k6_partfun1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_82,c_495,c_587,c_7309])).

tff(c_278,plain,(
    ! [A_52] : k2_relset_1(A_52,A_52,k6_partfun1(A_52)) = k2_relat_1(k6_partfun1(A_52)) ),
    inference(resolution,[status(thm)],[c_56,c_260])).

tff(c_7607,plain,(
    ! [B_449,C_447,A_450,D_448,E_451] :
      ( k2_relset_1(A_450,B_449,D_448) = B_449
      | k1_xboole_0 = C_447
      | ~ v2_funct_1(E_451)
      | k2_relset_1(A_450,C_447,k1_partfun1(A_450,B_449,B_449,C_447,D_448,E_451)) != C_447
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(B_449,C_447)))
      | ~ v1_funct_2(E_451,B_449,C_447)
      | ~ v1_funct_1(E_451)
      | ~ m1_subset_1(D_448,k1_zfmisc_1(k2_zfmisc_1(A_450,B_449)))
      | ~ v1_funct_2(D_448,A_450,B_449)
      | ~ v1_funct_1(D_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_7609,plain,
    ( k2_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3')) != '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3966,c_7607])).

tff(c_7611,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_84,c_82,c_80,c_76,c_7315,c_278,c_495,c_279,c_7609])).

tff(c_7613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7302,c_6900,c_7611])).

tff(c_7615,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6876])).

tff(c_7616,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7615,c_279])).

tff(c_9431,plain,(
    ! [C_512,D_513,B_514,A_515] :
      ( k2_funct_1(C_512) = D_513
      | k1_xboole_0 = B_514
      | k1_xboole_0 = A_515
      | ~ v2_funct_1(C_512)
      | ~ r2_relset_1(A_515,A_515,k1_partfun1(A_515,B_514,B_514,A_515,C_512,D_513),k6_partfun1(A_515))
      | k2_relset_1(A_515,B_514,C_512) != B_514
      | ~ m1_subset_1(D_513,k1_zfmisc_1(k2_zfmisc_1(B_514,A_515)))
      | ~ v1_funct_2(D_513,B_514,A_515)
      | ~ v1_funct_1(D_513)
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(A_515,B_514)))
      | ~ v1_funct_2(C_512,A_515,B_514)
      | ~ v1_funct_1(C_512) ) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_9434,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3'))
    | k2_relset_1('#skF_3','#skF_3','#skF_4') != '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3966,c_9431])).

tff(c_9436,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_84,c_82,c_80,c_76,c_7616,c_205,c_491,c_9434])).

tff(c_9437,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_8336,c_9436])).

tff(c_6630,plain,(
    ! [A_412,B_413] :
      ( m1_subset_1(k2_funct_2(A_412,B_413),k1_zfmisc_1(k2_zfmisc_1(A_412,A_412)))
      | ~ m1_subset_1(B_413,k1_zfmisc_1(k2_zfmisc_1(A_412,A_412)))
      | ~ v3_funct_2(B_413,A_412,A_412)
      | ~ v1_funct_2(B_413,A_412,A_412)
      | ~ v1_funct_1(B_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_6685,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4149,c_6630])).

tff(c_6707,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_6685])).

tff(c_4409,plain,(
    ! [B_326] :
      ( r2_hidden('#skF_2'('#skF_3',B_326,'#skF_5'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_326,'#skF_5')
      | ~ m1_subset_1(B_326,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_76,c_4373])).

tff(c_8159,plain,
    ( r2_hidden('#skF_2'('#skF_3',k2_funct_1('#skF_4'),'#skF_5'),'#skF_3')
    | r2_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6707,c_4409])).

tff(c_9323,plain,(
    r2_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8159])).

tff(c_9325,plain,
    ( k2_funct_1('#skF_4') = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_9323,c_30])).

tff(c_9328,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6707,c_76,c_9325])).

tff(c_9342,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9328,c_4156])).

tff(c_9359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_9342])).

tff(c_9361,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_8159])).

tff(c_9438,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9437,c_9361])).

tff(c_9456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_9438])).

tff(c_9458,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_14,plain,(
    ! [C_16,B_15,A_14] :
      ( ~ v1_xboole_0(C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(C_16))
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_375,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_14,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_354,c_14])).

tff(c_9514,plain,(
    ! [A_14] : ~ r2_hidden(A_14,k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9458,c_375])).

tff(c_11400,plain,(
    ! [A_14] : ~ r2_hidden(A_14,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11392,c_9514])).

tff(c_11956,plain,(
    ! [A_661,B_662,C_663] :
      ( r2_hidden('#skF_2'(A_661,B_662,C_663),A_661)
      | r2_relset_1(A_661,A_661,B_662,C_663)
      | ~ m1_subset_1(C_663,k1_zfmisc_1(k2_zfmisc_1(A_661,A_661)))
      | ~ m1_subset_1(B_662,k1_zfmisc_1(k2_zfmisc_1(A_661,A_661))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_11975,plain,(
    ! [B_662] :
      ( r2_hidden('#skF_2'('#skF_3',B_662,'#skF_4'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_662,'#skF_4')
      | ~ m1_subset_1(B_662,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_84,c_11956])).

tff(c_12000,plain,(
    ! [B_666] :
      ( r2_relset_1('#skF_3','#skF_3',B_666,'#skF_4')
      | ~ m1_subset_1(B_666,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11400,c_11975])).

tff(c_12049,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_12000])).

tff(c_12166,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_12049,c_30])).

tff(c_12169,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_84,c_12166])).

tff(c_209,plain,(
    ! [A_111,B_112] : r2_relset_1(A_111,B_112,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_192])).

tff(c_12195,plain,(
    ! [A_111,B_112] : r2_relset_1(A_111,B_112,'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12169,c_12169,c_209])).

tff(c_232,plain,(
    ! [A_114,B_115] : k1_relset_1(A_114,B_115,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_210])).

tff(c_341,plain,(
    ! [A_114,B_115] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_114))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_307])).

tff(c_356,plain,(
    ! [A_114] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_114)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_341])).

tff(c_12192,plain,(
    ! [A_114] : m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(A_114)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12169,c_356])).

tff(c_12221,plain,(
    ! [A_114] : m1_subset_1('#skF_3',k1_zfmisc_1(A_114)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11392,c_12192])).

tff(c_12199,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12169,c_8])).

tff(c_12356,plain,(
    ! [A_677] : m1_subset_1('#skF_3',k1_zfmisc_1(A_677)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11392,c_12192])).

tff(c_11992,plain,(
    ! [B_662] :
      ( r2_relset_1('#skF_3','#skF_3',B_662,'#skF_4')
      | ~ m1_subset_1(B_662,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11400,c_11975])).

tff(c_12416,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_12356,c_11992])).

tff(c_12496,plain,
    ( '#skF_3' = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_12416,c_30])).

tff(c_12499,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12221,c_12199,c_12496])).

tff(c_12048,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_12000])).

tff(c_12051,plain,
    ( '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_12048,c_30])).

tff(c_12054,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_84,c_12051])).

tff(c_11687,plain,(
    ! [A_649,B_650] :
      ( k2_funct_2(A_649,B_650) = k2_funct_1(B_650)
      | ~ m1_subset_1(B_650,k1_zfmisc_1(k2_zfmisc_1(A_649,A_649)))
      | ~ v3_funct_2(B_650,A_649,A_649)
      | ~ v1_funct_2(B_650,A_649,A_649)
      | ~ v1_funct_1(B_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_11716,plain,
    ( k2_funct_2('#skF_3','#skF_5') = k2_funct_1('#skF_5')
    | ~ v3_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_11687])).

tff(c_11732,plain,(
    k2_funct_2('#skF_3','#skF_5') = k2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_11716])).

tff(c_12055,plain,(
    ! [A_667,B_668] :
      ( m1_subset_1(k2_funct_2(A_667,B_668),k1_zfmisc_1(k2_zfmisc_1(A_667,A_667)))
      | ~ m1_subset_1(B_668,k1_zfmisc_1(k2_zfmisc_1(A_667,A_667)))
      | ~ v3_funct_2(B_668,A_667,A_667)
      | ~ v1_funct_2(B_668,A_667,A_667)
      | ~ v1_funct_1(B_668) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_12101,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v3_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11732,c_12055])).

tff(c_12122,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_12101])).

tff(c_12808,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12499,c_12499,c_12054,c_12122])).

tff(c_11980,plain,(
    ! [B_662] :
      ( r2_hidden('#skF_2'('#skF_3',B_662,'#skF_5'),'#skF_3')
      | r2_relset_1('#skF_3','#skF_3',B_662,'#skF_5')
      | ~ m1_subset_1(B_662,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_76,c_11956])).

tff(c_11996,plain,(
    ! [B_662] :
      ( r2_relset_1('#skF_3','#skF_3',B_662,'#skF_5')
      | ~ m1_subset_1(B_662,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11400,c_11980])).

tff(c_12668,plain,(
    ! [B_662] :
      ( r2_relset_1('#skF_4','#skF_4',B_662,'#skF_4')
      | ~ m1_subset_1(B_662,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12499,c_12499,c_12499,c_12499,c_12054,c_11996])).

tff(c_12857,plain,(
    r2_relset_1('#skF_4','#skF_4',k2_funct_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12808,c_12668])).

tff(c_12943,plain,
    ( k2_funct_1('#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4')))
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_12857,c_30])).

tff(c_12946,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12808,c_12199,c_12943])).

tff(c_11709,plain,
    ( k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_11687])).

tff(c_11728,plain,(
    k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_11709])).

tff(c_11737,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_5',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11728,c_72])).

tff(c_12128,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12054,c_11737])).

tff(c_12505,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12499,c_12499,c_12128])).

tff(c_12955,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12946,c_12505])).

tff(c_12967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12195,c_12955])).

tff(c_12968,plain,(
    ! [A_7] : ~ v1_xboole_0(A_7) ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_12972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12968,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.53/3.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.70/4.01  
% 10.70/4.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.70/4.01  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k11_relat_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 10.70/4.01  
% 10.70/4.01  %Foreground sorts:
% 10.70/4.01  
% 10.70/4.01  
% 10.70/4.01  %Background operators:
% 10.70/4.01  
% 10.70/4.01  
% 10.70/4.01  %Foreground operators:
% 10.70/4.01  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.70/4.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.70/4.01  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.70/4.01  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.70/4.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.70/4.01  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.70/4.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.70/4.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.70/4.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.70/4.01  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.70/4.01  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 10.70/4.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.70/4.01  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.70/4.01  tff('#skF_5', type, '#skF_5': $i).
% 10.70/4.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.70/4.01  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 10.70/4.01  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.70/4.01  tff('#skF_3', type, '#skF_3': $i).
% 10.70/4.01  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.70/4.01  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 10.70/4.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.70/4.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.70/4.01  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.70/4.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.70/4.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.70/4.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.70/4.01  tff('#skF_4', type, '#skF_4': $i).
% 10.70/4.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.70/4.01  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 10.70/4.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.70/4.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.70/4.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.70/4.01  
% 10.70/4.05  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 10.70/4.05  tff(f_268, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 10.70/4.05  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.70/4.05  tff(f_246, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 10.70/4.05  tff(f_93, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.70/4.05  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 10.70/4.05  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.70/4.05  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 10.70/4.05  tff(f_213, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 10.70/4.05  tff(f_149, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.70/4.05  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.70/4.05  tff(f_176, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 10.70/4.05  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.70/4.05  tff(f_105, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relset_1)).
% 10.70/4.05  tff(f_37, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 10.70/4.05  tff(f_238, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 10.70/4.05  tff(f_159, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 10.70/4.05  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 10.70/4.05  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 10.70/4.05  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.70/4.05  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 10.70/4.05  tff(f_197, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 10.70/4.05  tff(f_145, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 10.70/4.05  tff(c_8, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.70/4.05  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_268])).
% 10.70/4.05  tff(c_90, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_268])).
% 10.70/4.05  tff(c_88, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_268])).
% 10.70/4.05  tff(c_210, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.70/4.05  tff(c_229, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_210])).
% 10.70/4.05  tff(c_11355, plain, (![A_625, B_626]: (k1_relset_1(A_625, A_625, B_626)=A_625 | ~m1_subset_1(B_626, k1_zfmisc_1(k2_zfmisc_1(A_625, A_625))) | ~v1_funct_2(B_626, A_625, A_625) | ~v1_funct_1(B_626))), inference(cnfTransformation, [status(thm)], [f_246])).
% 10.70/4.05  tff(c_11373, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_11355])).
% 10.70/4.05  tff(c_11392, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_229, c_11373])).
% 10.70/4.05  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_268])).
% 10.70/4.05  tff(c_192, plain, (![A_111, B_112, D_113]: (r2_relset_1(A_111, B_112, D_113, D_113) | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.70/4.05  tff(c_208, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_192])).
% 10.70/4.05  tff(c_546, plain, (![A_153, B_154]: (k1_relset_1(A_153, A_153, B_154)=A_153 | ~m1_subset_1(B_154, k1_zfmisc_1(k2_zfmisc_1(A_153, A_153))) | ~v1_funct_2(B_154, A_153, A_153) | ~v1_funct_1(B_154))), inference(cnfTransformation, [status(thm)], [f_246])).
% 10.70/4.05  tff(c_564, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_546])).
% 10.70/4.05  tff(c_583, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_229, c_564])).
% 10.70/4.05  tff(c_307, plain, (![A_131, B_132, C_133]: (m1_subset_1(k1_relset_1(A_131, B_132, C_133), k1_zfmisc_1(A_131)) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.70/4.05  tff(c_338, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_229, c_307])).
% 10.70/4.05  tff(c_354, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_338])).
% 10.70/4.05  tff(c_591, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_583, c_354])).
% 10.70/4.05  tff(c_82, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_268])).
% 10.70/4.05  tff(c_80, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_268])).
% 10.70/4.05  tff(c_260, plain, (![A_125, B_126, C_127]: (k2_relset_1(A_125, B_126, C_127)=k2_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.70/4.05  tff(c_281, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_260])).
% 10.70/4.05  tff(c_78, plain, (v3_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_268])).
% 10.70/4.05  tff(c_455, plain, (![C_137, A_138, B_139]: (v2_funct_1(C_137) | ~v3_funct_2(C_137, A_138, B_139) | ~v1_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.70/4.05  tff(c_480, plain, (v2_funct_1('#skF_5') | ~v3_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_455])).
% 10.70/4.05  tff(c_495, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_480])).
% 10.70/4.05  tff(c_6829, plain, (![B_414, C_415, A_416]: (k6_partfun1(B_414)=k5_relat_1(k2_funct_1(C_415), C_415) | k1_xboole_0=B_414 | ~v2_funct_1(C_415) | k2_relset_1(A_416, B_414, C_415)!=B_414 | ~m1_subset_1(C_415, k1_zfmisc_1(k2_zfmisc_1(A_416, B_414))) | ~v1_funct_2(C_415, A_416, B_414) | ~v1_funct_1(C_415))), inference(cnfTransformation, [status(thm)], [f_213])).
% 10.70/4.05  tff(c_6857, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_3', '#skF_5')!='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_6829])).
% 10.70/4.05  tff(c_6881, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_281, c_495, c_6857])).
% 10.70/4.05  tff(c_7625, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_6881])).
% 10.70/4.05  tff(c_56, plain, (![A_52]: (m1_subset_1(k6_partfun1(A_52), k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.70/4.05  tff(c_205, plain, (![A_52]: (r2_relset_1(A_52, A_52, k6_partfun1(A_52), k6_partfun1(A_52)))), inference(resolution, [status(thm)], [c_56, c_192])).
% 10.70/4.05  tff(c_3890, plain, (![D_296, C_297, A_299, F_295, B_298, E_294]: (m1_subset_1(k1_partfun1(A_299, B_298, C_297, D_296, E_294, F_295), k1_zfmisc_1(k2_zfmisc_1(A_299, D_296))) | ~m1_subset_1(F_295, k1_zfmisc_1(k2_zfmisc_1(C_297, D_296))) | ~v1_funct_1(F_295) | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(A_299, B_298))) | ~v1_funct_1(E_294))), inference(cnfTransformation, [status(thm)], [f_129])).
% 10.70/4.05  tff(c_74, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 10.70/4.05  tff(c_625, plain, (![D_155, C_156, A_157, B_158]: (D_155=C_156 | ~r2_relset_1(A_157, B_158, C_156, D_155) | ~m1_subset_1(D_155, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.70/4.05  tff(c_639, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_74, c_625])).
% 10.70/4.05  tff(c_666, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_639])).
% 10.70/4.05  tff(c_677, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_666])).
% 10.70/4.05  tff(c_3920, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_3890, c_677])).
% 10.70/4.05  tff(c_3965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_84, c_82, c_76, c_3920])).
% 10.70/4.05  tff(c_3966, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_666])).
% 10.70/4.05  tff(c_8087, plain, (![A_464, B_465, C_466, D_467]: (k2_relset_1(A_464, B_465, C_466)=B_465 | ~r2_relset_1(B_465, B_465, k1_partfun1(B_465, A_464, A_464, B_465, D_467, C_466), k6_partfun1(B_465)) | ~m1_subset_1(D_467, k1_zfmisc_1(k2_zfmisc_1(B_465, A_464))) | ~v1_funct_2(D_467, B_465, A_464) | ~v1_funct_1(D_467) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_464, B_465))) | ~v1_funct_2(C_466, A_464, B_465) | ~v1_funct_1(C_466))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.70/4.05  tff(c_8090, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3966, c_8087])).
% 10.70/4.05  tff(c_8092, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_90, c_88, c_84, c_205, c_281, c_8090])).
% 10.70/4.05  tff(c_8094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7625, c_8092])).
% 10.70/4.05  tff(c_8096, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_6881])).
% 10.70/4.05  tff(c_8097, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8096, c_281])).
% 10.70/4.05  tff(c_8238, plain, (![A_468, C_469, B_470]: (k6_partfun1(A_468)=k5_relat_1(C_469, k2_funct_1(C_469)) | k1_xboole_0=B_470 | ~v2_funct_1(C_469) | k2_relset_1(A_468, B_470, C_469)!=B_470 | ~m1_subset_1(C_469, k1_zfmisc_1(k2_zfmisc_1(A_468, B_470))) | ~v1_funct_2(C_469, A_468, B_470) | ~v1_funct_1(C_469))), inference(cnfTransformation, [status(thm)], [f_213])).
% 10.70/4.05  tff(c_8268, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_3', '#skF_5')!='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_8238])).
% 10.70/4.05  tff(c_8295, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_8097, c_495, c_8268])).
% 10.70/4.05  tff(c_8298, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_8295])).
% 10.70/4.05  tff(c_206, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_192])).
% 10.70/4.05  tff(c_231, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_210])).
% 10.70/4.05  tff(c_335, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_231, c_307])).
% 10.70/4.05  tff(c_352, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_335])).
% 10.70/4.05  tff(c_10, plain, (![B_10, A_8]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.70/4.05  tff(c_366, plain, (v1_xboole_0(k1_relat_1('#skF_5')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_352, c_10])).
% 10.70/4.05  tff(c_407, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_366])).
% 10.70/4.05  tff(c_279, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_260])).
% 10.70/4.05  tff(c_86, plain, (v3_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_268])).
% 10.70/4.05  tff(c_473, plain, (v2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_455])).
% 10.70/4.05  tff(c_491, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_473])).
% 10.70/4.05  tff(c_4779, plain, (![B_346, C_347, A_348]: (k6_partfun1(B_346)=k5_relat_1(k2_funct_1(C_347), C_347) | k1_xboole_0=B_346 | ~v2_funct_1(C_347) | k2_relset_1(A_348, B_346, C_347)!=B_346 | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_348, B_346))) | ~v1_funct_2(C_347, A_348, B_346) | ~v1_funct_1(C_347))), inference(cnfTransformation, [status(thm)], [f_213])).
% 10.70/4.05  tff(c_4802, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_3', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_4779])).
% 10.70/4.05  tff(c_4824, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_279, c_491, c_4802])).
% 10.70/4.05  tff(c_4847, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_4824])).
% 10.70/4.05  tff(c_4373, plain, (![A_325, B_326, C_327]: (r2_hidden('#skF_2'(A_325, B_326, C_327), A_325) | r2_relset_1(A_325, A_325, B_326, C_327) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, A_325))) | ~m1_subset_1(B_326, k1_zfmisc_1(k2_zfmisc_1(A_325, A_325))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.70/4.05  tff(c_4479, plain, (![B_342]: (r2_hidden('#skF_2'('#skF_3', B_342, '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_342, '#skF_5') | ~m1_subset_1(B_342, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_76, c_4373])).
% 10.70/4.05  tff(c_4524, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_84, c_4479])).
% 10.70/4.05  tff(c_4529, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_4524])).
% 10.70/4.05  tff(c_30, plain, (![D_33, C_32, A_30, B_31]: (D_33=C_32 | ~r2_relset_1(A_30, B_31, C_32, D_33) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.70/4.05  tff(c_4531, plain, ('#skF_5'='#skF_4' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_4529, c_30])).
% 10.70/4.05  tff(c_4534, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_76, c_4531])).
% 10.70/4.05  tff(c_4542, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_4')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_3966])).
% 10.70/4.05  tff(c_5443, plain, (![A_366, B_367, C_368, D_369]: (k2_relset_1(A_366, B_367, C_368)=B_367 | ~r2_relset_1(B_367, B_367, k1_partfun1(B_367, A_366, A_366, B_367, D_369, C_368), k6_partfun1(B_367)) | ~m1_subset_1(D_369, k1_zfmisc_1(k2_zfmisc_1(B_367, A_366))) | ~v1_funct_2(D_369, B_367, A_366) | ~v1_funct_1(D_369) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_366, B_367))) | ~v1_funct_2(C_368, A_366, B_367) | ~v1_funct_1(C_368))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.70/4.05  tff(c_5446, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4542, c_5443])).
% 10.70/4.05  tff(c_5448, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_84, c_90, c_88, c_84, c_205, c_279, c_5446])).
% 10.70/4.05  tff(c_5450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4847, c_5448])).
% 10.70/4.05  tff(c_5452, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_4824])).
% 10.70/4.05  tff(c_5453, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5452, c_279])).
% 10.70/4.05  tff(c_5527, plain, (![A_370, C_371, B_372]: (k6_partfun1(A_370)=k5_relat_1(C_371, k2_funct_1(C_371)) | k1_xboole_0=B_372 | ~v2_funct_1(C_371) | k2_relset_1(A_370, B_372, C_371)!=B_372 | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_370, B_372))) | ~v1_funct_2(C_371, A_370, B_372) | ~v1_funct_1(C_371))), inference(cnfTransformation, [status(thm)], [f_213])).
% 10.70/4.05  tff(c_5550, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_3', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_5527])).
% 10.70/4.05  tff(c_5572, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_5453, c_491, c_5550])).
% 10.70/4.05  tff(c_5582, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5572])).
% 10.70/4.05  tff(c_119, plain, (![B_85, A_86]: (v1_xboole_0(B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)) | ~v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.70/4.05  tff(c_140, plain, (![A_7]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_7))), inference(resolution, [status(thm)], [c_8, c_119])).
% 10.70/4.05  tff(c_142, plain, (![A_7]: (~v1_xboole_0(A_7))), inference(splitLeft, [status(thm)], [c_140])).
% 10.70/4.05  tff(c_4, plain, (![A_5]: (v1_xboole_0('#skF_1'(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.70/4.05  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_4])).
% 10.70/4.05  tff(c_146, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_140])).
% 10.70/4.05  tff(c_5613, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5582, c_146])).
% 10.70/4.05  tff(c_5617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_407, c_5613])).
% 10.70/4.05  tff(c_5619, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5572])).
% 10.70/4.05  tff(c_6443, plain, (![C_406, D_407, B_408, A_409]: (k2_funct_1(C_406)=D_407 | k1_xboole_0=B_408 | k1_xboole_0=A_409 | ~v2_funct_1(C_406) | ~r2_relset_1(A_409, A_409, k1_partfun1(A_409, B_408, B_408, A_409, C_406, D_407), k6_partfun1(A_409)) | k2_relset_1(A_409, B_408, C_406)!=B_408 | ~m1_subset_1(D_407, k1_zfmisc_1(k2_zfmisc_1(B_408, A_409))) | ~v1_funct_2(D_407, B_408, A_409) | ~v1_funct_1(D_407) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(A_409, B_408))) | ~v1_funct_2(C_406, A_409, B_408) | ~v1_funct_1(C_406))), inference(cnfTransformation, [status(thm)], [f_238])).
% 10.70/4.05  tff(c_6446, plain, (k2_funct_1('#skF_4')='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3')) | k2_relset_1('#skF_3', '#skF_3', '#skF_4')!='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4542, c_6443])).
% 10.70/4.05  tff(c_6448, plain, (k2_funct_1('#skF_4')='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_84, c_90, c_88, c_84, c_5453, c_205, c_491, c_6446])).
% 10.70/4.05  tff(c_6449, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5619, c_6448])).
% 10.70/4.05  tff(c_4108, plain, (![A_311, B_312]: (k2_funct_2(A_311, B_312)=k2_funct_1(B_312) | ~m1_subset_1(B_312, k1_zfmisc_1(k2_zfmisc_1(A_311, A_311))) | ~v3_funct_2(B_312, A_311, A_311) | ~v1_funct_2(B_312, A_311, A_311) | ~v1_funct_1(B_312))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.70/4.05  tff(c_4130, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_4108])).
% 10.70/4.05  tff(c_4149, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_4130])).
% 10.70/4.05  tff(c_72, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_268])).
% 10.70/4.05  tff(c_4156, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4149, c_72])).
% 10.70/4.05  tff(c_4540, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4534, c_4156])).
% 10.70/4.05  tff(c_6483, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6449, c_4540])).
% 10.70/4.05  tff(c_6515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_6483])).
% 10.70/4.05  tff(c_6516, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_4524])).
% 10.70/4.05  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.70/4.05  tff(c_6575, plain, (![A_411]: (r2_hidden('#skF_2'('#skF_3', '#skF_4', '#skF_5'), A_411) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_411)))), inference(resolution, [status(thm)], [c_6516, c_2])).
% 10.70/4.05  tff(c_148, plain, (![C_90, B_91, A_92]: (~v1_xboole_0(C_90) | ~m1_subset_1(B_91, k1_zfmisc_1(C_90)) | ~r2_hidden(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.70/4.05  tff(c_163, plain, (![A_7, A_92]: (~v1_xboole_0(A_7) | ~r2_hidden(A_92, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_148])).
% 10.70/4.05  tff(c_164, plain, (![A_92]: (~r2_hidden(A_92, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_163])).
% 10.70/4.05  tff(c_6629, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_6575, c_164])).
% 10.70/4.05  tff(c_8303, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8298, c_6629])).
% 10.70/4.05  tff(c_8334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_591, c_8303])).
% 10.70/4.05  tff(c_8336, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_8295])).
% 10.70/4.05  tff(c_7056, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_6881])).
% 10.70/4.05  tff(c_7243, plain, (![A_430, B_431, C_432, D_433]: (k2_relset_1(A_430, B_431, C_432)=B_431 | ~r2_relset_1(B_431, B_431, k1_partfun1(B_431, A_430, A_430, B_431, D_433, C_432), k6_partfun1(B_431)) | ~m1_subset_1(D_433, k1_zfmisc_1(k2_zfmisc_1(B_431, A_430))) | ~v1_funct_2(D_433, B_431, A_430) | ~v1_funct_1(D_433) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))) | ~v1_funct_2(C_432, A_430, B_431) | ~v1_funct_1(C_432))), inference(cnfTransformation, [status(thm)], [f_176])).
% 10.70/4.05  tff(c_7246, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3966, c_7243])).
% 10.70/4.05  tff(c_7248, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_90, c_88, c_84, c_205, c_281, c_7246])).
% 10.70/4.05  tff(c_7250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7056, c_7248])).
% 10.70/4.05  tff(c_7252, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(splitRight, [status(thm)], [c_6881])).
% 10.70/4.05  tff(c_6987, plain, (![A_417, C_418, B_419]: (k6_partfun1(A_417)=k5_relat_1(C_418, k2_funct_1(C_418)) | k1_xboole_0=B_419 | ~v2_funct_1(C_418) | k2_relset_1(A_417, B_419, C_418)!=B_419 | ~m1_subset_1(C_418, k1_zfmisc_1(k2_zfmisc_1(A_417, B_419))) | ~v1_funct_2(C_418, A_417, B_419) | ~v1_funct_1(C_418))), inference(cnfTransformation, [status(thm)], [f_213])).
% 10.70/4.05  tff(c_7017, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_3', '#skF_5')!='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_6987])).
% 10.70/4.05  tff(c_7044, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_281, c_495, c_7017])).
% 10.70/4.05  tff(c_7263, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7252, c_7044])).
% 10.70/4.05  tff(c_7264, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_7263])).
% 10.70/4.05  tff(c_7269, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7264, c_6629])).
% 10.70/4.05  tff(c_7300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_591, c_7269])).
% 10.70/4.05  tff(c_7302, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_7263])).
% 10.70/4.05  tff(c_6852, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_3', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_6829])).
% 10.70/4.05  tff(c_6876, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_279, c_491, c_6852])).
% 10.70/4.05  tff(c_6900, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_6876])).
% 10.70/4.05  tff(c_96, plain, (![C_82, A_83, B_84]: (v1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.70/4.05  tff(c_117, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_96])).
% 10.70/4.05  tff(c_571, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_546])).
% 10.70/4.05  tff(c_587, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_231, c_571])).
% 10.70/4.05  tff(c_7301, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_7263])).
% 10.70/4.05  tff(c_16, plain, (![A_17]: (k2_relat_1(k5_relat_1(A_17, k2_funct_1(A_17)))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.70/4.05  tff(c_7309, plain, (k2_relat_1(k6_partfun1('#skF_3'))=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7301, c_16])).
% 10.70/4.05  tff(c_7315, plain, (k2_relat_1(k6_partfun1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_117, c_82, c_495, c_587, c_7309])).
% 10.70/4.05  tff(c_278, plain, (![A_52]: (k2_relset_1(A_52, A_52, k6_partfun1(A_52))=k2_relat_1(k6_partfun1(A_52)))), inference(resolution, [status(thm)], [c_56, c_260])).
% 10.70/4.05  tff(c_7607, plain, (![B_449, C_447, A_450, D_448, E_451]: (k2_relset_1(A_450, B_449, D_448)=B_449 | k1_xboole_0=C_447 | ~v2_funct_1(E_451) | k2_relset_1(A_450, C_447, k1_partfun1(A_450, B_449, B_449, C_447, D_448, E_451))!=C_447 | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(B_449, C_447))) | ~v1_funct_2(E_451, B_449, C_447) | ~v1_funct_1(E_451) | ~m1_subset_1(D_448, k1_zfmisc_1(k2_zfmisc_1(A_450, B_449))) | ~v1_funct_2(D_448, A_450, B_449) | ~v1_funct_1(D_448))), inference(cnfTransformation, [status(thm)], [f_197])).
% 10.70/4.05  tff(c_7609, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'))!='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3966, c_7607])).
% 10.70/4.05  tff(c_7611, plain, (k2_relat_1('#skF_4')='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_84, c_82, c_80, c_76, c_7315, c_278, c_495, c_279, c_7609])).
% 10.70/4.05  tff(c_7613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7302, c_6900, c_7611])).
% 10.70/4.05  tff(c_7615, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_6876])).
% 10.70/4.05  tff(c_7616, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7615, c_279])).
% 10.70/4.05  tff(c_9431, plain, (![C_512, D_513, B_514, A_515]: (k2_funct_1(C_512)=D_513 | k1_xboole_0=B_514 | k1_xboole_0=A_515 | ~v2_funct_1(C_512) | ~r2_relset_1(A_515, A_515, k1_partfun1(A_515, B_514, B_514, A_515, C_512, D_513), k6_partfun1(A_515)) | k2_relset_1(A_515, B_514, C_512)!=B_514 | ~m1_subset_1(D_513, k1_zfmisc_1(k2_zfmisc_1(B_514, A_515))) | ~v1_funct_2(D_513, B_514, A_515) | ~v1_funct_1(D_513) | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(A_515, B_514))) | ~v1_funct_2(C_512, A_515, B_514) | ~v1_funct_1(C_512))), inference(cnfTransformation, [status(thm)], [f_238])).
% 10.70/4.05  tff(c_9434, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3')) | k2_relset_1('#skF_3', '#skF_3', '#skF_4')!='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3966, c_9431])).
% 10.70/4.05  tff(c_9436, plain, (k2_funct_1('#skF_4')='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_84, c_82, c_80, c_76, c_7616, c_205, c_491, c_9434])).
% 10.70/4.05  tff(c_9437, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_8336, c_9436])).
% 10.70/4.05  tff(c_6630, plain, (![A_412, B_413]: (m1_subset_1(k2_funct_2(A_412, B_413), k1_zfmisc_1(k2_zfmisc_1(A_412, A_412))) | ~m1_subset_1(B_413, k1_zfmisc_1(k2_zfmisc_1(A_412, A_412))) | ~v3_funct_2(B_413, A_412, A_412) | ~v1_funct_2(B_413, A_412, A_412) | ~v1_funct_1(B_413))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.70/4.05  tff(c_6685, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4149, c_6630])).
% 10.70/4.05  tff(c_6707, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_6685])).
% 10.70/4.05  tff(c_4409, plain, (![B_326]: (r2_hidden('#skF_2'('#skF_3', B_326, '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_326, '#skF_5') | ~m1_subset_1(B_326, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_76, c_4373])).
% 10.70/4.05  tff(c_8159, plain, (r2_hidden('#skF_2'('#skF_3', k2_funct_1('#skF_4'), '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_6707, c_4409])).
% 10.70/4.05  tff(c_9323, plain, (r2_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_8159])).
% 10.70/4.05  tff(c_9325, plain, (k2_funct_1('#skF_4')='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_9323, c_30])).
% 10.70/4.05  tff(c_9328, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6707, c_76, c_9325])).
% 10.70/4.05  tff(c_9342, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9328, c_4156])).
% 10.70/4.05  tff(c_9359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_208, c_9342])).
% 10.70/4.05  tff(c_9361, plain, (~r2_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_8159])).
% 10.70/4.05  tff(c_9438, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9437, c_9361])).
% 10.70/4.05  tff(c_9456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_208, c_9438])).
% 10.70/4.05  tff(c_9458, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_366])).
% 10.70/4.05  tff(c_14, plain, (![C_16, B_15, A_14]: (~v1_xboole_0(C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(C_16)) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.70/4.05  tff(c_375, plain, (![A_14]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_14, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_354, c_14])).
% 10.70/4.05  tff(c_9514, plain, (![A_14]: (~r2_hidden(A_14, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9458, c_375])).
% 10.70/4.05  tff(c_11400, plain, (![A_14]: (~r2_hidden(A_14, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11392, c_9514])).
% 10.70/4.05  tff(c_11956, plain, (![A_661, B_662, C_663]: (r2_hidden('#skF_2'(A_661, B_662, C_663), A_661) | r2_relset_1(A_661, A_661, B_662, C_663) | ~m1_subset_1(C_663, k1_zfmisc_1(k2_zfmisc_1(A_661, A_661))) | ~m1_subset_1(B_662, k1_zfmisc_1(k2_zfmisc_1(A_661, A_661))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.70/4.05  tff(c_11975, plain, (![B_662]: (r2_hidden('#skF_2'('#skF_3', B_662, '#skF_4'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_662, '#skF_4') | ~m1_subset_1(B_662, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_84, c_11956])).
% 10.70/4.05  tff(c_12000, plain, (![B_666]: (r2_relset_1('#skF_3', '#skF_3', B_666, '#skF_4') | ~m1_subset_1(B_666, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_11400, c_11975])).
% 10.70/4.05  tff(c_12049, plain, (r2_relset_1('#skF_3', '#skF_3', k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_8, c_12000])).
% 10.70/4.05  tff(c_12166, plain, (k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_12049, c_30])).
% 10.70/4.05  tff(c_12169, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_84, c_12166])).
% 10.70/4.05  tff(c_209, plain, (![A_111, B_112]: (r2_relset_1(A_111, B_112, k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_192])).
% 10.70/4.05  tff(c_12195, plain, (![A_111, B_112]: (r2_relset_1(A_111, B_112, '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12169, c_12169, c_209])).
% 10.70/4.05  tff(c_232, plain, (![A_114, B_115]: (k1_relset_1(A_114, B_115, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_210])).
% 10.70/4.05  tff(c_341, plain, (![A_114, B_115]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_114)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(superposition, [status(thm), theory('equality')], [c_232, c_307])).
% 10.70/4.05  tff(c_356, plain, (![A_114]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_114)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_341])).
% 10.70/4.05  tff(c_12192, plain, (![A_114]: (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(A_114)))), inference(demodulation, [status(thm), theory('equality')], [c_12169, c_356])).
% 10.70/4.05  tff(c_12221, plain, (![A_114]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_114)))), inference(demodulation, [status(thm), theory('equality')], [c_11392, c_12192])).
% 10.70/4.05  tff(c_12199, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_12169, c_8])).
% 10.70/4.05  tff(c_12356, plain, (![A_677]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_677)))), inference(demodulation, [status(thm), theory('equality')], [c_11392, c_12192])).
% 10.70/4.05  tff(c_11992, plain, (![B_662]: (r2_relset_1('#skF_3', '#skF_3', B_662, '#skF_4') | ~m1_subset_1(B_662, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_11400, c_11975])).
% 10.70/4.05  tff(c_12416, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_12356, c_11992])).
% 10.70/4.05  tff(c_12496, plain, ('#skF_3'='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_12416, c_30])).
% 10.70/4.05  tff(c_12499, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12221, c_12199, c_12496])).
% 10.70/4.05  tff(c_12048, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_12000])).
% 10.70/4.05  tff(c_12051, plain, ('#skF_5'='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_12048, c_30])).
% 10.70/4.05  tff(c_12054, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_84, c_12051])).
% 10.70/4.05  tff(c_11687, plain, (![A_649, B_650]: (k2_funct_2(A_649, B_650)=k2_funct_1(B_650) | ~m1_subset_1(B_650, k1_zfmisc_1(k2_zfmisc_1(A_649, A_649))) | ~v3_funct_2(B_650, A_649, A_649) | ~v1_funct_2(B_650, A_649, A_649) | ~v1_funct_1(B_650))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.70/4.05  tff(c_11716, plain, (k2_funct_2('#skF_3', '#skF_5')=k2_funct_1('#skF_5') | ~v3_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_11687])).
% 10.70/4.05  tff(c_11732, plain, (k2_funct_2('#skF_3', '#skF_5')=k2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_11716])).
% 10.70/4.05  tff(c_12055, plain, (![A_667, B_668]: (m1_subset_1(k2_funct_2(A_667, B_668), k1_zfmisc_1(k2_zfmisc_1(A_667, A_667))) | ~m1_subset_1(B_668, k1_zfmisc_1(k2_zfmisc_1(A_667, A_667))) | ~v3_funct_2(B_668, A_667, A_667) | ~v1_funct_2(B_668, A_667, A_667) | ~v1_funct_1(B_668))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.70/4.05  tff(c_12101, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v3_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11732, c_12055])).
% 10.70/4.05  tff(c_12122, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_12101])).
% 10.70/4.05  tff(c_12808, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_12499, c_12499, c_12054, c_12122])).
% 10.70/4.05  tff(c_11980, plain, (![B_662]: (r2_hidden('#skF_2'('#skF_3', B_662, '#skF_5'), '#skF_3') | r2_relset_1('#skF_3', '#skF_3', B_662, '#skF_5') | ~m1_subset_1(B_662, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_76, c_11956])).
% 10.70/4.05  tff(c_11996, plain, (![B_662]: (r2_relset_1('#skF_3', '#skF_3', B_662, '#skF_5') | ~m1_subset_1(B_662, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_11400, c_11980])).
% 10.70/4.05  tff(c_12668, plain, (![B_662]: (r2_relset_1('#skF_4', '#skF_4', B_662, '#skF_4') | ~m1_subset_1(B_662, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_12499, c_12499, c_12499, c_12499, c_12054, c_11996])).
% 10.70/4.05  tff(c_12857, plain, (r2_relset_1('#skF_4', '#skF_4', k2_funct_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_12808, c_12668])).
% 10.70/4.05  tff(c_12943, plain, (k2_funct_1('#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4'))) | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_12857, c_30])).
% 10.70/4.05  tff(c_12946, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12808, c_12199, c_12943])).
% 10.70/4.05  tff(c_11709, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_11687])).
% 10.70/4.05  tff(c_11728, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_11709])).
% 10.70/4.05  tff(c_11737, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_5', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11728, c_72])).
% 10.70/4.05  tff(c_12128, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12054, c_11737])).
% 10.70/4.05  tff(c_12505, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12499, c_12499, c_12128])).
% 10.70/4.05  tff(c_12955, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12946, c_12505])).
% 10.70/4.05  tff(c_12967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12195, c_12955])).
% 10.70/4.05  tff(c_12968, plain, (![A_7]: (~v1_xboole_0(A_7))), inference(splitRight, [status(thm)], [c_163])).
% 10.70/4.05  tff(c_12972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12968, c_146])).
% 10.70/4.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.70/4.05  
% 10.70/4.05  Inference rules
% 10.70/4.05  ----------------------
% 10.70/4.05  #Ref     : 9
% 10.70/4.05  #Sup     : 2451
% 10.70/4.05  #Fact    : 0
% 10.70/4.05  #Define  : 0
% 10.70/4.05  #Split   : 83
% 10.70/4.05  #Chain   : 0
% 10.70/4.05  #Close   : 0
% 10.70/4.05  
% 10.70/4.05  Ordering : KBO
% 10.70/4.05  
% 10.70/4.05  Simplification rules
% 10.70/4.05  ----------------------
% 10.70/4.05  #Subsume      : 336
% 10.70/4.05  #Demod        : 4475
% 10.70/4.05  #Tautology    : 1009
% 10.70/4.05  #SimpNegUnit  : 166
% 10.70/4.05  #BackRed      : 1448
% 10.70/4.05  
% 10.70/4.05  #Partial instantiations: 0
% 10.70/4.05  #Strategies tried      : 1
% 10.70/4.05  
% 10.70/4.05  Timing (in seconds)
% 10.70/4.05  ----------------------
% 10.70/4.05  Preprocessing        : 0.43
% 10.70/4.05  Parsing              : 0.23
% 10.70/4.05  CNF conversion       : 0.03
% 10.70/4.05  Main loop            : 2.75
% 10.70/4.05  Inferencing          : 0.76
% 10.70/4.05  Reduction            : 1.15
% 10.70/4.05  Demodulation         : 0.87
% 10.70/4.05  BG Simplification    : 0.10
% 10.70/4.05  Subsumption          : 0.49
% 10.70/4.05  Abstraction          : 0.11
% 10.70/4.05  MUC search           : 0.00
% 10.70/4.05  Cooper               : 0.00
% 10.70/4.05  Total                : 3.26
% 10.70/4.05  Index Insertion      : 0.00
% 10.70/4.05  Index Deletion       : 0.00
% 10.70/4.05  Index Matching       : 0.00
% 10.70/4.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
