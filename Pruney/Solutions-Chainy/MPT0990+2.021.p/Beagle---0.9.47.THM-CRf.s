%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:58 EST 2020

% Result     : Theorem 11.56s
% Output     : CNFRefutation 11.56s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 743 expanded)
%              Number of leaves         :   44 ( 280 expanded)
%              Depth                    :   15
%              Number of atoms          :  465 (3019 expanded)
%              Number of equality atoms :  152 (1011 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_216,negated_conjecture,(
    ~ ! [A,B,C] :
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_112,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
           => ( v2_funct_1(C)
              & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_190,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_129,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_174,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(c_58,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_123,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_136,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_123])).

tff(c_137,plain,(
    ! [C_62,B_63,A_64] :
      ( v5_relat_1(C_62,B_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_149,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_137])).

tff(c_172,plain,(
    ! [B_72,A_73] :
      ( k2_relat_1(B_72) = A_73
      | ~ v2_funct_2(B_72,A_73)
      | ~ v5_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_178,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_149,c_172])).

tff(c_187,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_178])).

tff(c_191,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_38,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_26,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_81,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_26])).

tff(c_481,plain,(
    ! [A_114,B_115,D_116] :
      ( r2_relset_1(A_114,B_115,D_116,D_116)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_488,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_81,c_481])).

tff(c_620,plain,(
    ! [C_144,E_145,A_142,F_143,B_141,D_140] :
      ( k1_partfun1(A_142,B_141,C_144,D_140,E_145,F_143) = k5_relat_1(E_145,F_143)
      | ~ m1_subset_1(F_143,k1_zfmisc_1(k2_zfmisc_1(C_144,D_140)))
      | ~ v1_funct_1(F_143)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141)))
      | ~ v1_funct_1(E_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_626,plain,(
    ! [A_142,B_141,E_145] :
      ( k1_partfun1(A_142,B_141,'#skF_2','#skF_1',E_145,'#skF_4') = k5_relat_1(E_145,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141)))
      | ~ v1_funct_1(E_145) ) ),
    inference(resolution,[status(thm)],[c_70,c_620])).

tff(c_665,plain,(
    ! [A_152,B_153,E_154] :
      ( k1_partfun1(A_152,B_153,'#skF_2','#skF_1',E_154,'#skF_4') = k5_relat_1(E_154,'#skF_4')
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_1(E_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_626])).

tff(c_671,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_665])).

tff(c_678,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_671])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_510,plain,(
    ! [D_120,C_121,A_122,B_123] :
      ( D_120 = C_121
      | ~ r2_relset_1(A_122,B_123,C_121,D_120)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123)))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_518,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_510])).

tff(c_533,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_518])).

tff(c_534,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_533])).

tff(c_720,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_534])).

tff(c_836,plain,(
    ! [C_161,F_166,A_165,E_164,D_163,B_162] :
      ( m1_subset_1(k1_partfun1(A_165,B_162,C_161,D_163,E_164,F_166),k1_zfmisc_1(k2_zfmisc_1(A_165,D_163)))
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(C_161,D_163)))
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_162)))
      | ~ v1_funct_1(E_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_873,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_836])).

tff(c_895,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_873])).

tff(c_897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_720,c_895])).

tff(c_898,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_1727,plain,(
    ! [D_237,A_238,B_239,C_240] :
      ( v2_funct_2(D_237,A_238)
      | ~ r2_relset_1(A_238,A_238,k1_partfun1(A_238,B_239,B_239,A_238,C_240,D_237),k6_partfun1(A_238))
      | ~ m1_subset_1(D_237,k1_zfmisc_1(k2_zfmisc_1(B_239,A_238)))
      | ~ v1_funct_2(D_237,B_239,A_238)
      | ~ v1_funct_1(D_237)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ v1_funct_2(C_240,A_238,B_239)
      | ~ v1_funct_1(C_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1733,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_898,c_1727])).

tff(c_1737,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_488,c_1733])).

tff(c_1739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_1737])).

tff(c_1740,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_135,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_123])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_148,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_137])).

tff(c_181,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_172])).

tff(c_190,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_181])).

tff(c_1752,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [A_1] : k1_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1912,plain,(
    ! [B_278,C_279,A_280] :
      ( k6_partfun1(B_278) = k5_relat_1(k2_funct_1(C_279),C_279)
      | k1_xboole_0 = B_278
      | ~ v2_funct_1(C_279)
      | k2_relset_1(A_280,B_278,C_279) != B_278
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_280,B_278)))
      | ~ v1_funct_2(C_279,A_280,B_278)
      | ~ v1_funct_1(C_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1916,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1912])).

tff(c_1924,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_68,c_64,c_1916])).

tff(c_1925,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1924])).

tff(c_10,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_relat_1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_partfun1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10])).

tff(c_1935,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1925,c_84])).

tff(c_1945,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_80,c_64,c_1935])).

tff(c_1980,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1945,c_88])).

tff(c_1997,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1980])).

tff(c_28,plain,(
    ! [B_19] :
      ( v2_funct_2(B_19,k2_relat_1(B_19))
      | ~ v5_relat_1(B_19,k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2008,plain,
    ( v2_funct_2('#skF_3',k2_relat_1('#skF_3'))
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1997,c_28])).

tff(c_2014,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_148,c_1997,c_2008])).

tff(c_2016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1752,c_2014])).

tff(c_2017,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_14,plain,(
    ! [A_4,B_6] :
      ( k2_funct_1(A_4) = B_6
      | k6_relat_1(k2_relat_1(A_4)) != k5_relat_1(B_6,A_4)
      | k2_relat_1(B_6) != k1_relat_1(A_4)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2636,plain,(
    ! [A_373,B_374] :
      ( k2_funct_1(A_373) = B_374
      | k6_partfun1(k2_relat_1(A_373)) != k5_relat_1(B_374,A_373)
      | k2_relat_1(B_374) != k1_relat_1(A_373)
      | ~ v2_funct_1(A_373)
      | ~ v1_funct_1(B_374)
      | ~ v1_relat_1(B_374)
      | ~ v1_funct_1(A_373)
      | ~ v1_relat_1(A_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14])).

tff(c_2642,plain,(
    ! [B_374] :
      ( k2_funct_1('#skF_3') = B_374
      | k5_relat_1(B_374,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_374) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_374)
      | ~ v1_relat_1(B_374)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2017,c_2636])).

tff(c_2655,plain,(
    ! [B_375] :
      ( k2_funct_1('#skF_3') = B_375
      | k5_relat_1(B_375,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_375) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_375)
      | ~ v1_relat_1(B_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_80,c_64,c_2642])).

tff(c_2658,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_2655])).

tff(c_2667,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1740,c_2658])).

tff(c_2668,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2667])).

tff(c_2674,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2668])).

tff(c_2777,plain,(
    ! [A_401,C_402,B_403] :
      ( k6_partfun1(A_401) = k5_relat_1(C_402,k2_funct_1(C_402))
      | k1_xboole_0 = B_403
      | ~ v2_funct_1(C_402)
      | k2_relset_1(A_401,B_403,C_402) != B_403
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(A_401,B_403)))
      | ~ v1_funct_2(C_402,A_401,B_403)
      | ~ v1_funct_1(C_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_2781,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2777])).

tff(c_2789,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_68,c_64,c_2781])).

tff(c_2790,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2789])).

tff(c_12,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12])).

tff(c_2798,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2790,c_83])).

tff(c_2805,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_80,c_64,c_2798])).

tff(c_2841,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2805,c_88])).

tff(c_2862,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2841])).

tff(c_2864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2674,c_2862])).

tff(c_2865,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2668])).

tff(c_2400,plain,(
    ! [C_345,F_344,A_343,E_346,D_341,B_342] :
      ( k1_partfun1(A_343,B_342,C_345,D_341,E_346,F_344) = k5_relat_1(E_346,F_344)
      | ~ m1_subset_1(F_344,k1_zfmisc_1(k2_zfmisc_1(C_345,D_341)))
      | ~ v1_funct_1(F_344)
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_343,B_342)))
      | ~ v1_funct_1(E_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2406,plain,(
    ! [A_343,B_342,E_346] :
      ( k1_partfun1(A_343,B_342,'#skF_2','#skF_1',E_346,'#skF_4') = k5_relat_1(E_346,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_343,B_342)))
      | ~ v1_funct_1(E_346) ) ),
    inference(resolution,[status(thm)],[c_70,c_2400])).

tff(c_2442,plain,(
    ! [A_351,B_352,E_353] :
      ( k1_partfun1(A_351,B_352,'#skF_2','#skF_1',E_353,'#skF_4') = k5_relat_1(E_353,'#skF_4')
      | ~ m1_subset_1(E_353,k1_zfmisc_1(k2_zfmisc_1(A_351,B_352)))
      | ~ v1_funct_1(E_353) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2406])).

tff(c_2448,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_2442])).

tff(c_2455,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2448])).

tff(c_2058,plain,(
    ! [D_287,C_288,A_289,B_290] :
      ( D_287 = C_288
      | ~ r2_relset_1(A_289,B_290,C_288,D_287)
      | ~ m1_subset_1(D_287,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2066,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_2058])).

tff(c_2081,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_2066])).

tff(c_2082,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2081])).

tff(c_2460,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_2082])).

tff(c_2562,plain,(
    ! [E_370,C_367,B_368,F_372,A_371,D_369] :
      ( m1_subset_1(k1_partfun1(A_371,B_368,C_367,D_369,E_370,F_372),k1_zfmisc_1(k2_zfmisc_1(A_371,D_369)))
      | ~ m1_subset_1(F_372,k1_zfmisc_1(k2_zfmisc_1(C_367,D_369)))
      | ~ v1_funct_1(F_372)
      | ~ m1_subset_1(E_370,k1_zfmisc_1(k2_zfmisc_1(A_371,B_368)))
      | ~ v1_funct_1(E_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2601,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2455,c_2562])).

tff(c_2624,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_2601])).

tff(c_2626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2460,c_2624])).

tff(c_2627,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2081])).

tff(c_2950,plain,(
    ! [C_423,B_420,E_424,A_421,D_419,F_422] :
      ( k1_partfun1(A_421,B_420,C_423,D_419,E_424,F_422) = k5_relat_1(E_424,F_422)
      | ~ m1_subset_1(F_422,k1_zfmisc_1(k2_zfmisc_1(C_423,D_419)))
      | ~ v1_funct_1(F_422)
      | ~ m1_subset_1(E_424,k1_zfmisc_1(k2_zfmisc_1(A_421,B_420)))
      | ~ v1_funct_1(E_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2956,plain,(
    ! [A_421,B_420,E_424] :
      ( k1_partfun1(A_421,B_420,'#skF_2','#skF_1',E_424,'#skF_4') = k5_relat_1(E_424,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_424,k1_zfmisc_1(k2_zfmisc_1(A_421,B_420)))
      | ~ v1_funct_1(E_424) ) ),
    inference(resolution,[status(thm)],[c_70,c_2950])).

tff(c_4349,plain,(
    ! [A_514,B_515,E_516] :
      ( k1_partfun1(A_514,B_515,'#skF_2','#skF_1',E_516,'#skF_4') = k5_relat_1(E_516,'#skF_4')
      | ~ m1_subset_1(E_516,k1_zfmisc_1(k2_zfmisc_1(A_514,B_515)))
      | ~ v1_funct_1(E_516) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2956])).

tff(c_4355,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4349])).

tff(c_4362,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2627,c_4355])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_3005,plain,(
    ! [A_430,C_431,B_432] :
      ( k6_partfun1(A_430) = k5_relat_1(C_431,k2_funct_1(C_431))
      | k1_xboole_0 = B_432
      | ~ v2_funct_1(C_431)
      | k2_relset_1(A_430,B_432,C_431) != B_432
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_430,B_432)))
      | ~ v1_funct_2(C_431,A_430,B_432)
      | ~ v1_funct_1(C_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_3011,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3005])).

tff(c_3021,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_3011])).

tff(c_3022,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3021])).

tff(c_3037,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3022])).

tff(c_2029,plain,(
    ! [A_281,B_282,D_283] :
      ( r2_relset_1(A_281,B_282,D_283,D_283)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2036,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_81,c_2029])).

tff(c_3656,plain,(
    ! [A_472,B_473,C_474,D_475] :
      ( k2_relset_1(A_472,B_473,C_474) = B_473
      | ~ r2_relset_1(B_473,B_473,k1_partfun1(B_473,A_472,A_472,B_473,D_475,C_474),k6_partfun1(B_473))
      | ~ m1_subset_1(D_475,k1_zfmisc_1(k2_zfmisc_1(B_473,A_472)))
      | ~ v1_funct_2(D_475,B_473,A_472)
      | ~ v1_funct_1(D_475)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(A_472,B_473)))
      | ~ v1_funct_2(C_474,A_472,B_473)
      | ~ v1_funct_1(C_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3662,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2627,c_3656])).

tff(c_3666,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_2036,c_3662])).

tff(c_3668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3037,c_3666])).

tff(c_3669,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3022])).

tff(c_3675,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3669])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_4263,plain,(
    ! [D_511,C_510,E_509,B_513,A_512] :
      ( k1_xboole_0 = C_510
      | v2_funct_1(E_509)
      | k2_relset_1(A_512,B_513,D_511) != B_513
      | ~ v2_funct_1(k1_partfun1(A_512,B_513,B_513,C_510,D_511,E_509))
      | ~ m1_subset_1(E_509,k1_zfmisc_1(k2_zfmisc_1(B_513,C_510)))
      | ~ v1_funct_2(E_509,B_513,C_510)
      | ~ v1_funct_1(E_509)
      | ~ m1_subset_1(D_511,k1_zfmisc_1(k2_zfmisc_1(A_512,B_513)))
      | ~ v1_funct_2(D_511,A_512,B_513)
      | ~ v1_funct_1(D_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_4269,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2627,c_4263])).

tff(c_4277,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_85,c_68,c_4269])).

tff(c_4279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3675,c_62,c_4277])).

tff(c_4281,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3669])).

tff(c_4280,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3669])).

tff(c_4285,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4280,c_83])).

tff(c_4292,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_74,c_4281,c_4285])).

tff(c_4328,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4292,c_88])).

tff(c_4344,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_4328])).

tff(c_2644,plain,(
    ! [B_374] :
      ( k2_funct_1('#skF_4') = B_374
      | k5_relat_1(B_374,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_374) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_374)
      | ~ v1_relat_1(B_374)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1740,c_2636])).

tff(c_2652,plain,(
    ! [B_374] :
      ( k2_funct_1('#skF_4') = B_374
      | k5_relat_1(B_374,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_374) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_374)
      | ~ v1_relat_1(B_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_74,c_2644])).

tff(c_12783,plain,(
    ! [B_807] :
      ( k2_funct_1('#skF_4') = B_807
      | k5_relat_1(B_807,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_807) != '#skF_2'
      | ~ v1_funct_1(B_807)
      | ~ v1_relat_1(B_807) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4281,c_4344,c_2652])).

tff(c_12981,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_12783])).

tff(c_13156,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2017,c_4362,c_12981])).

tff(c_13161,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13156,c_4280])).

tff(c_13164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2865,c_13161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n022.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 09:15:41 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.62  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.56/5.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.56/5.77  
% 11.56/5.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.56/5.77  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.56/5.77  
% 11.56/5.77  %Foreground sorts:
% 11.56/5.77  
% 11.56/5.77  
% 11.56/5.77  %Background operators:
% 11.56/5.77  
% 11.56/5.77  
% 11.56/5.77  %Foreground operators:
% 11.56/5.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.56/5.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.56/5.77  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.56/5.77  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.56/5.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.56/5.77  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.56/5.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.56/5.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.56/5.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.56/5.77  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.56/5.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.56/5.77  tff('#skF_2', type, '#skF_2': $i).
% 11.56/5.77  tff('#skF_3', type, '#skF_3': $i).
% 11.56/5.77  tff('#skF_1', type, '#skF_1': $i).
% 11.56/5.77  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 11.56/5.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.56/5.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.56/5.77  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.56/5.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.56/5.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.56/5.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.56/5.77  tff('#skF_4', type, '#skF_4': $i).
% 11.56/5.77  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.56/5.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.56/5.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.56/5.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.56/5.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.56/5.77  
% 11.56/5.80  tff(f_216, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 11.56/5.80  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.56/5.80  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.56/5.80  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 11.56/5.80  tff(f_112, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.56/5.80  tff(f_80, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 11.56/5.80  tff(f_78, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.56/5.80  tff(f_110, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.56/5.80  tff(f_100, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.56/5.80  tff(f_148, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 11.56/5.80  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.56/5.80  tff(f_190, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 11.56/5.80  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 11.56/5.80  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 11.56/5.80  tff(f_129, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 11.56/5.80  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 11.56/5.80  tff(f_174, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 11.56/5.80  tff(c_58, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_123, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.56/5.80  tff(c_136, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_123])).
% 11.56/5.80  tff(c_137, plain, (![C_62, B_63, A_64]: (v5_relat_1(C_62, B_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.56/5.80  tff(c_149, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_137])).
% 11.56/5.80  tff(c_172, plain, (![B_72, A_73]: (k2_relat_1(B_72)=A_73 | ~v2_funct_2(B_72, A_73) | ~v5_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.56/5.80  tff(c_178, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_149, c_172])).
% 11.56/5.80  tff(c_187, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_178])).
% 11.56/5.80  tff(c_191, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_187])).
% 11.56/5.80  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_38, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.56/5.80  tff(c_26, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.56/5.80  tff(c_81, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_26])).
% 11.56/5.80  tff(c_481, plain, (![A_114, B_115, D_116]: (r2_relset_1(A_114, B_115, D_116, D_116) | ~m1_subset_1(D_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.56/5.80  tff(c_488, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_81, c_481])).
% 11.56/5.80  tff(c_620, plain, (![C_144, E_145, A_142, F_143, B_141, D_140]: (k1_partfun1(A_142, B_141, C_144, D_140, E_145, F_143)=k5_relat_1(E_145, F_143) | ~m1_subset_1(F_143, k1_zfmisc_1(k2_zfmisc_1(C_144, D_140))) | ~v1_funct_1(F_143) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))) | ~v1_funct_1(E_145))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.56/5.80  tff(c_626, plain, (![A_142, B_141, E_145]: (k1_partfun1(A_142, B_141, '#skF_2', '#skF_1', E_145, '#skF_4')=k5_relat_1(E_145, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))) | ~v1_funct_1(E_145))), inference(resolution, [status(thm)], [c_70, c_620])).
% 11.56/5.80  tff(c_665, plain, (![A_152, B_153, E_154]: (k1_partfun1(A_152, B_153, '#skF_2', '#skF_1', E_154, '#skF_4')=k5_relat_1(E_154, '#skF_4') | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_1(E_154))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_626])).
% 11.56/5.80  tff(c_671, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_665])).
% 11.56/5.80  tff(c_678, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_671])).
% 11.56/5.80  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_510, plain, (![D_120, C_121, A_122, B_123]: (D_120=C_121 | ~r2_relset_1(A_122, B_123, C_121, D_120) | ~m1_subset_1(D_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.56/5.80  tff(c_518, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_510])).
% 11.56/5.80  tff(c_533, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_518])).
% 11.56/5.80  tff(c_534, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_533])).
% 11.56/5.80  tff(c_720, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_678, c_534])).
% 11.56/5.80  tff(c_836, plain, (![C_161, F_166, A_165, E_164, D_163, B_162]: (m1_subset_1(k1_partfun1(A_165, B_162, C_161, D_163, E_164, F_166), k1_zfmisc_1(k2_zfmisc_1(A_165, D_163))) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(C_161, D_163))) | ~v1_funct_1(F_166) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_162))) | ~v1_funct_1(E_164))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.56/5.80  tff(c_873, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_678, c_836])).
% 11.56/5.80  tff(c_895, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_873])).
% 11.56/5.80  tff(c_897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_720, c_895])).
% 11.56/5.80  tff(c_898, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_533])).
% 11.56/5.80  tff(c_1727, plain, (![D_237, A_238, B_239, C_240]: (v2_funct_2(D_237, A_238) | ~r2_relset_1(A_238, A_238, k1_partfun1(A_238, B_239, B_239, A_238, C_240, D_237), k6_partfun1(A_238)) | ~m1_subset_1(D_237, k1_zfmisc_1(k2_zfmisc_1(B_239, A_238))) | ~v1_funct_2(D_237, B_239, A_238) | ~v1_funct_1(D_237) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~v1_funct_2(C_240, A_238, B_239) | ~v1_funct_1(C_240))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.56/5.80  tff(c_1733, plain, (v2_funct_2('#skF_4', '#skF_1') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_898, c_1727])).
% 11.56/5.80  tff(c_1737, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_488, c_1733])).
% 11.56/5.80  tff(c_1739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_1737])).
% 11.56/5.80  tff(c_1740, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_187])).
% 11.56/5.80  tff(c_135, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_123])).
% 11.56/5.80  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_148, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_137])).
% 11.56/5.80  tff(c_181, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_148, c_172])).
% 11.56/5.80  tff(c_190, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_181])).
% 11.56/5.80  tff(c_1752, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_190])).
% 11.56/5.80  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.56/5.80  tff(c_88, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2])).
% 11.56/5.80  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_1912, plain, (![B_278, C_279, A_280]: (k6_partfun1(B_278)=k5_relat_1(k2_funct_1(C_279), C_279) | k1_xboole_0=B_278 | ~v2_funct_1(C_279) | k2_relset_1(A_280, B_278, C_279)!=B_278 | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_280, B_278))) | ~v1_funct_2(C_279, A_280, B_278) | ~v1_funct_1(C_279))), inference(cnfTransformation, [status(thm)], [f_190])).
% 11.56/5.80  tff(c_1916, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1912])).
% 11.56/5.80  tff(c_1924, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_68, c_64, c_1916])).
% 11.56/5.80  tff(c_1925, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_1924])).
% 11.56/5.80  tff(c_10, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_relat_1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.56/5.80  tff(c_84, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_partfun1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_10])).
% 11.56/5.80  tff(c_1935, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1925, c_84])).
% 11.56/5.80  tff(c_1945, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_80, c_64, c_1935])).
% 11.56/5.80  tff(c_1980, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1945, c_88])).
% 11.56/5.80  tff(c_1997, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1980])).
% 11.56/5.80  tff(c_28, plain, (![B_19]: (v2_funct_2(B_19, k2_relat_1(B_19)) | ~v5_relat_1(B_19, k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.56/5.80  tff(c_2008, plain, (v2_funct_2('#skF_3', k2_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1997, c_28])).
% 11.56/5.80  tff(c_2014, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_148, c_1997, c_2008])).
% 11.56/5.80  tff(c_2016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1752, c_2014])).
% 11.56/5.80  tff(c_2017, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_190])).
% 11.56/5.80  tff(c_14, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_relat_1(k2_relat_1(A_4))!=k5_relat_1(B_6, A_4) | k2_relat_1(B_6)!=k1_relat_1(A_4) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.56/5.80  tff(c_2636, plain, (![A_373, B_374]: (k2_funct_1(A_373)=B_374 | k6_partfun1(k2_relat_1(A_373))!=k5_relat_1(B_374, A_373) | k2_relat_1(B_374)!=k1_relat_1(A_373) | ~v2_funct_1(A_373) | ~v1_funct_1(B_374) | ~v1_relat_1(B_374) | ~v1_funct_1(A_373) | ~v1_relat_1(A_373))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14])).
% 11.56/5.80  tff(c_2642, plain, (![B_374]: (k2_funct_1('#skF_3')=B_374 | k5_relat_1(B_374, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_374)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_374) | ~v1_relat_1(B_374) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2017, c_2636])).
% 11.56/5.80  tff(c_2655, plain, (![B_375]: (k2_funct_1('#skF_3')=B_375 | k5_relat_1(B_375, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_375)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_375) | ~v1_relat_1(B_375))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_80, c_64, c_2642])).
% 11.56/5.80  tff(c_2658, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_136, c_2655])).
% 11.56/5.80  tff(c_2667, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1740, c_2658])).
% 11.56/5.80  tff(c_2668, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_2667])).
% 11.56/5.80  tff(c_2674, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2668])).
% 11.56/5.80  tff(c_2777, plain, (![A_401, C_402, B_403]: (k6_partfun1(A_401)=k5_relat_1(C_402, k2_funct_1(C_402)) | k1_xboole_0=B_403 | ~v2_funct_1(C_402) | k2_relset_1(A_401, B_403, C_402)!=B_403 | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(A_401, B_403))) | ~v1_funct_2(C_402, A_401, B_403) | ~v1_funct_1(C_402))), inference(cnfTransformation, [status(thm)], [f_190])).
% 11.56/5.80  tff(c_2781, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2777])).
% 11.56/5.80  tff(c_2789, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_68, c_64, c_2781])).
% 11.56/5.80  tff(c_2790, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_2789])).
% 11.56/5.80  tff(c_12, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.56/5.80  tff(c_83, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12])).
% 11.56/5.80  tff(c_2798, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2790, c_83])).
% 11.56/5.80  tff(c_2805, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_80, c_64, c_2798])).
% 11.56/5.80  tff(c_2841, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2805, c_88])).
% 11.56/5.80  tff(c_2862, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2841])).
% 11.56/5.80  tff(c_2864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2674, c_2862])).
% 11.56/5.80  tff(c_2865, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2668])).
% 11.56/5.80  tff(c_2400, plain, (![C_345, F_344, A_343, E_346, D_341, B_342]: (k1_partfun1(A_343, B_342, C_345, D_341, E_346, F_344)=k5_relat_1(E_346, F_344) | ~m1_subset_1(F_344, k1_zfmisc_1(k2_zfmisc_1(C_345, D_341))) | ~v1_funct_1(F_344) | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_343, B_342))) | ~v1_funct_1(E_346))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.56/5.80  tff(c_2406, plain, (![A_343, B_342, E_346]: (k1_partfun1(A_343, B_342, '#skF_2', '#skF_1', E_346, '#skF_4')=k5_relat_1(E_346, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_343, B_342))) | ~v1_funct_1(E_346))), inference(resolution, [status(thm)], [c_70, c_2400])).
% 11.56/5.80  tff(c_2442, plain, (![A_351, B_352, E_353]: (k1_partfun1(A_351, B_352, '#skF_2', '#skF_1', E_353, '#skF_4')=k5_relat_1(E_353, '#skF_4') | ~m1_subset_1(E_353, k1_zfmisc_1(k2_zfmisc_1(A_351, B_352))) | ~v1_funct_1(E_353))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2406])).
% 11.56/5.80  tff(c_2448, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_2442])).
% 11.56/5.80  tff(c_2455, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2448])).
% 11.56/5.80  tff(c_2058, plain, (![D_287, C_288, A_289, B_290]: (D_287=C_288 | ~r2_relset_1(A_289, B_290, C_288, D_287) | ~m1_subset_1(D_287, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.56/5.80  tff(c_2066, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_2058])).
% 11.56/5.80  tff(c_2081, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_2066])).
% 11.56/5.80  tff(c_2082, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2081])).
% 11.56/5.80  tff(c_2460, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_2082])).
% 11.56/5.80  tff(c_2562, plain, (![E_370, C_367, B_368, F_372, A_371, D_369]: (m1_subset_1(k1_partfun1(A_371, B_368, C_367, D_369, E_370, F_372), k1_zfmisc_1(k2_zfmisc_1(A_371, D_369))) | ~m1_subset_1(F_372, k1_zfmisc_1(k2_zfmisc_1(C_367, D_369))) | ~v1_funct_1(F_372) | ~m1_subset_1(E_370, k1_zfmisc_1(k2_zfmisc_1(A_371, B_368))) | ~v1_funct_1(E_370))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.56/5.80  tff(c_2601, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2455, c_2562])).
% 11.56/5.80  tff(c_2624, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_2601])).
% 11.56/5.80  tff(c_2626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2460, c_2624])).
% 11.56/5.80  tff(c_2627, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2081])).
% 11.56/5.80  tff(c_2950, plain, (![C_423, B_420, E_424, A_421, D_419, F_422]: (k1_partfun1(A_421, B_420, C_423, D_419, E_424, F_422)=k5_relat_1(E_424, F_422) | ~m1_subset_1(F_422, k1_zfmisc_1(k2_zfmisc_1(C_423, D_419))) | ~v1_funct_1(F_422) | ~m1_subset_1(E_424, k1_zfmisc_1(k2_zfmisc_1(A_421, B_420))) | ~v1_funct_1(E_424))), inference(cnfTransformation, [status(thm)], [f_110])).
% 11.56/5.80  tff(c_2956, plain, (![A_421, B_420, E_424]: (k1_partfun1(A_421, B_420, '#skF_2', '#skF_1', E_424, '#skF_4')=k5_relat_1(E_424, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_424, k1_zfmisc_1(k2_zfmisc_1(A_421, B_420))) | ~v1_funct_1(E_424))), inference(resolution, [status(thm)], [c_70, c_2950])).
% 11.56/5.80  tff(c_4349, plain, (![A_514, B_515, E_516]: (k1_partfun1(A_514, B_515, '#skF_2', '#skF_1', E_516, '#skF_4')=k5_relat_1(E_516, '#skF_4') | ~m1_subset_1(E_516, k1_zfmisc_1(k2_zfmisc_1(A_514, B_515))) | ~v1_funct_1(E_516))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2956])).
% 11.56/5.80  tff(c_4355, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4349])).
% 11.56/5.80  tff(c_4362, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2627, c_4355])).
% 11.56/5.80  tff(c_62, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_216])).
% 11.56/5.80  tff(c_3005, plain, (![A_430, C_431, B_432]: (k6_partfun1(A_430)=k5_relat_1(C_431, k2_funct_1(C_431)) | k1_xboole_0=B_432 | ~v2_funct_1(C_431) | k2_relset_1(A_430, B_432, C_431)!=B_432 | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_430, B_432))) | ~v1_funct_2(C_431, A_430, B_432) | ~v1_funct_1(C_431))), inference(cnfTransformation, [status(thm)], [f_190])).
% 11.56/5.80  tff(c_3011, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3005])).
% 11.56/5.80  tff(c_3021, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_3011])).
% 11.56/5.80  tff(c_3022, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_3021])).
% 11.56/5.80  tff(c_3037, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3022])).
% 11.56/5.80  tff(c_2029, plain, (![A_281, B_282, D_283]: (r2_relset_1(A_281, B_282, D_283, D_283) | ~m1_subset_1(D_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.56/5.80  tff(c_2036, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_81, c_2029])).
% 11.56/5.80  tff(c_3656, plain, (![A_472, B_473, C_474, D_475]: (k2_relset_1(A_472, B_473, C_474)=B_473 | ~r2_relset_1(B_473, B_473, k1_partfun1(B_473, A_472, A_472, B_473, D_475, C_474), k6_partfun1(B_473)) | ~m1_subset_1(D_475, k1_zfmisc_1(k2_zfmisc_1(B_473, A_472))) | ~v1_funct_2(D_475, B_473, A_472) | ~v1_funct_1(D_475) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(A_472, B_473))) | ~v1_funct_2(C_474, A_472, B_473) | ~v1_funct_1(C_474))), inference(cnfTransformation, [status(thm)], [f_129])).
% 11.56/5.80  tff(c_3662, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2627, c_3656])).
% 11.56/5.80  tff(c_3666, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_2036, c_3662])).
% 11.56/5.80  tff(c_3668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3037, c_3666])).
% 11.56/5.80  tff(c_3669, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3022])).
% 11.56/5.80  tff(c_3675, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3669])).
% 11.56/5.80  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.56/5.80  tff(c_85, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8])).
% 11.56/5.80  tff(c_4263, plain, (![D_511, C_510, E_509, B_513, A_512]: (k1_xboole_0=C_510 | v2_funct_1(E_509) | k2_relset_1(A_512, B_513, D_511)!=B_513 | ~v2_funct_1(k1_partfun1(A_512, B_513, B_513, C_510, D_511, E_509)) | ~m1_subset_1(E_509, k1_zfmisc_1(k2_zfmisc_1(B_513, C_510))) | ~v1_funct_2(E_509, B_513, C_510) | ~v1_funct_1(E_509) | ~m1_subset_1(D_511, k1_zfmisc_1(k2_zfmisc_1(A_512, B_513))) | ~v1_funct_2(D_511, A_512, B_513) | ~v1_funct_1(D_511))), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.56/5.80  tff(c_4269, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2627, c_4263])).
% 11.56/5.80  tff(c_4277, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_85, c_68, c_4269])).
% 11.56/5.80  tff(c_4279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3675, c_62, c_4277])).
% 11.56/5.80  tff(c_4281, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3669])).
% 11.56/5.80  tff(c_4280, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3669])).
% 11.56/5.80  tff(c_4285, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4280, c_83])).
% 11.56/5.80  tff(c_4292, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_74, c_4281, c_4285])).
% 11.56/5.80  tff(c_4328, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4292, c_88])).
% 11.56/5.80  tff(c_4344, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_4328])).
% 11.56/5.80  tff(c_2644, plain, (![B_374]: (k2_funct_1('#skF_4')=B_374 | k5_relat_1(B_374, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_374)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_374) | ~v1_relat_1(B_374) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1740, c_2636])).
% 11.56/5.80  tff(c_2652, plain, (![B_374]: (k2_funct_1('#skF_4')=B_374 | k5_relat_1(B_374, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_374)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_374) | ~v1_relat_1(B_374))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_74, c_2644])).
% 11.56/5.80  tff(c_12783, plain, (![B_807]: (k2_funct_1('#skF_4')=B_807 | k5_relat_1(B_807, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_807)!='#skF_2' | ~v1_funct_1(B_807) | ~v1_relat_1(B_807))), inference(demodulation, [status(thm), theory('equality')], [c_4281, c_4344, c_2652])).
% 11.56/5.80  tff(c_12981, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_12783])).
% 11.56/5.80  tff(c_13156, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2017, c_4362, c_12981])).
% 11.56/5.80  tff(c_13161, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13156, c_4280])).
% 11.56/5.80  tff(c_13164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2865, c_13161])).
% 11.56/5.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.56/5.80  
% 11.56/5.80  Inference rules
% 11.56/5.80  ----------------------
% 11.56/5.80  #Ref     : 0
% 11.56/5.80  #Sup     : 2639
% 11.56/5.80  #Fact    : 0
% 11.56/5.80  #Define  : 0
% 11.56/5.80  #Split   : 75
% 11.56/5.80  #Chain   : 0
% 11.56/5.80  #Close   : 0
% 11.56/5.80  
% 11.56/5.80  Ordering : KBO
% 11.56/5.80  
% 11.56/5.80  Simplification rules
% 11.56/5.80  ----------------------
% 11.56/5.80  #Subsume      : 209
% 11.56/5.80  #Demod        : 6438
% 11.56/5.80  #Tautology    : 470
% 11.56/5.80  #SimpNegUnit  : 309
% 11.56/5.80  #BackRed      : 72
% 11.56/5.80  
% 11.56/5.80  #Partial instantiations: 0
% 11.56/5.80  #Strategies tried      : 1
% 11.56/5.80  
% 11.56/5.80  Timing (in seconds)
% 11.56/5.80  ----------------------
% 11.83/5.83  Preprocessing        : 0.39
% 11.83/5.83  Parsing              : 0.19
% 11.83/5.83  CNF conversion       : 0.02
% 11.83/5.83  Main loop            : 3.92
% 11.83/5.83  Inferencing          : 0.91
% 11.83/5.83  Reduction            : 2.09
% 11.83/5.83  Demodulation         : 1.73
% 11.83/5.83  BG Simplification    : 0.08
% 11.83/5.83  Subsumption          : 0.65
% 11.83/5.83  Abstraction          : 0.12
% 11.83/5.83  MUC search           : 0.00
% 11.83/5.83  Cooper               : 0.00
% 11.83/5.83  Total                : 4.36
% 11.83/5.83  Index Insertion      : 0.00
% 11.83/5.83  Index Deletion       : 0.00
% 11.83/5.83  Index Matching       : 0.00
% 11.83/5.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
