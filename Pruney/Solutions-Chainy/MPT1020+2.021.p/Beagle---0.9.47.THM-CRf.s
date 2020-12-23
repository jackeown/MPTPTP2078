%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:53 EST 2020

% Result     : Theorem 6.37s
% Output     : CNFRefutation 6.37s
% Verified   : 
% Statistics : Number of formulae       :  177 (1843 expanded)
%              Number of leaves         :   46 ( 610 expanded)
%              Depth                    :   15
%              Number of atoms          :  312 (5285 expanded)
%              Number of equality atoms :   84 (1316 expanded)
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_105,axiom,(
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

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_121,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_106,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_106])).

tff(c_4562,plain,(
    ! [C_280,B_281,A_282] :
      ( v1_xboole_0(C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(B_281,A_282)))
      | ~ v1_xboole_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4573,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_4562])).

tff(c_4576,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4573])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_118,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_106])).

tff(c_917,plain,(
    ! [A_123,B_124,D_125] :
      ( r2_relset_1(A_123,B_124,D_125,D_125)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_925,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_917])).

tff(c_145,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_157,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_145])).

tff(c_245,plain,(
    ! [B_75,A_76] :
      ( k2_relat_1(B_75) = A_76
      | ~ v2_funct_2(B_75,A_76)
      | ~ v5_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_251,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_157,c_245])).

tff(c_260,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_251])).

tff(c_274,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_72,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_68,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_634,plain,(
    ! [C_103,B_104,A_105] :
      ( v2_funct_2(C_103,B_104)
      | ~ v3_funct_2(C_103,A_105,B_104)
      | ~ v1_funct_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_646,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_634])).

tff(c_656,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_646])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_656])).

tff(c_659,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_6,plain,(
    ! [A_3] :
      ( k2_relat_1(A_3) != k1_xboole_0
      | k1_xboole_0 = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_118,c_6])).

tff(c_144,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_661,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_144])).

tff(c_70,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_937,plain,(
    ! [A_127,B_128,C_129] :
      ( k2_relset_1(A_127,B_128,C_129) = k2_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_946,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_937])).

tff(c_951,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_946])).

tff(c_42,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_924,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_42,c_917])).

tff(c_1004,plain,(
    ! [C_131,A_132,B_133] :
      ( v2_funct_1(C_131)
      | ~ v3_funct_2(C_131,A_132,B_133)
      | ~ v1_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1016,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1004])).

tff(c_1024,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1016])).

tff(c_1714,plain,(
    ! [B_180,A_181,C_177,D_178,F_176,E_179] :
      ( m1_subset_1(k1_partfun1(A_181,B_180,C_177,D_178,E_179,F_176),k1_zfmisc_1(k2_zfmisc_1(A_181,D_178)))
      | ~ m1_subset_1(F_176,k1_zfmisc_1(k2_zfmisc_1(C_177,D_178)))
      | ~ v1_funct_1(F_176)
      | ~ m1_subset_1(E_179,k1_zfmisc_1(k2_zfmisc_1(A_181,B_180)))
      | ~ v1_funct_1(E_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1084,plain,(
    ! [D_140,C_141,A_142,B_143] :
      ( D_140 = C_141
      | ~ r2_relset_1(A_142,B_143,C_141,D_140)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1094,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_1084])).

tff(c_1113,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1094])).

tff(c_1145,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1113])).

tff(c_1722,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1714,c_1145])).

tff(c_1755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_64,c_58,c_1722])).

tff(c_1756,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1113])).

tff(c_4330,plain,(
    ! [C_252,D_253,B_254,A_255] :
      ( k2_funct_1(C_252) = D_253
      | k1_xboole_0 = B_254
      | k1_xboole_0 = A_255
      | ~ v2_funct_1(C_252)
      | ~ r2_relset_1(A_255,A_255,k1_partfun1(A_255,B_254,B_254,A_255,C_252,D_253),k6_partfun1(A_255))
      | k2_relset_1(A_255,B_254,C_252) != B_254
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1(B_254,A_255)))
      | ~ v1_funct_2(D_253,B_254,A_255)
      | ~ v1_funct_1(D_253)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_255,B_254)))
      | ~ v1_funct_2(C_252,A_255,B_254)
      | ~ v1_funct_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_4351,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_4330])).

tff(c_4359,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_58,c_951,c_924,c_1024,c_4351])).

tff(c_4360,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_661,c_4359])).

tff(c_1861,plain,(
    ! [A_189,B_190] :
      ( k2_funct_2(A_189,B_190) = k2_funct_1(B_190)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v3_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1876,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1861])).

tff(c_1888,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1876])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1893,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_54])).

tff(c_4362,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4360,c_1893])).

tff(c_4366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_4362])).

tff(c_4367,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_4368,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_4381,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_4368])).

tff(c_4444,plain,(
    ! [C_265,B_266,A_267] :
      ( v5_relat_1(C_265,B_266)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_267,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4456,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_4444])).

tff(c_4577,plain,(
    ! [B_283,A_284] :
      ( k2_relat_1(B_283) = A_284
      | ~ v2_funct_2(B_283,A_284)
      | ~ v5_relat_1(B_283,A_284)
      | ~ v1_relat_1(B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4586,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4456,c_4577])).

tff(c_4598,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_4381,c_4586])).

tff(c_4610,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4598])).

tff(c_5040,plain,(
    ! [C_314,B_315,A_316] :
      ( v2_funct_2(C_314,B_315)
      | ~ v3_funct_2(C_314,A_316,B_315)
      | ~ v1_funct_1(C_314)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_316,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5052,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_5040])).

tff(c_5062,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_5052])).

tff(c_5064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4610,c_5062])).

tff(c_5065,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4598])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4372,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_2])).

tff(c_5079,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5065,c_4372])).

tff(c_5089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4576,c_5079])).

tff(c_5091,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4573])).

tff(c_93,plain,(
    ! [B_51,A_52] :
      ( ~ v1_xboole_0(B_51)
      | B_51 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_2,c_93])).

tff(c_4371,plain,(
    ! [A_52] :
      ( A_52 = '#skF_2'
      | ~ v1_xboole_0(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_96])).

tff(c_5104,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5091,c_4371])).

tff(c_5090,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4573])).

tff(c_5097,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5090,c_4371])).

tff(c_5139,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5104,c_5097])).

tff(c_5117,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5097,c_5097,c_4381])).

tff(c_5172,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5139,c_5139,c_5117])).

tff(c_126,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_117,c_6])).

tff(c_4392,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4367,c_4367,c_126])).

tff(c_4393,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4392])).

tff(c_5115,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5097,c_4393])).

tff(c_5184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5172,c_5139,c_5139,c_5115])).

tff(c_5185,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4392])).

tff(c_5201,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5185,c_5185,c_4381])).

tff(c_5241,plain,(
    ! [C_325,B_326,A_327] :
      ( v5_relat_1(C_325,B_326)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_327,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5249,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_5241])).

tff(c_5483,plain,(
    ! [B_347,A_348] :
      ( k2_relat_1(B_347) = A_348
      | ~ v2_funct_2(B_347,A_348)
      | ~ v5_relat_1(B_347,A_348)
      | ~ v1_relat_1(B_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5495,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5249,c_5483])).

tff(c_5507,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_5201,c_5495])).

tff(c_5508,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5507])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_5598,plain,(
    ! [C_363,B_364,A_365] :
      ( v2_funct_2(C_363,B_364)
      | ~ v3_funct_2(C_363,A_365,B_364)
      | ~ v1_funct_1(C_363)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_365,B_364))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5607,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_5598])).

tff(c_5614,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_5607])).

tff(c_5616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5508,c_5614])).

tff(c_5617,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5507])).

tff(c_5438,plain,(
    ! [A_341,B_342,D_343] :
      ( r2_relset_1(A_341,B_342,D_343,D_343)
      | ~ m1_subset_1(D_343,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5447,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_5438])).

tff(c_5622,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5617,c_5617,c_5447])).

tff(c_5650,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5617,c_64])).

tff(c_5648,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5617,c_62])).

tff(c_5649,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5617,c_60])).

tff(c_5202,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5185,c_4372])).

tff(c_5280,plain,(
    ! [C_333,B_334,A_335] :
      ( v1_xboole_0(C_333)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(B_334,A_335)))
      | ~ v1_xboole_0(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5290,plain,(
    ! [A_336] :
      ( v1_xboole_0(k6_partfun1(A_336))
      | ~ v1_xboole_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_42,c_5280])).

tff(c_5200,plain,(
    ! [A_52] :
      ( A_52 = '#skF_3'
      | ~ v1_xboole_0(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5185,c_4371])).

tff(c_5298,plain,(
    ! [A_337] :
      ( k6_partfun1(A_337) = '#skF_3'
      | ~ v1_xboole_0(A_337) ) ),
    inference(resolution,[status(thm)],[c_5290,c_5200])).

tff(c_5306,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5202,c_5298])).

tff(c_46,plain,(
    ! [A_36] : k6_relat_1(A_36) = k6_partfun1(A_36) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_10,plain,(
    ! [A_4] : k2_funct_1(k6_relat_1(A_4)) = k6_relat_1(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_73,plain,(
    ! [A_4] : k2_funct_1(k6_partfun1(A_4)) = k6_partfun1(A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_10])).

tff(c_5330,plain,(
    k6_partfun1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5306,c_73])).

tff(c_5342,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5306,c_5330])).

tff(c_5628,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5617,c_5617,c_5342])).

tff(c_5647,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5617,c_58])).

tff(c_5917,plain,(
    ! [A_385,B_386] :
      ( k2_funct_2(A_385,B_386) = k2_funct_1(B_386)
      | ~ m1_subset_1(B_386,k1_zfmisc_1(k2_zfmisc_1(A_385,A_385)))
      | ~ v3_funct_2(B_386,A_385,A_385)
      | ~ v1_funct_2(B_386,A_385,A_385)
      | ~ v1_funct_1(B_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5920,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5647,c_5917])).

tff(c_5926,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5650,c_5648,c_5649,c_5628,c_5920])).

tff(c_5206,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5185,c_54])).

tff(c_5638,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5617,c_5617,c_5206])).

tff(c_5929,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5926,c_5638])).

tff(c_5932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5622,c_5929])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.37/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.37/2.30  
% 6.37/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.37/2.30  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.37/2.30  
% 6.37/2.30  %Foreground sorts:
% 6.37/2.30  
% 6.37/2.30  
% 6.37/2.30  %Background operators:
% 6.37/2.30  
% 6.37/2.30  
% 6.37/2.30  %Foreground operators:
% 6.37/2.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.37/2.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.37/2.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.37/2.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.37/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.37/2.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.37/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.37/2.30  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.37/2.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.37/2.30  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.37/2.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.37/2.30  tff('#skF_2', type, '#skF_2': $i).
% 6.37/2.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.37/2.30  tff('#skF_3', type, '#skF_3': $i).
% 6.37/2.30  tff('#skF_1', type, '#skF_1': $i).
% 6.37/2.30  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.37/2.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.37/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.37/2.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.37/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.37/2.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.37/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.37/2.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.37/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.37/2.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.37/2.30  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.37/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.37/2.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.37/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.37/2.30  
% 6.37/2.33  tff(f_187, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 6.37/2.33  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.37/2.33  tff(f_61, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 6.37/2.33  tff(f_73, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.37/2.33  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.37/2.33  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.37/2.33  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.37/2.33  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 6.37/2.33  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.37/2.33  tff(f_109, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.37/2.33  tff(f_105, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.37/2.33  tff(f_165, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.37/2.33  tff(f_119, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.37/2.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.37/2.33  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 6.37/2.33  tff(f_121, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.37/2.33  tff(f_44, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 6.37/2.33  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.37/2.33  tff(c_106, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.37/2.33  tff(c_117, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_106])).
% 6.37/2.33  tff(c_4562, plain, (![C_280, B_281, A_282]: (v1_xboole_0(C_280) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(B_281, A_282))) | ~v1_xboole_0(A_282))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.37/2.33  tff(c_4573, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_4562])).
% 6.37/2.33  tff(c_4576, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_4573])).
% 6.37/2.33  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.37/2.33  tff(c_118, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_106])).
% 6.37/2.33  tff(c_917, plain, (![A_123, B_124, D_125]: (r2_relset_1(A_123, B_124, D_125, D_125) | ~m1_subset_1(D_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.37/2.33  tff(c_925, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_917])).
% 6.37/2.33  tff(c_145, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.37/2.33  tff(c_157, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_145])).
% 6.37/2.33  tff(c_245, plain, (![B_75, A_76]: (k2_relat_1(B_75)=A_76 | ~v2_funct_2(B_75, A_76) | ~v5_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.37/2.33  tff(c_251, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_157, c_245])).
% 6.37/2.33  tff(c_260, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_251])).
% 6.37/2.33  tff(c_274, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_260])).
% 6.37/2.33  tff(c_72, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.37/2.33  tff(c_68, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.37/2.33  tff(c_634, plain, (![C_103, B_104, A_105]: (v2_funct_2(C_103, B_104) | ~v3_funct_2(C_103, A_105, B_104) | ~v1_funct_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.37/2.33  tff(c_646, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_634])).
% 6.37/2.33  tff(c_656, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_646])).
% 6.37/2.33  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_656])).
% 6.37/2.33  tff(c_659, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_260])).
% 6.37/2.33  tff(c_6, plain, (![A_3]: (k2_relat_1(A_3)!=k1_xboole_0 | k1_xboole_0=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.37/2.33  tff(c_134, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_118, c_6])).
% 6.37/2.33  tff(c_144, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_134])).
% 6.37/2.33  tff(c_661, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_659, c_144])).
% 6.37/2.33  tff(c_70, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.37/2.33  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.37/2.33  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.37/2.33  tff(c_937, plain, (![A_127, B_128, C_129]: (k2_relset_1(A_127, B_128, C_129)=k2_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.37/2.33  tff(c_946, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_937])).
% 6.37/2.33  tff(c_951, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_659, c_946])).
% 6.37/2.33  tff(c_42, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.37/2.33  tff(c_924, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_42, c_917])).
% 6.37/2.33  tff(c_1004, plain, (![C_131, A_132, B_133]: (v2_funct_1(C_131) | ~v3_funct_2(C_131, A_132, B_133) | ~v1_funct_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.37/2.33  tff(c_1016, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1004])).
% 6.37/2.33  tff(c_1024, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1016])).
% 6.37/2.33  tff(c_1714, plain, (![B_180, A_181, C_177, D_178, F_176, E_179]: (m1_subset_1(k1_partfun1(A_181, B_180, C_177, D_178, E_179, F_176), k1_zfmisc_1(k2_zfmisc_1(A_181, D_178))) | ~m1_subset_1(F_176, k1_zfmisc_1(k2_zfmisc_1(C_177, D_178))) | ~v1_funct_1(F_176) | ~m1_subset_1(E_179, k1_zfmisc_1(k2_zfmisc_1(A_181, B_180))) | ~v1_funct_1(E_179))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.37/2.33  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.37/2.33  tff(c_1084, plain, (![D_140, C_141, A_142, B_143]: (D_140=C_141 | ~r2_relset_1(A_142, B_143, C_141, D_140) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.37/2.33  tff(c_1094, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_1084])).
% 6.37/2.33  tff(c_1113, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1094])).
% 6.37/2.33  tff(c_1145, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1113])).
% 6.37/2.33  tff(c_1722, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_1714, c_1145])).
% 6.37/2.33  tff(c_1755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_64, c_58, c_1722])).
% 6.37/2.33  tff(c_1756, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1113])).
% 6.37/2.33  tff(c_4330, plain, (![C_252, D_253, B_254, A_255]: (k2_funct_1(C_252)=D_253 | k1_xboole_0=B_254 | k1_xboole_0=A_255 | ~v2_funct_1(C_252) | ~r2_relset_1(A_255, A_255, k1_partfun1(A_255, B_254, B_254, A_255, C_252, D_253), k6_partfun1(A_255)) | k2_relset_1(A_255, B_254, C_252)!=B_254 | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1(B_254, A_255))) | ~v1_funct_2(D_253, B_254, A_255) | ~v1_funct_1(D_253) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_255, B_254))) | ~v1_funct_2(C_252, A_255, B_254) | ~v1_funct_1(C_252))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.37/2.33  tff(c_4351, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1756, c_4330])).
% 6.37/2.33  tff(c_4359, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_58, c_951, c_924, c_1024, c_4351])).
% 6.37/2.33  tff(c_4360, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_661, c_4359])).
% 6.37/2.33  tff(c_1861, plain, (![A_189, B_190]: (k2_funct_2(A_189, B_190)=k2_funct_1(B_190) | ~m1_subset_1(B_190, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v3_funct_2(B_190, A_189, A_189) | ~v1_funct_2(B_190, A_189, A_189) | ~v1_funct_1(B_190))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.37/2.33  tff(c_1876, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1861])).
% 6.37/2.33  tff(c_1888, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1876])).
% 6.37/2.33  tff(c_54, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.37/2.33  tff(c_1893, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_54])).
% 6.37/2.33  tff(c_4362, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4360, c_1893])).
% 6.37/2.33  tff(c_4366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_925, c_4362])).
% 6.37/2.33  tff(c_4367, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_134])).
% 6.37/2.33  tff(c_4368, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_134])).
% 6.37/2.33  tff(c_4381, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4367, c_4368])).
% 6.37/2.33  tff(c_4444, plain, (![C_265, B_266, A_267]: (v5_relat_1(C_265, B_266) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_267, B_266))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.37/2.33  tff(c_4456, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_4444])).
% 6.37/2.33  tff(c_4577, plain, (![B_283, A_284]: (k2_relat_1(B_283)=A_284 | ~v2_funct_2(B_283, A_284) | ~v5_relat_1(B_283, A_284) | ~v1_relat_1(B_283))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.37/2.33  tff(c_4586, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4456, c_4577])).
% 6.37/2.33  tff(c_4598, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_4381, c_4586])).
% 6.37/2.33  tff(c_4610, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_4598])).
% 6.37/2.33  tff(c_5040, plain, (![C_314, B_315, A_316]: (v2_funct_2(C_314, B_315) | ~v3_funct_2(C_314, A_316, B_315) | ~v1_funct_1(C_314) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_316, B_315))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.37/2.33  tff(c_5052, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_5040])).
% 6.37/2.33  tff(c_5062, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_5052])).
% 6.37/2.33  tff(c_5064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4610, c_5062])).
% 6.37/2.33  tff(c_5065, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_4598])).
% 6.37/2.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.37/2.33  tff(c_4372, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4367, c_2])).
% 6.37/2.33  tff(c_5079, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5065, c_4372])).
% 6.37/2.33  tff(c_5089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4576, c_5079])).
% 6.37/2.33  tff(c_5091, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_4573])).
% 6.37/2.33  tff(c_93, plain, (![B_51, A_52]: (~v1_xboole_0(B_51) | B_51=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.37/2.33  tff(c_96, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_2, c_93])).
% 6.37/2.33  tff(c_4371, plain, (![A_52]: (A_52='#skF_2' | ~v1_xboole_0(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_4367, c_96])).
% 6.37/2.33  tff(c_5104, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_5091, c_4371])).
% 6.37/2.33  tff(c_5090, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_4573])).
% 6.37/2.33  tff(c_5097, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_5090, c_4371])).
% 6.37/2.33  tff(c_5139, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5104, c_5097])).
% 6.37/2.33  tff(c_5117, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5097, c_5097, c_4381])).
% 6.37/2.33  tff(c_5172, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5139, c_5139, c_5117])).
% 6.37/2.33  tff(c_126, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_117, c_6])).
% 6.37/2.33  tff(c_4392, plain, (k2_relat_1('#skF_3')!='#skF_2' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4367, c_4367, c_126])).
% 6.37/2.33  tff(c_4393, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_4392])).
% 6.37/2.33  tff(c_5115, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5097, c_4393])).
% 6.37/2.33  tff(c_5184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5172, c_5139, c_5139, c_5115])).
% 6.37/2.33  tff(c_5185, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_4392])).
% 6.37/2.33  tff(c_5201, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5185, c_5185, c_4381])).
% 6.37/2.33  tff(c_5241, plain, (![C_325, B_326, A_327]: (v5_relat_1(C_325, B_326) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_327, B_326))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.37/2.33  tff(c_5249, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_5241])).
% 6.37/2.33  tff(c_5483, plain, (![B_347, A_348]: (k2_relat_1(B_347)=A_348 | ~v2_funct_2(B_347, A_348) | ~v5_relat_1(B_347, A_348) | ~v1_relat_1(B_347))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.37/2.33  tff(c_5495, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5249, c_5483])).
% 6.37/2.33  tff(c_5507, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_5201, c_5495])).
% 6.37/2.33  tff(c_5508, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_5507])).
% 6.37/2.33  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 6.37/2.33  tff(c_5598, plain, (![C_363, B_364, A_365]: (v2_funct_2(C_363, B_364) | ~v3_funct_2(C_363, A_365, B_364) | ~v1_funct_1(C_363) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_365, B_364))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.37/2.33  tff(c_5607, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_5598])).
% 6.37/2.33  tff(c_5614, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_5607])).
% 6.37/2.33  tff(c_5616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5508, c_5614])).
% 6.37/2.33  tff(c_5617, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_5507])).
% 6.37/2.33  tff(c_5438, plain, (![A_341, B_342, D_343]: (r2_relset_1(A_341, B_342, D_343, D_343) | ~m1_subset_1(D_343, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.37/2.33  tff(c_5447, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_5438])).
% 6.37/2.33  tff(c_5622, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5617, c_5617, c_5447])).
% 6.37/2.33  tff(c_5650, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5617, c_64])).
% 6.37/2.33  tff(c_5648, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5617, c_62])).
% 6.37/2.33  tff(c_5649, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5617, c_60])).
% 6.37/2.33  tff(c_5202, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5185, c_4372])).
% 6.37/2.33  tff(c_5280, plain, (![C_333, B_334, A_335]: (v1_xboole_0(C_333) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(B_334, A_335))) | ~v1_xboole_0(A_335))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.37/2.33  tff(c_5290, plain, (![A_336]: (v1_xboole_0(k6_partfun1(A_336)) | ~v1_xboole_0(A_336))), inference(resolution, [status(thm)], [c_42, c_5280])).
% 6.37/2.33  tff(c_5200, plain, (![A_52]: (A_52='#skF_3' | ~v1_xboole_0(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_5185, c_4371])).
% 6.37/2.33  tff(c_5298, plain, (![A_337]: (k6_partfun1(A_337)='#skF_3' | ~v1_xboole_0(A_337))), inference(resolution, [status(thm)], [c_5290, c_5200])).
% 6.37/2.33  tff(c_5306, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_5202, c_5298])).
% 6.37/2.33  tff(c_46, plain, (![A_36]: (k6_relat_1(A_36)=k6_partfun1(A_36))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.37/2.33  tff(c_10, plain, (![A_4]: (k2_funct_1(k6_relat_1(A_4))=k6_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.37/2.33  tff(c_73, plain, (![A_4]: (k2_funct_1(k6_partfun1(A_4))=k6_partfun1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_10])).
% 6.37/2.33  tff(c_5330, plain, (k6_partfun1('#skF_3')=k2_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5306, c_73])).
% 6.37/2.33  tff(c_5342, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5306, c_5330])).
% 6.37/2.33  tff(c_5628, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5617, c_5617, c_5342])).
% 6.37/2.33  tff(c_5647, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5617, c_58])).
% 6.37/2.33  tff(c_5917, plain, (![A_385, B_386]: (k2_funct_2(A_385, B_386)=k2_funct_1(B_386) | ~m1_subset_1(B_386, k1_zfmisc_1(k2_zfmisc_1(A_385, A_385))) | ~v3_funct_2(B_386, A_385, A_385) | ~v1_funct_2(B_386, A_385, A_385) | ~v1_funct_1(B_386))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.37/2.33  tff(c_5920, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_5647, c_5917])).
% 6.37/2.33  tff(c_5926, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5650, c_5648, c_5649, c_5628, c_5920])).
% 6.37/2.33  tff(c_5206, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5185, c_54])).
% 6.37/2.33  tff(c_5638, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5617, c_5617, c_5206])).
% 6.37/2.33  tff(c_5929, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5926, c_5638])).
% 6.37/2.33  tff(c_5932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5622, c_5929])).
% 6.37/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.37/2.33  
% 6.37/2.33  Inference rules
% 6.37/2.33  ----------------------
% 6.37/2.33  #Ref     : 0
% 6.37/2.33  #Sup     : 1509
% 6.37/2.33  #Fact    : 0
% 6.37/2.33  #Define  : 0
% 6.37/2.33  #Split   : 26
% 6.37/2.33  #Chain   : 0
% 6.37/2.33  #Close   : 0
% 6.37/2.33  
% 6.37/2.33  Ordering : KBO
% 6.37/2.33  
% 6.37/2.33  Simplification rules
% 6.37/2.33  ----------------------
% 6.37/2.33  #Subsume      : 333
% 6.37/2.33  #Demod        : 1045
% 6.37/2.33  #Tautology    : 512
% 6.37/2.33  #SimpNegUnit  : 14
% 6.37/2.33  #BackRed      : 109
% 6.37/2.33  
% 6.37/2.33  #Partial instantiations: 0
% 6.37/2.33  #Strategies tried      : 1
% 6.37/2.33  
% 6.37/2.33  Timing (in seconds)
% 6.37/2.33  ----------------------
% 6.37/2.33  Preprocessing        : 0.36
% 6.37/2.33  Parsing              : 0.18
% 6.37/2.33  CNF conversion       : 0.02
% 6.37/2.33  Main loop            : 1.09
% 6.37/2.33  Inferencing          : 0.35
% 6.37/2.33  Reduction            : 0.39
% 6.37/2.33  Demodulation         : 0.28
% 6.37/2.33  BG Simplification    : 0.04
% 6.37/2.33  Subsumption          : 0.23
% 6.37/2.33  Abstraction          : 0.05
% 6.37/2.33  MUC search           : 0.00
% 6.37/2.33  Cooper               : 0.00
% 6.37/2.33  Total                : 1.50
% 6.37/2.33  Index Insertion      : 0.00
% 6.37/2.33  Index Deletion       : 0.00
% 6.37/2.33  Index Matching       : 0.00
% 6.37/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
