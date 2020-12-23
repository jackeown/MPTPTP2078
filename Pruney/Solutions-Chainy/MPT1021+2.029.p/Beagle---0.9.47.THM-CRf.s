%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:04 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :  194 (1585 expanded)
%              Number of leaves         :   43 ( 581 expanded)
%              Depth                    :   22
%              Number of atoms          :  426 (4864 expanded)
%              Number of equality atoms :   59 ( 344 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_121,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1181,plain,(
    ! [C_141,A_142,B_143] :
      ( v1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1189,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1181])).

tff(c_62,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_58,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1572,plain,(
    ! [C_198,A_199,B_200] :
      ( v2_funct_1(C_198)
      | ~ v3_funct_2(C_198,A_199,B_200)
      | ~ v1_funct_1(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1584,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1572])).

tff(c_1592,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_1584])).

tff(c_38,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1422,plain,(
    ! [A_183,B_184,D_185] :
      ( r2_relset_1(A_183,B_184,D_185,D_185)
      | ~ m1_subset_1(D_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1427,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_38,c_1422])).

tff(c_1191,plain,(
    ! [C_145,B_146,A_147] :
      ( v5_relat_1(C_145,B_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1199,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1191])).

tff(c_1228,plain,(
    ! [B_156,A_157] :
      ( k2_relat_1(B_156) = A_157
      | ~ v2_funct_2(B_156,A_157)
      | ~ v5_relat_1(B_156,A_157)
      | ~ v1_relat_1(B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1234,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1199,c_1228])).

tff(c_1240,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_1234])).

tff(c_1241,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1240])).

tff(c_1387,plain,(
    ! [C_179,B_180,A_181] :
      ( v2_funct_2(C_179,B_180)
      | ~ v3_funct_2(C_179,A_181,B_180)
      | ~ v1_funct_1(C_179)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_181,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1396,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1387])).

tff(c_1401,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_1396])).

tff(c_1403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1241,c_1401])).

tff(c_1404,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1240])).

tff(c_44,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_10,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_relat_1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_64,plain,(
    ! [A_3] :
      ( k5_relat_1(k2_funct_1(A_3),A_3) = k6_partfun1(k2_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_2] :
      ( k1_relat_1(k2_funct_1(A_2)) = k2_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1442,plain,(
    ! [A_188] :
      ( m1_subset_1(A_188,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_188),k2_relat_1(A_188))))
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_18,plain,(
    ! [C_9,A_7,B_8] :
      ( v4_relat_1(C_9,A_7)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1504,plain,(
    ! [A_190] :
      ( v4_relat_1(A_190,k1_relat_1(A_190))
      | ~ v1_funct_1(A_190)
      | ~ v1_relat_1(A_190) ) ),
    inference(resolution,[status(thm)],[c_1442,c_18])).

tff(c_1721,plain,(
    ! [A_212] :
      ( v4_relat_1(k2_funct_1(A_212),k2_relat_1(A_212))
      | ~ v1_funct_1(k2_funct_1(A_212))
      | ~ v1_relat_1(k2_funct_1(A_212))
      | ~ v2_funct_1(A_212)
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1504])).

tff(c_1724,plain,
    ( v4_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1404,c_1721])).

tff(c_1729,plain,
    ( v4_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_62,c_1592,c_1724])).

tff(c_1752,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1729])).

tff(c_1755,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_1752])).

tff(c_1759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_62,c_1755])).

tff(c_1760,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_2'))
    | v4_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1729])).

tff(c_1763,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1760])).

tff(c_1766,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_1763])).

tff(c_1770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_62,c_1766])).

tff(c_1772,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1760])).

tff(c_1761,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1729])).

tff(c_60,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1529,plain,(
    ! [A_193,B_194,C_195] :
      ( k1_relset_1(A_193,B_194,C_195) = k1_relat_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1545,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1529])).

tff(c_1658,plain,(
    ! [A_209,B_210] :
      ( k1_relset_1(A_209,A_209,B_210) = A_209
      | ~ m1_subset_1(B_210,k1_zfmisc_1(k2_zfmisc_1(A_209,A_209)))
      | ~ v1_funct_2(B_210,A_209,A_209)
      | ~ v1_funct_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1664,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1658])).

tff(c_1669,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_1545,c_1664])).

tff(c_6,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [C_9,B_8,A_7] :
      ( v5_relat_1(C_9,B_8)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1486,plain,(
    ! [A_189] :
      ( v5_relat_1(A_189,k2_relat_1(A_189))
      | ~ v1_funct_1(A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(resolution,[status(thm)],[c_1442,c_16])).

tff(c_1797,plain,(
    ! [A_219] :
      ( v5_relat_1(k2_funct_1(A_219),k1_relat_1(A_219))
      | ~ v1_funct_1(k2_funct_1(A_219))
      | ~ v1_relat_1(k2_funct_1(A_219))
      | ~ v2_funct_1(A_219)
      | ~ v1_funct_1(A_219)
      | ~ v1_relat_1(A_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1486])).

tff(c_1803,plain,
    ( v5_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1669,c_1797])).

tff(c_1809,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_62,c_1592,c_1761,c_1772,c_1803])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(B_21) = A_20
      | ~ v2_funct_2(B_21,A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1812,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1809,c_34])).

tff(c_1815,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1761,c_1812])).

tff(c_1816,plain,(
    ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1815])).

tff(c_32,plain,(
    ! [B_21] :
      ( v2_funct_2(B_21,k2_relat_1(B_21))
      | ~ v5_relat_1(B_21,k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1508,plain,(
    ! [A_191] :
      ( v2_funct_2(A_191,k2_relat_1(A_191))
      | ~ v1_funct_1(A_191)
      | ~ v1_relat_1(A_191) ) ),
    inference(resolution,[status(thm)],[c_1486,c_32])).

tff(c_1829,plain,(
    ! [A_226] :
      ( v2_funct_2(k2_funct_1(A_226),k1_relat_1(A_226))
      | ~ v1_funct_1(k2_funct_1(A_226))
      | ~ v1_relat_1(k2_funct_1(A_226))
      | ~ v2_funct_1(A_226)
      | ~ v1_funct_1(A_226)
      | ~ v1_relat_1(A_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1508])).

tff(c_1832,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1669,c_1829])).

tff(c_1837,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_62,c_1592,c_1761,c_1772,c_1832])).

tff(c_1839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1816,c_1837])).

tff(c_1840,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1815])).

tff(c_46,plain,(
    ! [A_32] :
      ( m1_subset_1(A_32,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_32),k2_relat_1(A_32))))
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1863,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_2')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1840,c_46])).

tff(c_1891,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_2')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1761,c_1772,c_1863])).

tff(c_1930,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_2'),'#skF_1')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1891])).

tff(c_1945,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_62,c_1592,c_1404,c_1930])).

tff(c_1946,plain,(
    ! [D_231,C_227,F_228,A_232,E_229,B_230] :
      ( k1_partfun1(A_232,B_230,C_227,D_231,E_229,F_228) = k5_relat_1(E_229,F_228)
      | ~ m1_subset_1(F_228,k1_zfmisc_1(k2_zfmisc_1(C_227,D_231)))
      | ~ v1_funct_1(F_228)
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230)))
      | ~ v1_funct_1(E_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1954,plain,(
    ! [A_232,B_230,E_229] :
      ( k1_partfun1(A_232,B_230,'#skF_1','#skF_1',E_229,'#skF_2') = k5_relat_1(E_229,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230)))
      | ~ v1_funct_1(E_229) ) ),
    inference(resolution,[status(thm)],[c_56,c_1946])).

tff(c_2023,plain,(
    ! [A_233,B_234,E_235] :
      ( k1_partfun1(A_233,B_234,'#skF_1','#skF_1',E_235,'#skF_2') = k5_relat_1(E_235,'#skF_2')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1954])).

tff(c_2026,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1945,c_2023])).

tff(c_2041,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1772,c_2026])).

tff(c_1773,plain,(
    ! [A_217,B_218] :
      ( k2_funct_2(A_217,B_218) = k2_funct_1(B_218)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_zfmisc_1(A_217,A_217)))
      | ~ v3_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1779,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1773])).

tff(c_1783,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1779])).

tff(c_79,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_87,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_79])).

tff(c_514,plain,(
    ! [C_98,A_99,B_100] :
      ( v2_funct_1(C_98)
      | ~ v3_funct_2(C_98,A_99,B_100)
      | ~ v1_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_526,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_514])).

tff(c_534,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_526])).

tff(c_111,plain,(
    ! [A_54,B_55,D_56] :
      ( r2_relset_1(A_54,B_55,D_56,D_56)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_116,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_382,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_394,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_382])).

tff(c_570,plain,(
    ! [A_106,B_107] :
      ( k1_relset_1(A_106,A_106,B_107) = A_106
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_zfmisc_1(A_106,A_106)))
      | ~ v1_funct_2(B_107,A_106,A_106)
      | ~ v1_funct_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_576,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_570])).

tff(c_581,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_394,c_576])).

tff(c_12,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_63,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_355,plain,(
    ! [A_86] :
      ( m1_subset_1(A_86,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_86),k2_relat_1(A_86))))
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_424,plain,(
    ! [A_90] :
      ( v5_relat_1(A_90,k2_relat_1(A_90))
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_355,c_16])).

tff(c_634,plain,(
    ! [A_110] :
      ( v5_relat_1(k2_funct_1(A_110),k1_relat_1(A_110))
      | ~ v1_funct_1(k2_funct_1(A_110))
      | ~ v1_relat_1(k2_funct_1(A_110))
      | ~ v2_funct_1(A_110)
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_424])).

tff(c_640,plain,
    ( v5_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_634])).

tff(c_646,plain,
    ( v5_relat_1(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_62,c_534,c_640])).

tff(c_647,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_646])).

tff(c_650,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_647])).

tff(c_654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_62,c_650])).

tff(c_655,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_2'))
    | v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_646])).

tff(c_674,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_655])).

tff(c_677,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_674])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_62,c_677])).

tff(c_683,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_89,plain,(
    ! [C_44,B_45,A_46] :
      ( v5_relat_1(C_44,B_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_89])).

tff(c_119,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(B_58) = A_59
      | ~ v2_funct_2(B_58,A_59)
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_125,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_97,c_119])).

tff(c_131,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_125])).

tff(c_132,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_293,plain,(
    ! [C_80,B_81,A_82] :
      ( v2_funct_2(C_80,B_81)
      | ~ v3_funct_2(C_80,A_82,B_81)
      | ~ v1_funct_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_302,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_293])).

tff(c_307,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_302])).

tff(c_309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_307])).

tff(c_310,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_656,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_646])).

tff(c_682,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_686,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_682,c_34])).

tff(c_689,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_686])).

tff(c_690,plain,(
    ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_689])).

tff(c_455,plain,(
    ! [A_93] :
      ( v2_funct_2(A_93,k2_relat_1(A_93))
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_424,c_32])).

tff(c_716,plain,(
    ! [A_118] :
      ( v2_funct_2(k2_funct_1(A_118),k1_relat_1(A_118))
      | ~ v1_funct_1(k2_funct_1(A_118))
      | ~ v1_relat_1(k2_funct_1(A_118))
      | ~ v2_funct_1(A_118)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_455])).

tff(c_719,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_716])).

tff(c_724,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_62,c_534,c_656,c_683,c_719])).

tff(c_726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_690,c_724])).

tff(c_727,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_689])).

tff(c_747,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_2')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_46])).

tff(c_773,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_2')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_683,c_747])).

tff(c_841,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_2'),'#skF_1')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_773])).

tff(c_857,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_62,c_534,c_310,c_841])).

tff(c_914,plain,(
    ! [C_121,A_126,E_123,D_125,B_124,F_122] :
      ( k1_partfun1(A_126,B_124,C_121,D_125,E_123,F_122) = k5_relat_1(E_123,F_122)
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_121,D_125)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_126,B_124)))
      | ~ v1_funct_1(E_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_916,plain,(
    ! [A_126,B_124,E_123] :
      ( k1_partfun1(A_126,B_124,'#skF_1','#skF_1',E_123,k2_funct_1('#skF_2')) = k5_relat_1(E_123,k2_funct_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_126,B_124)))
      | ~ v1_funct_1(E_123) ) ),
    inference(resolution,[status(thm)],[c_857,c_914])).

tff(c_1147,plain,(
    ! [A_138,B_139,E_140] :
      ( k1_partfun1(A_138,B_139,'#skF_1','#skF_1',E_140,k2_funct_1('#skF_2')) = k5_relat_1(E_140,k2_funct_1('#skF_2'))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_916])).

tff(c_1159,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1147])).

tff(c_1167,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1159])).

tff(c_790,plain,(
    ! [A_119,B_120] :
      ( k2_funct_2(A_119,B_120) = k2_funct_1(B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1(A_119,A_119)))
      | ~ v3_funct_2(B_120,A_119,A_119)
      | ~ v1_funct_2(B_120,A_119,A_119)
      | ~ v1_funct_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_796,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_790])).

tff(c_800,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_796])).

tff(c_54,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_78,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_801,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_78])).

tff(c_1168,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1167,c_801])).

tff(c_1175,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_1168])).

tff(c_1178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_62,c_534,c_116,c_581,c_1175])).

tff(c_1179,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1786,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_1179])).

tff(c_2125,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2041,c_1786])).

tff(c_2154,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2125])).

tff(c_2157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1189,c_62,c_1592,c_1427,c_1404,c_2154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.78  
% 4.50/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.78  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.50/1.78  
% 4.50/1.78  %Foreground sorts:
% 4.50/1.78  
% 4.50/1.78  
% 4.50/1.78  %Background operators:
% 4.50/1.78  
% 4.50/1.78  
% 4.50/1.78  %Foreground operators:
% 4.50/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.50/1.78  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.50/1.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.50/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.78  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.50/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.50/1.78  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.50/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.50/1.78  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.50/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.50/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.50/1.78  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.50/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.50/1.78  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.50/1.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.50/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.50/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.50/1.78  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.50/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.50/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.50/1.78  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.50/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.50/1.78  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.50/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.50/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.50/1.78  
% 4.67/1.83  tff(f_152, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 4.67/1.83  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.67/1.83  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.67/1.83  tff(f_99, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.67/1.83  tff(f_75, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.67/1.83  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.67/1.83  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.67/1.83  tff(f_121, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.67/1.83  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 4.67/1.83  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.67/1.83  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.67/1.83  tff(f_131, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.67/1.83  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.67/1.83  tff(f_139, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 4.67/1.83  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.67/1.83  tff(f_119, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.67/1.83  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.67/1.83  tff(c_1181, plain, (![C_141, A_142, B_143]: (v1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.67/1.83  tff(c_1189, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1181])).
% 4.67/1.83  tff(c_62, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.67/1.83  tff(c_58, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.67/1.83  tff(c_1572, plain, (![C_198, A_199, B_200]: (v2_funct_1(C_198) | ~v3_funct_2(C_198, A_199, B_200) | ~v1_funct_1(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.67/1.83  tff(c_1584, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1572])).
% 4.67/1.83  tff(c_1592, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_1584])).
% 4.67/1.83  tff(c_38, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.67/1.83  tff(c_1422, plain, (![A_183, B_184, D_185]: (r2_relset_1(A_183, B_184, D_185, D_185) | ~m1_subset_1(D_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.67/1.83  tff(c_1427, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_38, c_1422])).
% 4.67/1.83  tff(c_1191, plain, (![C_145, B_146, A_147]: (v5_relat_1(C_145, B_146) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.67/1.83  tff(c_1199, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_1191])).
% 4.67/1.83  tff(c_1228, plain, (![B_156, A_157]: (k2_relat_1(B_156)=A_157 | ~v2_funct_2(B_156, A_157) | ~v5_relat_1(B_156, A_157) | ~v1_relat_1(B_156))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_1234, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1199, c_1228])).
% 4.67/1.83  tff(c_1240, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_1234])).
% 4.67/1.83  tff(c_1241, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1240])).
% 4.67/1.83  tff(c_1387, plain, (![C_179, B_180, A_181]: (v2_funct_2(C_179, B_180) | ~v3_funct_2(C_179, A_181, B_180) | ~v1_funct_1(C_179) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_181, B_180))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.67/1.83  tff(c_1396, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1387])).
% 4.67/1.83  tff(c_1401, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_1396])).
% 4.67/1.83  tff(c_1403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1241, c_1401])).
% 4.67/1.83  tff(c_1404, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1240])).
% 4.67/1.83  tff(c_44, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.67/1.83  tff(c_10, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_relat_1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.67/1.83  tff(c_64, plain, (![A_3]: (k5_relat_1(k2_funct_1(A_3), A_3)=k6_partfun1(k2_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 4.67/1.83  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.67/1.83  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.67/1.83  tff(c_8, plain, (![A_2]: (k1_relat_1(k2_funct_1(A_2))=k2_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.67/1.83  tff(c_1442, plain, (![A_188]: (m1_subset_1(A_188, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_188), k2_relat_1(A_188)))) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.67/1.83  tff(c_18, plain, (![C_9, A_7, B_8]: (v4_relat_1(C_9, A_7) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.67/1.83  tff(c_1504, plain, (![A_190]: (v4_relat_1(A_190, k1_relat_1(A_190)) | ~v1_funct_1(A_190) | ~v1_relat_1(A_190))), inference(resolution, [status(thm)], [c_1442, c_18])).
% 4.67/1.83  tff(c_1721, plain, (![A_212]: (v4_relat_1(k2_funct_1(A_212), k2_relat_1(A_212)) | ~v1_funct_1(k2_funct_1(A_212)) | ~v1_relat_1(k2_funct_1(A_212)) | ~v2_funct_1(A_212) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1504])).
% 4.67/1.83  tff(c_1724, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1404, c_1721])).
% 4.67/1.83  tff(c_1729, plain, (v4_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_62, c_1592, c_1724])).
% 4.67/1.83  tff(c_1752, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1729])).
% 4.67/1.83  tff(c_1755, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4, c_1752])).
% 4.67/1.83  tff(c_1759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1189, c_62, c_1755])).
% 4.67/1.83  tff(c_1760, plain, (~v1_funct_1(k2_funct_1('#skF_2')) | v4_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_1729])).
% 4.67/1.83  tff(c_1763, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1760])).
% 4.67/1.83  tff(c_1766, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_1763])).
% 4.67/1.83  tff(c_1770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1189, c_62, c_1766])).
% 4.67/1.83  tff(c_1772, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1760])).
% 4.67/1.83  tff(c_1761, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1729])).
% 4.67/1.83  tff(c_60, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.67/1.83  tff(c_1529, plain, (![A_193, B_194, C_195]: (k1_relset_1(A_193, B_194, C_195)=k1_relat_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.67/1.83  tff(c_1545, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1529])).
% 4.67/1.83  tff(c_1658, plain, (![A_209, B_210]: (k1_relset_1(A_209, A_209, B_210)=A_209 | ~m1_subset_1(B_210, k1_zfmisc_1(k2_zfmisc_1(A_209, A_209))) | ~v1_funct_2(B_210, A_209, A_209) | ~v1_funct_1(B_210))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.67/1.83  tff(c_1664, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1658])).
% 4.67/1.83  tff(c_1669, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_1545, c_1664])).
% 4.67/1.83  tff(c_6, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.67/1.83  tff(c_16, plain, (![C_9, B_8, A_7]: (v5_relat_1(C_9, B_8) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.67/1.83  tff(c_1486, plain, (![A_189]: (v5_relat_1(A_189, k2_relat_1(A_189)) | ~v1_funct_1(A_189) | ~v1_relat_1(A_189))), inference(resolution, [status(thm)], [c_1442, c_16])).
% 4.67/1.83  tff(c_1797, plain, (![A_219]: (v5_relat_1(k2_funct_1(A_219), k1_relat_1(A_219)) | ~v1_funct_1(k2_funct_1(A_219)) | ~v1_relat_1(k2_funct_1(A_219)) | ~v2_funct_1(A_219) | ~v1_funct_1(A_219) | ~v1_relat_1(A_219))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1486])).
% 4.67/1.83  tff(c_1803, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1669, c_1797])).
% 4.67/1.83  tff(c_1809, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_62, c_1592, c_1761, c_1772, c_1803])).
% 4.67/1.83  tff(c_34, plain, (![B_21, A_20]: (k2_relat_1(B_21)=A_20 | ~v2_funct_2(B_21, A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_1812, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1809, c_34])).
% 4.67/1.83  tff(c_1815, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1761, c_1812])).
% 4.67/1.83  tff(c_1816, plain, (~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1815])).
% 4.67/1.83  tff(c_32, plain, (![B_21]: (v2_funct_2(B_21, k2_relat_1(B_21)) | ~v5_relat_1(B_21, k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_1508, plain, (![A_191]: (v2_funct_2(A_191, k2_relat_1(A_191)) | ~v1_funct_1(A_191) | ~v1_relat_1(A_191))), inference(resolution, [status(thm)], [c_1486, c_32])).
% 4.67/1.83  tff(c_1829, plain, (![A_226]: (v2_funct_2(k2_funct_1(A_226), k1_relat_1(A_226)) | ~v1_funct_1(k2_funct_1(A_226)) | ~v1_relat_1(k2_funct_1(A_226)) | ~v2_funct_1(A_226) | ~v1_funct_1(A_226) | ~v1_relat_1(A_226))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1508])).
% 4.67/1.83  tff(c_1832, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1669, c_1829])).
% 4.67/1.83  tff(c_1837, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_62, c_1592, c_1761, c_1772, c_1832])).
% 4.67/1.83  tff(c_1839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1816, c_1837])).
% 4.67/1.83  tff(c_1840, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_1815])).
% 4.67/1.83  tff(c_46, plain, (![A_32]: (m1_subset_1(A_32, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_32), k2_relat_1(A_32)))) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.67/1.83  tff(c_1863, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_2')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1840, c_46])).
% 4.67/1.83  tff(c_1891, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_2')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1761, c_1772, c_1863])).
% 4.67/1.83  tff(c_1930, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_2'), '#skF_1'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_1891])).
% 4.67/1.83  tff(c_1945, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1189, c_62, c_1592, c_1404, c_1930])).
% 4.67/1.83  tff(c_1946, plain, (![D_231, C_227, F_228, A_232, E_229, B_230]: (k1_partfun1(A_232, B_230, C_227, D_231, E_229, F_228)=k5_relat_1(E_229, F_228) | ~m1_subset_1(F_228, k1_zfmisc_1(k2_zfmisc_1(C_227, D_231))) | ~v1_funct_1(F_228) | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))) | ~v1_funct_1(E_229))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.67/1.83  tff(c_1954, plain, (![A_232, B_230, E_229]: (k1_partfun1(A_232, B_230, '#skF_1', '#skF_1', E_229, '#skF_2')=k5_relat_1(E_229, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))) | ~v1_funct_1(E_229))), inference(resolution, [status(thm)], [c_56, c_1946])).
% 4.67/1.83  tff(c_2023, plain, (![A_233, B_234, E_235]: (k1_partfun1(A_233, B_234, '#skF_1', '#skF_1', E_235, '#skF_2')=k5_relat_1(E_235, '#skF_2') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_235))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1954])).
% 4.67/1.83  tff(c_2026, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1945, c_2023])).
% 4.67/1.83  tff(c_2041, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1772, c_2026])).
% 4.67/1.83  tff(c_1773, plain, (![A_217, B_218]: (k2_funct_2(A_217, B_218)=k2_funct_1(B_218) | ~m1_subset_1(B_218, k1_zfmisc_1(k2_zfmisc_1(A_217, A_217))) | ~v3_funct_2(B_218, A_217, A_217) | ~v1_funct_2(B_218, A_217, A_217) | ~v1_funct_1(B_218))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.67/1.83  tff(c_1779, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1773])).
% 4.67/1.83  tff(c_1783, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1779])).
% 4.67/1.83  tff(c_79, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.67/1.83  tff(c_87, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_79])).
% 4.67/1.83  tff(c_514, plain, (![C_98, A_99, B_100]: (v2_funct_1(C_98) | ~v3_funct_2(C_98, A_99, B_100) | ~v1_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.67/1.83  tff(c_526, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_514])).
% 4.67/1.83  tff(c_534, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_526])).
% 4.67/1.83  tff(c_111, plain, (![A_54, B_55, D_56]: (r2_relset_1(A_54, B_55, D_56, D_56) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.67/1.83  tff(c_116, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_38, c_111])).
% 4.67/1.83  tff(c_382, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.67/1.83  tff(c_394, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_382])).
% 4.67/1.83  tff(c_570, plain, (![A_106, B_107]: (k1_relset_1(A_106, A_106, B_107)=A_106 | ~m1_subset_1(B_107, k1_zfmisc_1(k2_zfmisc_1(A_106, A_106))) | ~v1_funct_2(B_107, A_106, A_106) | ~v1_funct_1(B_107))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.67/1.83  tff(c_576, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_570])).
% 4.67/1.83  tff(c_581, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_394, c_576])).
% 4.67/1.83  tff(c_12, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.67/1.83  tff(c_63, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 4.67/1.83  tff(c_355, plain, (![A_86]: (m1_subset_1(A_86, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_86), k2_relat_1(A_86)))) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.67/1.83  tff(c_424, plain, (![A_90]: (v5_relat_1(A_90, k2_relat_1(A_90)) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_355, c_16])).
% 4.67/1.83  tff(c_634, plain, (![A_110]: (v5_relat_1(k2_funct_1(A_110), k1_relat_1(A_110)) | ~v1_funct_1(k2_funct_1(A_110)) | ~v1_relat_1(k2_funct_1(A_110)) | ~v2_funct_1(A_110) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(superposition, [status(thm), theory('equality')], [c_6, c_424])).
% 4.67/1.83  tff(c_640, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_581, c_634])).
% 4.67/1.83  tff(c_646, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_62, c_534, c_640])).
% 4.67/1.83  tff(c_647, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_646])).
% 4.67/1.83  tff(c_650, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4, c_647])).
% 4.67/1.83  tff(c_654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_62, c_650])).
% 4.67/1.83  tff(c_655, plain, (~v1_funct_1(k2_funct_1('#skF_2')) | v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_646])).
% 4.67/1.83  tff(c_674, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_655])).
% 4.67/1.83  tff(c_677, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_674])).
% 4.67/1.83  tff(c_681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_62, c_677])).
% 4.67/1.83  tff(c_683, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_655])).
% 4.67/1.83  tff(c_89, plain, (![C_44, B_45, A_46]: (v5_relat_1(C_44, B_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_46, B_45))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.67/1.83  tff(c_97, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_89])).
% 4.67/1.83  tff(c_119, plain, (![B_58, A_59]: (k2_relat_1(B_58)=A_59 | ~v2_funct_2(B_58, A_59) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.67/1.83  tff(c_125, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_97, c_119])).
% 4.67/1.83  tff(c_131, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_125])).
% 4.67/1.83  tff(c_132, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_131])).
% 4.67/1.83  tff(c_293, plain, (![C_80, B_81, A_82]: (v2_funct_2(C_80, B_81) | ~v3_funct_2(C_80, A_82, B_81) | ~v1_funct_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.67/1.83  tff(c_302, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_293])).
% 4.67/1.83  tff(c_307, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_302])).
% 4.67/1.83  tff(c_309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_307])).
% 4.67/1.83  tff(c_310, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_131])).
% 4.67/1.83  tff(c_656, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_646])).
% 4.67/1.83  tff(c_682, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_655])).
% 4.67/1.83  tff(c_686, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_682, c_34])).
% 4.67/1.83  tff(c_689, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_656, c_686])).
% 4.67/1.83  tff(c_690, plain, (~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_689])).
% 4.67/1.83  tff(c_455, plain, (![A_93]: (v2_funct_2(A_93, k2_relat_1(A_93)) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_424, c_32])).
% 4.67/1.83  tff(c_716, plain, (![A_118]: (v2_funct_2(k2_funct_1(A_118), k1_relat_1(A_118)) | ~v1_funct_1(k2_funct_1(A_118)) | ~v1_relat_1(k2_funct_1(A_118)) | ~v2_funct_1(A_118) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_6, c_455])).
% 4.67/1.83  tff(c_719, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_581, c_716])).
% 4.67/1.83  tff(c_724, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_62, c_534, c_656, c_683, c_719])).
% 4.67/1.83  tff(c_726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_690, c_724])).
% 4.67/1.83  tff(c_727, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_689])).
% 4.67/1.83  tff(c_747, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_2')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_727, c_46])).
% 4.67/1.83  tff(c_773, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_2')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_683, c_747])).
% 4.67/1.83  tff(c_841, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_2'), '#skF_1'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_773])).
% 4.67/1.83  tff(c_857, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_62, c_534, c_310, c_841])).
% 4.67/1.83  tff(c_914, plain, (![C_121, A_126, E_123, D_125, B_124, F_122]: (k1_partfun1(A_126, B_124, C_121, D_125, E_123, F_122)=k5_relat_1(E_123, F_122) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_121, D_125))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_126, B_124))) | ~v1_funct_1(E_123))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.67/1.83  tff(c_916, plain, (![A_126, B_124, E_123]: (k1_partfun1(A_126, B_124, '#skF_1', '#skF_1', E_123, k2_funct_1('#skF_2'))=k5_relat_1(E_123, k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_126, B_124))) | ~v1_funct_1(E_123))), inference(resolution, [status(thm)], [c_857, c_914])).
% 4.67/1.83  tff(c_1147, plain, (![A_138, B_139, E_140]: (k1_partfun1(A_138, B_139, '#skF_1', '#skF_1', E_140, k2_funct_1('#skF_2'))=k5_relat_1(E_140, k2_funct_1('#skF_2')) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(E_140))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_916])).
% 4.67/1.83  tff(c_1159, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1147])).
% 4.67/1.83  tff(c_1167, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1159])).
% 4.67/1.83  tff(c_790, plain, (![A_119, B_120]: (k2_funct_2(A_119, B_120)=k2_funct_1(B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1(A_119, A_119))) | ~v3_funct_2(B_120, A_119, A_119) | ~v1_funct_2(B_120, A_119, A_119) | ~v1_funct_1(B_120))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.67/1.83  tff(c_796, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_790])).
% 4.67/1.83  tff(c_800, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_796])).
% 4.67/1.83  tff(c_54, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.67/1.83  tff(c_78, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_54])).
% 4.67/1.83  tff(c_801, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_800, c_78])).
% 4.67/1.83  tff(c_1168, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1167, c_801])).
% 4.67/1.83  tff(c_1175, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_63, c_1168])).
% 4.67/1.83  tff(c_1178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_62, c_534, c_116, c_581, c_1175])).
% 4.67/1.83  tff(c_1179, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_54])).
% 4.67/1.83  tff(c_1786, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1783, c_1179])).
% 4.67/1.83  tff(c_2125, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2041, c_1786])).
% 4.67/1.83  tff(c_2154, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_64, c_2125])).
% 4.67/1.83  tff(c_2157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1189, c_62, c_1592, c_1427, c_1404, c_2154])).
% 4.67/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.83  
% 4.67/1.83  Inference rules
% 4.67/1.83  ----------------------
% 4.67/1.83  #Ref     : 0
% 4.67/1.83  #Sup     : 454
% 4.67/1.83  #Fact    : 0
% 4.67/1.83  #Define  : 0
% 4.67/1.83  #Split   : 14
% 4.67/1.83  #Chain   : 0
% 4.67/1.83  #Close   : 0
% 4.67/1.83  
% 4.67/1.83  Ordering : KBO
% 4.67/1.83  
% 4.67/1.83  Simplification rules
% 4.67/1.83  ----------------------
% 4.67/1.83  #Subsume      : 18
% 4.67/1.83  #Demod        : 555
% 4.67/1.83  #Tautology    : 232
% 4.67/1.83  #SimpNegUnit  : 4
% 4.67/1.83  #BackRed      : 26
% 4.67/1.83  
% 4.67/1.83  #Partial instantiations: 0
% 4.67/1.83  #Strategies tried      : 1
% 4.67/1.83  
% 4.67/1.83  Timing (in seconds)
% 4.67/1.83  ----------------------
% 4.67/1.83  Preprocessing        : 0.35
% 4.67/1.83  Parsing              : 0.18
% 4.67/1.83  CNF conversion       : 0.02
% 4.67/1.83  Main loop            : 0.66
% 4.67/1.83  Inferencing          : 0.24
% 4.67/1.83  Reduction            : 0.23
% 4.67/1.83  Demodulation         : 0.16
% 4.67/1.83  BG Simplification    : 0.03
% 4.67/1.83  Subsumption          : 0.10
% 4.67/1.83  Abstraction          : 0.03
% 4.67/1.83  MUC search           : 0.00
% 4.67/1.83  Cooper               : 0.00
% 4.67/1.83  Total                : 1.10
% 4.67/1.83  Index Insertion      : 0.00
% 4.67/1.83  Index Deletion       : 0.00
% 4.67/1.83  Index Matching       : 0.00
% 4.67/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
