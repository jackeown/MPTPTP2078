%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:31 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  157 (23540 expanded)
%              Number of leaves         :   41 (8200 expanded)
%              Depth                    :   26
%              Number of atoms          :  413 (68501 expanded)
%              Number of equality atoms :   73 (15379 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
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
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_60,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_61,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_69,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_61])).

tff(c_56,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_68,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_61])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_79,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_68,c_50])).

tff(c_87,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_87])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_46,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_168,plain,(
    ! [A_55,B_56,C_57] :
      ( k2_relset_1(A_55,B_56,C_57) = k2_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_172,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_168])).

tff(c_48,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_82,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_68,c_48])).

tff(c_173,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_82])).

tff(c_40,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(k2_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_187,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_40])).

tff(c_191,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_187])).

tff(c_192,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_191])).

tff(c_100,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_104,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_79,c_100])).

tff(c_148,plain,(
    ! [B_52,A_53] :
      ( k1_relat_1(B_52) = A_53
      | ~ v1_partfun1(B_52,A_53)
      | ~ v4_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_151,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_148])).

tff(c_154,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_151])).

tff(c_155,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_70,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_52])).

tff(c_80,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_70])).

tff(c_181,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_80])).

tff(c_182,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_79])).

tff(c_22,plain,(
    ! [C_16,A_13,B_14] :
      ( v1_partfun1(C_16,A_13)
      | ~ v1_funct_2(C_16,A_13,B_14)
      | ~ v1_funct_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | v1_xboole_0(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_201,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_182,c_22])).

tff(c_216,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_181,c_201])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_155,c_216])).

tff(c_219,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_225,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_79])).

tff(c_286,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_290,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_225,c_286])).

tff(c_223,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_82])).

tff(c_291,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_223])).

tff(c_224,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_80])).

tff(c_299,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_224])).

tff(c_298,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_225])).

tff(c_449,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( r2_funct_2(A_88,B_89,C_90,C_90)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2(D_91,A_88,B_89)
      | ~ v1_funct_1(D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2(C_90,A_88,B_89)
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_453,plain,(
    ! [C_90] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_90,C_90)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_90,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_298,c_449])).

tff(c_498,plain,(
    ! [C_92] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_92,C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_92,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_299,c_453])).

tff(c_503,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_498])).

tff(c_507,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_299,c_503])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_funct_1(k2_funct_1(A_3)) = A_3
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_296,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_290])).

tff(c_358,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_funct_1(k2_funct_1(C_69))
      | k2_relset_1(A_70,B_71,C_69) != B_71
      | ~ v2_funct_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_2(C_69,A_70,B_71)
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_361,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_358])).

tff(c_364,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_299,c_46,c_296,c_361])).

tff(c_365,plain,(
    ! [C_72,B_73,A_74] :
      ( v1_funct_2(k2_funct_1(C_72),B_73,A_74)
      | k2_relset_1(A_74,B_73,C_72) != B_73
      | ~ v2_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73)))
      | ~ v1_funct_2(C_72,A_74,B_73)
      | ~ v1_funct_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_368,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_365])).

tff(c_371,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_299,c_46,c_296,c_368])).

tff(c_8,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_391,plain,(
    ! [C_79,B_80,A_81] :
      ( m1_subset_1(k2_funct_1(C_79),k1_zfmisc_1(k2_zfmisc_1(B_80,A_81)))
      | k2_relset_1(A_81,B_80,C_79) != B_80
      | ~ v2_funct_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80)))
      | ~ v1_funct_2(C_79,A_81,B_80)
      | ~ v1_funct_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14,plain,(
    ! [C_6,A_4,B_5] :
      ( v1_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_427,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(k2_funct_1(C_82))
      | k2_relset_1(A_83,B_84,C_82) != B_84
      | ~ v2_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_82,A_83,B_84)
      | ~ v1_funct_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_391,c_14])).

tff(c_433,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_427])).

tff(c_437,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_299,c_46,c_296,c_433])).

tff(c_18,plain,(
    ! [C_9,A_7,B_8] :
      ( v4_relat_1(C_9,A_7)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_438,plain,(
    ! [C_85,B_86,A_87] :
      ( v4_relat_1(k2_funct_1(C_85),B_86)
      | k2_relset_1(A_87,B_86,C_85) != B_86
      | ~ v2_funct_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86)))
      | ~ v1_funct_2(C_85,A_87,B_86)
      | ~ v1_funct_1(C_85) ) ),
    inference(resolution,[status(thm)],[c_391,c_18])).

tff(c_444,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_438])).

tff(c_448,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_299,c_46,c_296,c_444])).

tff(c_10,plain,(
    ! [A_2] :
      ( k1_relat_1(k2_funct_1(A_2)) = k2_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [A_51] :
      ( k1_relat_1(k2_funct_1(A_51)) = k2_relat_1(A_51)
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [B_18] :
      ( v1_partfun1(B_18,k1_relat_1(B_18))
      | ~ v4_relat_1(B_18,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_348,plain,(
    ! [A_68] :
      ( v1_partfun1(k2_funct_1(A_68),k1_relat_1(k2_funct_1(A_68)))
      | ~ v4_relat_1(k2_funct_1(A_68),k2_relat_1(A_68))
      | ~ v1_relat_1(k2_funct_1(A_68))
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_26])).

tff(c_351,plain,(
    ! [A_2] :
      ( v1_partfun1(k2_funct_1(A_2),k2_relat_1(A_2))
      | ~ v4_relat_1(k2_funct_1(A_2),k2_relat_1(A_2))
      | ~ v1_relat_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_348])).

tff(c_460,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_448,c_351])).

tff(c_466,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_54,c_46,c_437,c_460])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(B_18) = A_17
      | ~ v1_partfun1(B_18,A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_463,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_448,c_28])).

tff(c_469,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_463])).

tff(c_471,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_469])).

tff(c_559,plain,(
    ! [A_103] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_103)),k1_relat_1(A_103))
      | ~ v4_relat_1(k2_funct_1(k2_funct_1(A_103)),k2_relat_1(k2_funct_1(A_103)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_103)))
      | ~ v2_funct_1(k2_funct_1(A_103))
      | ~ v1_funct_1(k2_funct_1(A_103))
      | ~ v1_relat_1(k2_funct_1(A_103))
      | ~ v2_funct_1(A_103)
      | ~ v1_funct_1(A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_348])).

tff(c_597,plain,(
    ! [A_109] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_109)),k1_relat_1(A_109))
      | ~ v4_relat_1(A_109,k2_relat_1(k2_funct_1(A_109)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_109)))
      | ~ v2_funct_1(k2_funct_1(A_109))
      | ~ v1_funct_1(k2_funct_1(A_109))
      | ~ v1_relat_1(k2_funct_1(A_109))
      | ~ v2_funct_1(A_109)
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109)
      | ~ v2_funct_1(A_109)
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_559])).

tff(c_600,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_597])).

tff(c_611,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_364,c_437,c_364,c_600])).

tff(c_612,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_611])).

tff(c_615,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_612])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_54,c_46,c_615])).

tff(c_621,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_519,plain,(
    ! [B_96,A_97,C_98] :
      ( k2_relset_1(B_96,A_97,k2_funct_1(C_98)) = k2_relat_1(k2_funct_1(C_98))
      | k2_relset_1(A_97,B_96,C_98) != B_96
      | ~ v2_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_2(C_98,A_97,B_96)
      | ~ v1_funct_1(C_98) ) ),
    inference(resolution,[status(thm)],[c_391,c_20])).

tff(c_525,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_519])).

tff(c_529,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_299,c_46,c_296,c_525])).

tff(c_36,plain,(
    ! [C_25,A_23,B_24] :
      ( v1_funct_1(k2_funct_1(C_25))
      | k2_relset_1(A_23,B_24,C_25) != B_24
      | ~ v2_funct_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_622,plain,(
    ! [C_110,B_111,A_112] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_110)))
      | k2_relset_1(B_111,A_112,k2_funct_1(C_110)) != A_112
      | ~ v2_funct_1(k2_funct_1(C_110))
      | ~ v1_funct_2(k2_funct_1(C_110),B_111,A_112)
      | ~ v1_funct_1(k2_funct_1(C_110))
      | k2_relset_1(A_112,B_111,C_110) != B_111
      | ~ v2_funct_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111)))
      | ~ v1_funct_2(C_110,A_112,B_111)
      | ~ v1_funct_1(C_110) ) ),
    inference(resolution,[status(thm)],[c_391,c_36])).

tff(c_628,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_622])).

tff(c_632,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_299,c_46,c_296,c_364,c_371,c_621,c_529,c_628])).

tff(c_633,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_632])).

tff(c_636,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_633])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_54,c_46,c_636])).

tff(c_642,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_648,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_529])).

tff(c_42,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_tops_2(A_28,B_29,C_30) = k2_funct_1(C_30)
      | ~ v2_funct_1(C_30)
      | k2_relset_1(A_28,B_29,C_30) != B_29
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_964,plain,(
    ! [B_126,A_127,C_128] :
      ( k2_tops_2(B_126,A_127,k2_funct_1(C_128)) = k2_funct_1(k2_funct_1(C_128))
      | ~ v2_funct_1(k2_funct_1(C_128))
      | k2_relset_1(B_126,A_127,k2_funct_1(C_128)) != A_127
      | ~ v1_funct_2(k2_funct_1(C_128),B_126,A_127)
      | ~ v1_funct_1(k2_funct_1(C_128))
      | k2_relset_1(A_127,B_126,C_128) != B_126
      | ~ v2_funct_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126)))
      | ~ v1_funct_2(C_128,A_127,B_126)
      | ~ v1_funct_1(C_128) ) ),
    inference(resolution,[status(thm)],[c_391,c_42])).

tff(c_970,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_964])).

tff(c_974,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_299,c_46,c_296,c_364,c_371,c_648,c_621,c_970])).

tff(c_372,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_tops_2(A_75,B_76,C_77) = k2_funct_1(C_77)
      | ~ v2_funct_1(C_77)
      | k2_relset_1(A_75,B_76,C_77) != B_76
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_2(C_77,A_75,B_76)
      | ~ v1_funct_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_375,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_372])).

tff(c_378,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_299,c_296,c_46,c_375])).

tff(c_44,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_99,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_69,c_68,c_68,c_68,c_44])).

tff(c_222,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_219,c_219,c_99])).

tff(c_297,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_291,c_291,c_222])).

tff(c_379,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_297])).

tff(c_1036,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_379])).

tff(c_1046,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1036])).

tff(c_1052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_54,c_46,c_507,c_1046])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.65  
% 3.94/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.65  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.94/1.65  
% 3.94/1.65  %Foreground sorts:
% 3.94/1.65  
% 3.94/1.65  
% 3.94/1.65  %Background operators:
% 3.94/1.65  
% 3.94/1.65  
% 3.94/1.65  %Foreground operators:
% 3.94/1.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.94/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.94/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.94/1.65  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.94/1.65  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.94/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.94/1.65  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.94/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.94/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.94/1.65  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.94/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.94/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.94/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.94/1.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.94/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.94/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.94/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.94/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.94/1.65  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.94/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.94/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.94/1.65  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.94/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.94/1.65  
% 3.94/1.68  tff(f_167, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.94/1.68  tff(f_125, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.94/1.68  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.94/1.68  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.94/1.68  tff(f_133, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.94/1.68  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.94/1.68  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.94/1.68  tff(f_83, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.94/1.68  tff(f_105, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 3.94/1.68  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.94/1.68  tff(f_121, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.94/1.68  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.94/1.68  tff(f_37, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.94/1.68  tff(f_145, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.94/1.68  tff(c_60, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.94/1.68  tff(c_61, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.94/1.68  tff(c_69, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_61])).
% 3.94/1.68  tff(c_56, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.94/1.68  tff(c_68, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_61])).
% 3.94/1.68  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.94/1.68  tff(c_79, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_68, c_50])).
% 3.94/1.68  tff(c_87, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.94/1.68  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_87])).
% 3.94/1.68  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.94/1.68  tff(c_46, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.94/1.68  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.94/1.68  tff(c_168, plain, (![A_55, B_56, C_57]: (k2_relset_1(A_55, B_56, C_57)=k2_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.94/1.68  tff(c_172, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_168])).
% 3.94/1.68  tff(c_48, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.94/1.68  tff(c_82, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_68, c_48])).
% 3.94/1.68  tff(c_173, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_82])).
% 3.94/1.68  tff(c_40, plain, (![A_27]: (~v1_xboole_0(k2_struct_0(A_27)) | ~l1_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.94/1.68  tff(c_187, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_173, c_40])).
% 3.94/1.68  tff(c_191, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_187])).
% 3.94/1.68  tff(c_192, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_191])).
% 3.94/1.68  tff(c_100, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.94/1.68  tff(c_104, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_79, c_100])).
% 3.94/1.68  tff(c_148, plain, (![B_52, A_53]: (k1_relat_1(B_52)=A_53 | ~v1_partfun1(B_52, A_53) | ~v4_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.94/1.68  tff(c_151, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_148])).
% 3.94/1.68  tff(c_154, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_151])).
% 3.94/1.68  tff(c_155, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_154])).
% 3.94/1.68  tff(c_52, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.94/1.68  tff(c_70, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_52])).
% 3.94/1.68  tff(c_80, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_70])).
% 3.94/1.68  tff(c_181, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_80])).
% 3.94/1.68  tff(c_182, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_79])).
% 3.94/1.68  tff(c_22, plain, (![C_16, A_13, B_14]: (v1_partfun1(C_16, A_13) | ~v1_funct_2(C_16, A_13, B_14) | ~v1_funct_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | v1_xboole_0(B_14))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.94/1.68  tff(c_201, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_182, c_22])).
% 3.94/1.68  tff(c_216, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_181, c_201])).
% 3.94/1.68  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_155, c_216])).
% 3.94/1.68  tff(c_219, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_154])).
% 3.94/1.68  tff(c_225, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_79])).
% 3.94/1.68  tff(c_286, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.94/1.68  tff(c_290, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_225, c_286])).
% 3.94/1.68  tff(c_223, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_82])).
% 3.94/1.68  tff(c_291, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_223])).
% 3.94/1.68  tff(c_224, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_80])).
% 3.94/1.68  tff(c_299, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_224])).
% 3.94/1.68  tff(c_298, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_291, c_225])).
% 3.94/1.68  tff(c_449, plain, (![A_88, B_89, C_90, D_91]: (r2_funct_2(A_88, B_89, C_90, C_90) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2(D_91, A_88, B_89) | ~v1_funct_1(D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2(C_90, A_88, B_89) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.94/1.68  tff(c_453, plain, (![C_90]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_90, C_90) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_90, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_90))), inference(resolution, [status(thm)], [c_298, c_449])).
% 3.94/1.68  tff(c_498, plain, (![C_92]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_92, C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_92, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_92))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_299, c_453])).
% 3.94/1.68  tff(c_503, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_498])).
% 3.94/1.68  tff(c_507, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_299, c_503])).
% 3.94/1.68  tff(c_12, plain, (![A_3]: (k2_funct_1(k2_funct_1(A_3))=A_3 | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.94/1.68  tff(c_296, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_290])).
% 3.94/1.68  tff(c_358, plain, (![C_69, A_70, B_71]: (v1_funct_1(k2_funct_1(C_69)) | k2_relset_1(A_70, B_71, C_69)!=B_71 | ~v2_funct_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_2(C_69, A_70, B_71) | ~v1_funct_1(C_69))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.68  tff(c_361, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_358])).
% 3.94/1.68  tff(c_364, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_299, c_46, c_296, c_361])).
% 3.94/1.68  tff(c_365, plain, (![C_72, B_73, A_74]: (v1_funct_2(k2_funct_1(C_72), B_73, A_74) | k2_relset_1(A_74, B_73, C_72)!=B_73 | ~v2_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))) | ~v1_funct_2(C_72, A_74, B_73) | ~v1_funct_1(C_72))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.68  tff(c_368, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_365])).
% 3.94/1.68  tff(c_371, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_299, c_46, c_296, c_368])).
% 3.94/1.68  tff(c_8, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.94/1.68  tff(c_2, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.94/1.68  tff(c_391, plain, (![C_79, B_80, A_81]: (m1_subset_1(k2_funct_1(C_79), k1_zfmisc_1(k2_zfmisc_1(B_80, A_81))) | k2_relset_1(A_81, B_80, C_79)!=B_80 | ~v2_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_2(C_79, A_81, B_80) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.68  tff(c_14, plain, (![C_6, A_4, B_5]: (v1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.94/1.68  tff(c_427, plain, (![C_82, A_83, B_84]: (v1_relat_1(k2_funct_1(C_82)) | k2_relset_1(A_83, B_84, C_82)!=B_84 | ~v2_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_82, A_83, B_84) | ~v1_funct_1(C_82))), inference(resolution, [status(thm)], [c_391, c_14])).
% 3.94/1.68  tff(c_433, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_427])).
% 3.94/1.68  tff(c_437, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_299, c_46, c_296, c_433])).
% 3.94/1.68  tff(c_18, plain, (![C_9, A_7, B_8]: (v4_relat_1(C_9, A_7) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.94/1.68  tff(c_438, plain, (![C_85, B_86, A_87]: (v4_relat_1(k2_funct_1(C_85), B_86) | k2_relset_1(A_87, B_86, C_85)!=B_86 | ~v2_funct_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))) | ~v1_funct_2(C_85, A_87, B_86) | ~v1_funct_1(C_85))), inference(resolution, [status(thm)], [c_391, c_18])).
% 3.94/1.68  tff(c_444, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_438])).
% 3.94/1.68  tff(c_448, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_299, c_46, c_296, c_444])).
% 3.94/1.68  tff(c_10, plain, (![A_2]: (k1_relat_1(k2_funct_1(A_2))=k2_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.94/1.68  tff(c_133, plain, (![A_51]: (k1_relat_1(k2_funct_1(A_51))=k2_relat_1(A_51) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.94/1.68  tff(c_26, plain, (![B_18]: (v1_partfun1(B_18, k1_relat_1(B_18)) | ~v4_relat_1(B_18, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.94/1.68  tff(c_348, plain, (![A_68]: (v1_partfun1(k2_funct_1(A_68), k1_relat_1(k2_funct_1(A_68))) | ~v4_relat_1(k2_funct_1(A_68), k2_relat_1(A_68)) | ~v1_relat_1(k2_funct_1(A_68)) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(superposition, [status(thm), theory('equality')], [c_133, c_26])).
% 3.94/1.68  tff(c_351, plain, (![A_2]: (v1_partfun1(k2_funct_1(A_2), k2_relat_1(A_2)) | ~v4_relat_1(k2_funct_1(A_2), k2_relat_1(A_2)) | ~v1_relat_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_10, c_348])).
% 3.94/1.68  tff(c_460, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_448, c_351])).
% 3.94/1.68  tff(c_466, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_54, c_46, c_437, c_460])).
% 3.94/1.68  tff(c_28, plain, (![B_18, A_17]: (k1_relat_1(B_18)=A_17 | ~v1_partfun1(B_18, A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.94/1.68  tff(c_463, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_448, c_28])).
% 3.94/1.68  tff(c_469, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_463])).
% 3.94/1.68  tff(c_471, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_469])).
% 3.94/1.68  tff(c_559, plain, (![A_103]: (v1_partfun1(k2_funct_1(k2_funct_1(A_103)), k1_relat_1(A_103)) | ~v4_relat_1(k2_funct_1(k2_funct_1(A_103)), k2_relat_1(k2_funct_1(A_103))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_103))) | ~v2_funct_1(k2_funct_1(A_103)) | ~v1_funct_1(k2_funct_1(A_103)) | ~v1_relat_1(k2_funct_1(A_103)) | ~v2_funct_1(A_103) | ~v1_funct_1(A_103) | ~v1_relat_1(A_103))), inference(superposition, [status(thm), theory('equality')], [c_12, c_348])).
% 3.94/1.68  tff(c_597, plain, (![A_109]: (v1_partfun1(k2_funct_1(k2_funct_1(A_109)), k1_relat_1(A_109)) | ~v4_relat_1(A_109, k2_relat_1(k2_funct_1(A_109))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_109))) | ~v2_funct_1(k2_funct_1(A_109)) | ~v1_funct_1(k2_funct_1(A_109)) | ~v1_relat_1(k2_funct_1(A_109)) | ~v2_funct_1(A_109) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109) | ~v2_funct_1(A_109) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_12, c_559])).
% 3.94/1.68  tff(c_600, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_471, c_597])).
% 3.94/1.68  tff(c_611, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_364, c_437, c_364, c_600])).
% 3.94/1.68  tff(c_612, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_611])).
% 3.94/1.68  tff(c_615, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_612])).
% 3.94/1.68  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_54, c_46, c_615])).
% 3.94/1.68  tff(c_621, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_611])).
% 3.94/1.68  tff(c_20, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.94/1.68  tff(c_519, plain, (![B_96, A_97, C_98]: (k2_relset_1(B_96, A_97, k2_funct_1(C_98))=k2_relat_1(k2_funct_1(C_98)) | k2_relset_1(A_97, B_96, C_98)!=B_96 | ~v2_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_2(C_98, A_97, B_96) | ~v1_funct_1(C_98))), inference(resolution, [status(thm)], [c_391, c_20])).
% 3.94/1.68  tff(c_525, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_519])).
% 3.94/1.68  tff(c_529, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_299, c_46, c_296, c_525])).
% 3.94/1.68  tff(c_36, plain, (![C_25, A_23, B_24]: (v1_funct_1(k2_funct_1(C_25)) | k2_relset_1(A_23, B_24, C_25)!=B_24 | ~v2_funct_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.68  tff(c_622, plain, (![C_110, B_111, A_112]: (v1_funct_1(k2_funct_1(k2_funct_1(C_110))) | k2_relset_1(B_111, A_112, k2_funct_1(C_110))!=A_112 | ~v2_funct_1(k2_funct_1(C_110)) | ~v1_funct_2(k2_funct_1(C_110), B_111, A_112) | ~v1_funct_1(k2_funct_1(C_110)) | k2_relset_1(A_112, B_111, C_110)!=B_111 | ~v2_funct_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))) | ~v1_funct_2(C_110, A_112, B_111) | ~v1_funct_1(C_110))), inference(resolution, [status(thm)], [c_391, c_36])).
% 3.94/1.68  tff(c_628, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_622])).
% 3.94/1.68  tff(c_632, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_299, c_46, c_296, c_364, c_371, c_621, c_529, c_628])).
% 3.94/1.68  tff(c_633, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_632])).
% 3.94/1.68  tff(c_636, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_633])).
% 3.94/1.68  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_54, c_46, c_636])).
% 3.94/1.68  tff(c_642, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_632])).
% 3.94/1.68  tff(c_648, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_529])).
% 3.94/1.68  tff(c_42, plain, (![A_28, B_29, C_30]: (k2_tops_2(A_28, B_29, C_30)=k2_funct_1(C_30) | ~v2_funct_1(C_30) | k2_relset_1(A_28, B_29, C_30)!=B_29 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.94/1.68  tff(c_964, plain, (![B_126, A_127, C_128]: (k2_tops_2(B_126, A_127, k2_funct_1(C_128))=k2_funct_1(k2_funct_1(C_128)) | ~v2_funct_1(k2_funct_1(C_128)) | k2_relset_1(B_126, A_127, k2_funct_1(C_128))!=A_127 | ~v1_funct_2(k2_funct_1(C_128), B_126, A_127) | ~v1_funct_1(k2_funct_1(C_128)) | k2_relset_1(A_127, B_126, C_128)!=B_126 | ~v2_funct_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))) | ~v1_funct_2(C_128, A_127, B_126) | ~v1_funct_1(C_128))), inference(resolution, [status(thm)], [c_391, c_42])).
% 3.94/1.68  tff(c_970, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_964])).
% 3.94/1.68  tff(c_974, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_299, c_46, c_296, c_364, c_371, c_648, c_621, c_970])).
% 3.94/1.68  tff(c_372, plain, (![A_75, B_76, C_77]: (k2_tops_2(A_75, B_76, C_77)=k2_funct_1(C_77) | ~v2_funct_1(C_77) | k2_relset_1(A_75, B_76, C_77)!=B_76 | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_2(C_77, A_75, B_76) | ~v1_funct_1(C_77))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.94/1.68  tff(c_375, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_372])).
% 3.94/1.68  tff(c_378, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_299, c_296, c_46, c_375])).
% 3.94/1.68  tff(c_44, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.94/1.68  tff(c_99, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_69, c_68, c_68, c_68, c_44])).
% 3.94/1.68  tff(c_222, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_219, c_219, c_99])).
% 3.94/1.68  tff(c_297, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_291, c_291, c_222])).
% 3.94/1.68  tff(c_379, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_378, c_297])).
% 3.94/1.68  tff(c_1036, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_974, c_379])).
% 3.94/1.68  tff(c_1046, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_1036])).
% 3.94/1.68  tff(c_1052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_54, c_46, c_507, c_1046])).
% 3.94/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.68  
% 3.94/1.68  Inference rules
% 3.94/1.68  ----------------------
% 3.94/1.68  #Ref     : 0
% 3.94/1.68  #Sup     : 219
% 3.94/1.68  #Fact    : 0
% 3.94/1.68  #Define  : 0
% 3.94/1.68  #Split   : 11
% 3.94/1.68  #Chain   : 0
% 3.94/1.68  #Close   : 0
% 3.94/1.68  
% 3.94/1.68  Ordering : KBO
% 3.94/1.68  
% 3.94/1.68  Simplification rules
% 3.94/1.68  ----------------------
% 3.94/1.68  #Subsume      : 5
% 3.94/1.68  #Demod        : 412
% 3.94/1.68  #Tautology    : 117
% 3.94/1.68  #SimpNegUnit  : 5
% 3.94/1.68  #BackRed      : 25
% 3.94/1.68  
% 3.94/1.68  #Partial instantiations: 0
% 3.94/1.68  #Strategies tried      : 1
% 3.94/1.68  
% 3.94/1.68  Timing (in seconds)
% 3.94/1.68  ----------------------
% 3.94/1.68  Preprocessing        : 0.36
% 3.94/1.68  Parsing              : 0.20
% 3.94/1.68  CNF conversion       : 0.02
% 3.94/1.68  Main loop            : 0.50
% 3.94/1.68  Inferencing          : 0.17
% 3.94/1.68  Reduction            : 0.17
% 3.94/1.68  Demodulation         : 0.12
% 3.94/1.68  BG Simplification    : 0.03
% 3.94/1.68  Subsumption          : 0.10
% 3.94/1.68  Abstraction          : 0.02
% 3.94/1.68  MUC search           : 0.00
% 3.94/1.68  Cooper               : 0.00
% 3.94/1.68  Total                : 0.92
% 3.94/1.68  Index Insertion      : 0.00
% 3.94/1.68  Index Deletion       : 0.00
% 3.94/1.68  Index Matching       : 0.00
% 3.94/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
