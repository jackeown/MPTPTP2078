%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:30 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  152 (23453 expanded)
%              Number of leaves         :   41 (8169 expanded)
%              Depth                    :   26
%              Number of atoms          :  407 (68250 expanded)
%              Number of equality atoms :   70 (15311 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_145,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

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

tff(c_99,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_103,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_99])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_46,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_81,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(u1_struct_0(A_36))
      | ~ l1_struct_0(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_87,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_81])).

tff(c_91,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_87])).

tff(c_92,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_91])).

tff(c_104,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_108,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_79,c_104])).

tff(c_160,plain,(
    ! [B_52,A_53] :
      ( k1_relat_1(B_52) = A_53
      | ~ v1_partfun1(B_52,A_53)
      | ~ v4_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_163,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_160])).

tff(c_166,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_163])).

tff(c_167,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_70,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_52])).

tff(c_80,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_70])).

tff(c_190,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_partfun1(C_58,A_59)
      | ~ v1_funct_2(C_58,A_59,B_60)
      | ~ v1_funct_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | v1_xboole_0(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_193,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_79,c_190])).

tff(c_196,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_80,c_193])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_167,c_196])).

tff(c_199,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_206,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_79])).

tff(c_267,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_271,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_206,c_267])).

tff(c_48,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_94,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_68,c_48])).

tff(c_203,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_94])).

tff(c_272,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_203])).

tff(c_205,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_80])).

tff(c_279,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_205])).

tff(c_280,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_206])).

tff(c_442,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( r2_funct_2(A_91,B_92,C_93,C_93)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_2(D_94,A_91,B_92)
      | ~ v1_funct_1(D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_2(C_93,A_91,B_92)
      | ~ v1_funct_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_446,plain,(
    ! [C_93] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_93,C_93)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_93,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_280,c_442])).

tff(c_491,plain,(
    ! [C_95] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_95,C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_95,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279,c_446])).

tff(c_496,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_491])).

tff(c_500,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279,c_496])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_funct_1(k2_funct_1(A_3)) = A_3
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_278,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_271])).

tff(c_330,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_funct_1(k2_funct_1(C_68))
      | k2_relset_1(A_69,B_70,C_68) != B_70
      | ~ v2_funct_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_2(C_68,A_69,B_70)
      | ~ v1_funct_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_333,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_330])).

tff(c_336,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279,c_46,c_278,c_333])).

tff(c_347,plain,(
    ! [C_72,B_73,A_74] :
      ( v1_funct_2(k2_funct_1(C_72),B_73,A_74)
      | k2_relset_1(A_74,B_73,C_72) != B_73
      | ~ v2_funct_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73)))
      | ~ v1_funct_2(C_72,A_74,B_73)
      | ~ v1_funct_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_350,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_347])).

tff(c_353,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279,c_46,c_278,c_350])).

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

tff(c_373,plain,(
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

tff(c_409,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(k2_funct_1(C_82))
      | k2_relset_1(A_83,B_84,C_82) != B_84
      | ~ v2_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84)))
      | ~ v1_funct_2(C_82,A_83,B_84)
      | ~ v1_funct_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_373,c_14])).

tff(c_415,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_409])).

tff(c_419,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279,c_46,c_278,c_415])).

tff(c_18,plain,(
    ! [C_9,A_7,B_8] :
      ( v4_relat_1(C_9,A_7)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_431,plain,(
    ! [C_88,B_89,A_90] :
      ( v4_relat_1(k2_funct_1(C_88),B_89)
      | k2_relset_1(A_90,B_89,C_88) != B_89
      | ~ v2_funct_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89)))
      | ~ v1_funct_2(C_88,A_90,B_89)
      | ~ v1_funct_1(C_88) ) ),
    inference(resolution,[status(thm)],[c_373,c_18])).

tff(c_437,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_431])).

tff(c_441,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279,c_46,c_278,c_437])).

tff(c_10,plain,(
    ! [A_2] :
      ( k1_relat_1(k2_funct_1(A_2)) = k2_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_145,plain,(
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

tff(c_337,plain,(
    ! [A_71] :
      ( v1_partfun1(k2_funct_1(A_71),k1_relat_1(k2_funct_1(A_71)))
      | ~ v4_relat_1(k2_funct_1(A_71),k2_relat_1(A_71))
      | ~ v1_relat_1(k2_funct_1(A_71))
      | ~ v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_26])).

tff(c_340,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_10,c_337])).

tff(c_453,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_441,c_340])).

tff(c_459,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_54,c_46,c_419,c_453])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(B_18) = A_17
      | ~ v1_partfun1(B_18,A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_456,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_441,c_28])).

tff(c_462,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_456])).

tff(c_464,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_462])).

tff(c_529,plain,(
    ! [A_100] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_100)),k1_relat_1(A_100))
      | ~ v4_relat_1(k2_funct_1(k2_funct_1(A_100)),k2_relat_1(k2_funct_1(A_100)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_100)))
      | ~ v2_funct_1(k2_funct_1(A_100))
      | ~ v1_funct_1(k2_funct_1(A_100))
      | ~ v1_relat_1(k2_funct_1(A_100))
      | ~ v2_funct_1(A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_337])).

tff(c_562,plain,(
    ! [A_107] :
      ( v1_partfun1(k2_funct_1(k2_funct_1(A_107)),k1_relat_1(A_107))
      | ~ v4_relat_1(A_107,k2_relat_1(k2_funct_1(A_107)))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(A_107)))
      | ~ v2_funct_1(k2_funct_1(A_107))
      | ~ v1_funct_1(k2_funct_1(A_107))
      | ~ v1_relat_1(k2_funct_1(A_107))
      | ~ v2_funct_1(A_107)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107)
      | ~ v2_funct_1(A_107)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_529])).

tff(c_565,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_464,c_562])).

tff(c_576,plain,
    ( v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3'))
    | ~ v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_336,c_419,c_336,c_565])).

tff(c_577,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_587,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_577])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_54,c_46,c_587])).

tff(c_593,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_501,plain,(
    ! [B_96,A_97,C_98] :
      ( k2_relset_1(B_96,A_97,k2_funct_1(C_98)) = k2_relat_1(k2_funct_1(C_98))
      | k2_relset_1(A_97,B_96,C_98) != B_96
      | ~ v2_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_2(C_98,A_97,B_96)
      | ~ v1_funct_1(C_98) ) ),
    inference(resolution,[status(thm)],[c_373,c_20])).

tff(c_507,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_501])).

tff(c_511,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279,c_46,c_278,c_507])).

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
    ! [C_109,B_110,A_111] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_109)))
      | k2_relset_1(B_110,A_111,k2_funct_1(C_109)) != A_111
      | ~ v2_funct_1(k2_funct_1(C_109))
      | ~ v1_funct_2(k2_funct_1(C_109),B_110,A_111)
      | ~ v1_funct_1(k2_funct_1(C_109))
      | k2_relset_1(A_111,B_110,C_109) != B_110
      | ~ v2_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110)))
      | ~ v1_funct_2(C_109,A_111,B_110)
      | ~ v1_funct_1(C_109) ) ),
    inference(resolution,[status(thm)],[c_373,c_36])).

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
    inference(resolution,[status(thm)],[c_280,c_622])).

tff(c_632,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279,c_46,c_278,c_336,c_353,c_593,c_511,c_628])).

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
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_54,c_46,c_636])).

tff(c_642,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_632])).

tff(c_648,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_511])).

tff(c_42,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_tops_2(A_28,B_29,C_30) = k2_funct_1(C_30)
      | ~ v2_funct_1(C_30)
      | k2_relset_1(A_28,B_29,C_30) != B_29
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_889,plain,(
    ! [B_121,A_122,C_123] :
      ( k2_tops_2(B_121,A_122,k2_funct_1(C_123)) = k2_funct_1(k2_funct_1(C_123))
      | ~ v2_funct_1(k2_funct_1(C_123))
      | k2_relset_1(B_121,A_122,k2_funct_1(C_123)) != A_122
      | ~ v1_funct_2(k2_funct_1(C_123),B_121,A_122)
      | ~ v1_funct_1(k2_funct_1(C_123))
      | k2_relset_1(A_122,B_121,C_123) != B_121
      | ~ v2_funct_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_2(C_123,A_122,B_121)
      | ~ v1_funct_1(C_123) ) ),
    inference(resolution,[status(thm)],[c_373,c_42])).

tff(c_895,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_889])).

tff(c_899,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279,c_46,c_278,c_336,c_353,c_648,c_593,c_895])).

tff(c_354,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_tops_2(A_75,B_76,C_77) = k2_funct_1(C_77)
      | ~ v2_funct_1(C_77)
      | k2_relset_1(A_75,B_76,C_77) != B_76
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_funct_2(C_77,A_75,B_76)
      | ~ v1_funct_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_357,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_354])).

tff(c_360,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279,c_278,c_46,c_357])).

tff(c_44,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_109,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_69,c_68,c_68,c_68,c_44])).

tff(c_202,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_199,c_199,c_109])).

tff(c_277,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_272,c_272,c_202])).

tff(c_361,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_277])).

tff(c_910,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_361])).

tff(c_917,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_910])).

tff(c_920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_54,c_46,c_500,c_917])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.55  
% 3.65/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.55  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.65/1.55  
% 3.65/1.55  %Foreground sorts:
% 3.65/1.55  
% 3.65/1.55  
% 3.65/1.55  %Background operators:
% 3.65/1.55  
% 3.65/1.55  
% 3.65/1.55  %Foreground operators:
% 3.65/1.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.65/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.65/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.65/1.55  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.65/1.55  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.65/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.65/1.55  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.65/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.65/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.65/1.55  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.65/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.65/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.65/1.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.65/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.65/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.65/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.65/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.65/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.65/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.65/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.65/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.65/1.55  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.65/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.55  
% 3.65/1.58  tff(f_167, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 3.65/1.58  tff(f_125, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.65/1.58  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.65/1.58  tff(f_133, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.65/1.58  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.65/1.58  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.65/1.58  tff(f_83, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.65/1.58  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.65/1.58  tff(f_105, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 3.65/1.58  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 3.65/1.58  tff(f_121, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 3.65/1.58  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.65/1.58  tff(f_37, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.65/1.58  tff(f_145, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.65/1.58  tff(c_60, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.65/1.58  tff(c_61, plain, (![A_35]: (u1_struct_0(A_35)=k2_struct_0(A_35) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.65/1.58  tff(c_69, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_61])).
% 3.65/1.58  tff(c_56, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.65/1.58  tff(c_68, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_61])).
% 3.65/1.58  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.65/1.58  tff(c_79, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_68, c_50])).
% 3.65/1.58  tff(c_99, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.65/1.58  tff(c_103, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_99])).
% 3.65/1.58  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.65/1.58  tff(c_46, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.65/1.58  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.65/1.58  tff(c_81, plain, (![A_36]: (~v1_xboole_0(u1_struct_0(A_36)) | ~l1_struct_0(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.65/1.58  tff(c_87, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_68, c_81])).
% 3.65/1.58  tff(c_91, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_87])).
% 3.65/1.58  tff(c_92, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_91])).
% 3.65/1.58  tff(c_104, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.65/1.58  tff(c_108, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_79, c_104])).
% 3.65/1.58  tff(c_160, plain, (![B_52, A_53]: (k1_relat_1(B_52)=A_53 | ~v1_partfun1(B_52, A_53) | ~v4_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.65/1.58  tff(c_163, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_160])).
% 3.65/1.58  tff(c_166, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_163])).
% 3.65/1.58  tff(c_167, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_166])).
% 3.65/1.58  tff(c_52, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.65/1.58  tff(c_70, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_52])).
% 3.65/1.58  tff(c_80, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_70])).
% 3.65/1.58  tff(c_190, plain, (![C_58, A_59, B_60]: (v1_partfun1(C_58, A_59) | ~v1_funct_2(C_58, A_59, B_60) | ~v1_funct_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | v1_xboole_0(B_60))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.65/1.58  tff(c_193, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_79, c_190])).
% 3.65/1.58  tff(c_196, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_80, c_193])).
% 3.65/1.58  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_167, c_196])).
% 3.65/1.58  tff(c_199, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_166])).
% 3.65/1.58  tff(c_206, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_79])).
% 3.65/1.58  tff(c_267, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.65/1.58  tff(c_271, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_206, c_267])).
% 3.65/1.58  tff(c_48, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.65/1.58  tff(c_94, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_68, c_48])).
% 3.65/1.58  tff(c_203, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_94])).
% 3.65/1.58  tff(c_272, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_203])).
% 3.65/1.58  tff(c_205, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_80])).
% 3.65/1.58  tff(c_279, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_205])).
% 3.65/1.58  tff(c_280, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_206])).
% 3.65/1.58  tff(c_442, plain, (![A_91, B_92, C_93, D_94]: (r2_funct_2(A_91, B_92, C_93, C_93) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_2(D_94, A_91, B_92) | ~v1_funct_1(D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_2(C_93, A_91, B_92) | ~v1_funct_1(C_93))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.65/1.58  tff(c_446, plain, (![C_93]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_93, C_93) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_93, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_93))), inference(resolution, [status(thm)], [c_280, c_442])).
% 3.65/1.58  tff(c_491, plain, (![C_95]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_95, C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_95, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_95))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279, c_446])).
% 3.65/1.58  tff(c_496, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_491])).
% 3.65/1.58  tff(c_500, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279, c_496])).
% 3.65/1.58  tff(c_12, plain, (![A_3]: (k2_funct_1(k2_funct_1(A_3))=A_3 | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.65/1.58  tff(c_278, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_271])).
% 3.65/1.58  tff(c_330, plain, (![C_68, A_69, B_70]: (v1_funct_1(k2_funct_1(C_68)) | k2_relset_1(A_69, B_70, C_68)!=B_70 | ~v2_funct_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_2(C_68, A_69, B_70) | ~v1_funct_1(C_68))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.65/1.58  tff(c_333, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_330])).
% 3.65/1.58  tff(c_336, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279, c_46, c_278, c_333])).
% 3.65/1.58  tff(c_347, plain, (![C_72, B_73, A_74]: (v1_funct_2(k2_funct_1(C_72), B_73, A_74) | k2_relset_1(A_74, B_73, C_72)!=B_73 | ~v2_funct_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))) | ~v1_funct_2(C_72, A_74, B_73) | ~v1_funct_1(C_72))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.65/1.58  tff(c_350, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_347])).
% 3.65/1.58  tff(c_353, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279, c_46, c_278, c_350])).
% 3.65/1.58  tff(c_8, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/1.58  tff(c_2, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.65/1.58  tff(c_373, plain, (![C_79, B_80, A_81]: (m1_subset_1(k2_funct_1(C_79), k1_zfmisc_1(k2_zfmisc_1(B_80, A_81))) | k2_relset_1(A_81, B_80, C_79)!=B_80 | ~v2_funct_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))) | ~v1_funct_2(C_79, A_81, B_80) | ~v1_funct_1(C_79))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.65/1.58  tff(c_14, plain, (![C_6, A_4, B_5]: (v1_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.65/1.58  tff(c_409, plain, (![C_82, A_83, B_84]: (v1_relat_1(k2_funct_1(C_82)) | k2_relset_1(A_83, B_84, C_82)!=B_84 | ~v2_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))) | ~v1_funct_2(C_82, A_83, B_84) | ~v1_funct_1(C_82))), inference(resolution, [status(thm)], [c_373, c_14])).
% 3.65/1.58  tff(c_415, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_409])).
% 3.65/1.58  tff(c_419, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279, c_46, c_278, c_415])).
% 3.65/1.58  tff(c_18, plain, (![C_9, A_7, B_8]: (v4_relat_1(C_9, A_7) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.65/1.58  tff(c_431, plain, (![C_88, B_89, A_90]: (v4_relat_1(k2_funct_1(C_88), B_89) | k2_relset_1(A_90, B_89, C_88)!=B_89 | ~v2_funct_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))) | ~v1_funct_2(C_88, A_90, B_89) | ~v1_funct_1(C_88))), inference(resolution, [status(thm)], [c_373, c_18])).
% 3.65/1.58  tff(c_437, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_431])).
% 3.65/1.58  tff(c_441, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279, c_46, c_278, c_437])).
% 3.65/1.58  tff(c_10, plain, (![A_2]: (k1_relat_1(k2_funct_1(A_2))=k2_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/1.58  tff(c_145, plain, (![A_51]: (k1_relat_1(k2_funct_1(A_51))=k2_relat_1(A_51) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.65/1.58  tff(c_26, plain, (![B_18]: (v1_partfun1(B_18, k1_relat_1(B_18)) | ~v4_relat_1(B_18, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.65/1.58  tff(c_337, plain, (![A_71]: (v1_partfun1(k2_funct_1(A_71), k1_relat_1(k2_funct_1(A_71))) | ~v4_relat_1(k2_funct_1(A_71), k2_relat_1(A_71)) | ~v1_relat_1(k2_funct_1(A_71)) | ~v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_145, c_26])).
% 3.65/1.58  tff(c_340, plain, (![A_2]: (v1_partfun1(k2_funct_1(A_2), k2_relat_1(A_2)) | ~v4_relat_1(k2_funct_1(A_2), k2_relat_1(A_2)) | ~v1_relat_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_10, c_337])).
% 3.65/1.58  tff(c_453, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_441, c_340])).
% 3.65/1.58  tff(c_459, plain, (v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_54, c_46, c_419, c_453])).
% 3.65/1.58  tff(c_28, plain, (![B_18, A_17]: (k1_relat_1(B_18)=A_17 | ~v1_partfun1(B_18, A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.65/1.58  tff(c_456, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_441, c_28])).
% 3.65/1.58  tff(c_462, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_456])).
% 3.65/1.58  tff(c_464, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_462])).
% 3.65/1.58  tff(c_529, plain, (![A_100]: (v1_partfun1(k2_funct_1(k2_funct_1(A_100)), k1_relat_1(A_100)) | ~v4_relat_1(k2_funct_1(k2_funct_1(A_100)), k2_relat_1(k2_funct_1(A_100))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_100))) | ~v2_funct_1(k2_funct_1(A_100)) | ~v1_funct_1(k2_funct_1(A_100)) | ~v1_relat_1(k2_funct_1(A_100)) | ~v2_funct_1(A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_12, c_337])).
% 3.65/1.58  tff(c_562, plain, (![A_107]: (v1_partfun1(k2_funct_1(k2_funct_1(A_107)), k1_relat_1(A_107)) | ~v4_relat_1(A_107, k2_relat_1(k2_funct_1(A_107))) | ~v1_relat_1(k2_funct_1(k2_funct_1(A_107))) | ~v2_funct_1(k2_funct_1(A_107)) | ~v1_funct_1(k2_funct_1(A_107)) | ~v1_relat_1(k2_funct_1(A_107)) | ~v2_funct_1(A_107) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107) | ~v2_funct_1(A_107) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_12, c_529])).
% 3.65/1.58  tff(c_565, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_464, c_562])).
% 3.65/1.58  tff(c_576, plain, (v1_partfun1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3')) | ~v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_419, c_336, c_419, c_336, c_565])).
% 3.65/1.58  tff(c_577, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_576])).
% 3.65/1.58  tff(c_587, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_577])).
% 3.65/1.58  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_54, c_46, c_587])).
% 3.65/1.58  tff(c_593, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_576])).
% 3.65/1.58  tff(c_20, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.65/1.58  tff(c_501, plain, (![B_96, A_97, C_98]: (k2_relset_1(B_96, A_97, k2_funct_1(C_98))=k2_relat_1(k2_funct_1(C_98)) | k2_relset_1(A_97, B_96, C_98)!=B_96 | ~v2_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_2(C_98, A_97, B_96) | ~v1_funct_1(C_98))), inference(resolution, [status(thm)], [c_373, c_20])).
% 3.65/1.58  tff(c_507, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_501])).
% 3.65/1.58  tff(c_511, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279, c_46, c_278, c_507])).
% 3.65/1.58  tff(c_36, plain, (![C_25, A_23, B_24]: (v1_funct_1(k2_funct_1(C_25)) | k2_relset_1(A_23, B_24, C_25)!=B_24 | ~v2_funct_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.65/1.58  tff(c_622, plain, (![C_109, B_110, A_111]: (v1_funct_1(k2_funct_1(k2_funct_1(C_109))) | k2_relset_1(B_110, A_111, k2_funct_1(C_109))!=A_111 | ~v2_funct_1(k2_funct_1(C_109)) | ~v1_funct_2(k2_funct_1(C_109), B_110, A_111) | ~v1_funct_1(k2_funct_1(C_109)) | k2_relset_1(A_111, B_110, C_109)!=B_110 | ~v2_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))) | ~v1_funct_2(C_109, A_111, B_110) | ~v1_funct_1(C_109))), inference(resolution, [status(thm)], [c_373, c_36])).
% 3.65/1.58  tff(c_628, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_622])).
% 3.65/1.58  tff(c_632, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279, c_46, c_278, c_336, c_353, c_593, c_511, c_628])).
% 3.65/1.58  tff(c_633, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_632])).
% 3.65/1.58  tff(c_636, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_633])).
% 3.65/1.58  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_54, c_46, c_636])).
% 3.65/1.58  tff(c_642, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_632])).
% 3.65/1.58  tff(c_648, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_511])).
% 3.65/1.58  tff(c_42, plain, (![A_28, B_29, C_30]: (k2_tops_2(A_28, B_29, C_30)=k2_funct_1(C_30) | ~v2_funct_1(C_30) | k2_relset_1(A_28, B_29, C_30)!=B_29 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.65/1.58  tff(c_889, plain, (![B_121, A_122, C_123]: (k2_tops_2(B_121, A_122, k2_funct_1(C_123))=k2_funct_1(k2_funct_1(C_123)) | ~v2_funct_1(k2_funct_1(C_123)) | k2_relset_1(B_121, A_122, k2_funct_1(C_123))!=A_122 | ~v1_funct_2(k2_funct_1(C_123), B_121, A_122) | ~v1_funct_1(k2_funct_1(C_123)) | k2_relset_1(A_122, B_121, C_123)!=B_121 | ~v2_funct_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_2(C_123, A_122, B_121) | ~v1_funct_1(C_123))), inference(resolution, [status(thm)], [c_373, c_42])).
% 3.65/1.58  tff(c_895, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_889])).
% 3.65/1.58  tff(c_899, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279, c_46, c_278, c_336, c_353, c_648, c_593, c_895])).
% 3.65/1.58  tff(c_354, plain, (![A_75, B_76, C_77]: (k2_tops_2(A_75, B_76, C_77)=k2_funct_1(C_77) | ~v2_funct_1(C_77) | k2_relset_1(A_75, B_76, C_77)!=B_76 | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_funct_2(C_77, A_75, B_76) | ~v1_funct_1(C_77))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.65/1.58  tff(c_357, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_354])).
% 3.65/1.58  tff(c_360, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279, c_278, c_46, c_357])).
% 3.65/1.58  tff(c_44, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 3.65/1.58  tff(c_109, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_69, c_68, c_68, c_68, c_44])).
% 3.65/1.58  tff(c_202, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_199, c_199, c_109])).
% 3.65/1.58  tff(c_277, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_272, c_272, c_202])).
% 3.65/1.58  tff(c_361, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_277])).
% 3.65/1.58  tff(c_910, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_899, c_361])).
% 3.65/1.58  tff(c_917, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_910])).
% 3.65/1.58  tff(c_920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_54, c_46, c_500, c_917])).
% 3.65/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.58  
% 3.65/1.58  Inference rules
% 3.65/1.58  ----------------------
% 3.65/1.58  #Ref     : 0
% 3.65/1.58  #Sup     : 188
% 3.65/1.58  #Fact    : 0
% 3.65/1.58  #Define  : 0
% 3.65/1.58  #Split   : 10
% 3.65/1.58  #Chain   : 0
% 3.65/1.58  #Close   : 0
% 3.65/1.58  
% 3.65/1.58  Ordering : KBO
% 3.65/1.58  
% 3.65/1.58  Simplification rules
% 3.65/1.58  ----------------------
% 3.65/1.58  #Subsume      : 5
% 3.65/1.58  #Demod        : 312
% 3.65/1.58  #Tautology    : 96
% 3.65/1.58  #SimpNegUnit  : 5
% 3.65/1.58  #BackRed      : 21
% 3.65/1.58  
% 3.65/1.58  #Partial instantiations: 0
% 3.65/1.58  #Strategies tried      : 1
% 3.65/1.58  
% 3.65/1.58  Timing (in seconds)
% 3.65/1.58  ----------------------
% 3.65/1.58  Preprocessing        : 0.35
% 3.65/1.58  Parsing              : 0.19
% 3.65/1.59  CNF conversion       : 0.02
% 3.65/1.59  Main loop            : 0.44
% 3.65/1.59  Inferencing          : 0.15
% 3.65/1.59  Reduction            : 0.14
% 3.65/1.59  Demodulation         : 0.11
% 3.65/1.59  BG Simplification    : 0.02
% 3.65/1.59  Subsumption          : 0.08
% 3.65/1.59  Abstraction          : 0.02
% 3.65/1.59  MUC search           : 0.00
% 3.65/1.59  Cooper               : 0.00
% 3.65/1.59  Total                : 0.84
% 3.65/1.59  Index Insertion      : 0.00
% 3.65/1.59  Index Deletion       : 0.00
% 3.65/1.59  Index Matching       : 0.00
% 3.65/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
