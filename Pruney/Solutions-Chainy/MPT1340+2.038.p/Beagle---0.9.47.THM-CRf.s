%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:35 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   90 (1074 expanded)
%              Number of leaves         :   31 ( 415 expanded)
%              Depth                    :   14
%              Number of atoms          :  210 (3556 expanded)
%              Number of equality atoms :   44 ( 778 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_41,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_112,axiom,(
    ! [A] :
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
               => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                  & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(c_42,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_43,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_51,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_43])).

tff(c_38,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_43])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_32])).

tff(c_67,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_67])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_34,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_60,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_34])).

tff(c_101,plain,(
    ! [A_37,B_38,D_39] :
      ( r2_funct_2(A_37,B_38,D_39,D_39)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_2(D_39,A_37,B_38)
      | ~ v1_funct_1(D_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_101])).

tff(c_106,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_103])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_funct_1(k2_funct_1(A_2)) = A_2
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_61,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_50,c_30])).

tff(c_139,plain,(
    ! [A_49,B_50,C_51] :
      ( k2_tops_2(A_49,B_50,C_51) = k2_funct_1(C_51)
      | ~ v2_funct_1(C_51)
      | k2_relset_1(A_49,B_50,C_51) != B_50
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(C_51,A_49,B_50)
      | ~ v1_funct_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_145,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_139])).

tff(c_149,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_61,c_28,c_145])).

tff(c_94,plain,(
    ! [A_34,B_35,C_36] :
      ( v1_funct_1(k2_tops_2(A_34,B_35,C_36))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_2(C_36,A_34,B_35)
      | ~ v1_funct_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_97,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_94])).

tff(c_100,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_97])).

tff(c_152,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_100])).

tff(c_107,plain,(
    ! [A_40,B_41,C_42] :
      ( v1_funct_2(k2_tops_2(A_40,B_41,C_42),B_41,A_40)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(C_42,A_40,B_41)
      | ~ v1_funct_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_109,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_107])).

tff(c_112,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_109])).

tff(c_151,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_112])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k2_tops_2(A_14,B_15,C_16),k1_zfmisc_1(k2_zfmisc_1(B_15,A_14)))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_157,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_16])).

tff(c_161,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_66,c_157])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_tops_2(A_11,B_12,C_13) = k2_funct_1(C_13)
      | ~ v2_funct_1(C_13)
      | k2_relset_1(A_11,B_12,C_13) != B_12
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_2(C_13,A_11,B_12)
      | ~ v1_funct_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_165,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_161,c_14])).

tff(c_181,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_151,c_165])).

tff(c_209,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_210,plain,(
    ! [B_56,A_57,C_58] :
      ( k2_relset_1(u1_struct_0(B_56),u1_struct_0(A_57),k2_tops_2(u1_struct_0(A_57),u1_struct_0(B_56),C_58)) = k2_struct_0(A_57)
      | ~ v2_funct_1(C_58)
      | k2_relset_1(u1_struct_0(A_57),u1_struct_0(B_56),C_58) != k2_struct_0(B_56)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_57),u1_struct_0(B_56))))
      | ~ v1_funct_2(C_58,u1_struct_0(A_57),u1_struct_0(B_56))
      | ~ v1_funct_1(C_58)
      | ~ l1_struct_0(B_56)
      | v2_struct_0(B_56)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_240,plain,(
    ! [A_57,C_58] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_57),k2_tops_2(u1_struct_0(A_57),k2_struct_0('#skF_2'),C_58)) = k2_struct_0(A_57)
      | ~ v2_funct_1(C_58)
      | k2_relset_1(u1_struct_0(A_57),u1_struct_0('#skF_2'),C_58) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_57),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_58,u1_struct_0(A_57),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_58)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_210])).

tff(c_259,plain,(
    ! [A_57,C_58] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_57),k2_tops_2(u1_struct_0(A_57),k2_struct_0('#skF_2'),C_58)) = k2_struct_0(A_57)
      | ~ v2_funct_1(C_58)
      | k2_relset_1(u1_struct_0(A_57),k2_struct_0('#skF_2'),C_58) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_57),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_58,u1_struct_0(A_57),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_58)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50,c_50,c_50,c_50,c_240])).

tff(c_361,plain,(
    ! [A_74,C_75] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_74),k2_tops_2(u1_struct_0(A_74),k2_struct_0('#skF_2'),C_75)) = k2_struct_0(A_74)
      | ~ v2_funct_1(C_75)
      | k2_relset_1(u1_struct_0(A_74),k2_struct_0('#skF_2'),C_75) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_75,u1_struct_0(A_74),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_75)
      | ~ l1_struct_0(A_74) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_259])).

tff(c_370,plain,(
    ! [C_75] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_75)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_75)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_75) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_75,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_75)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_361])).

tff(c_390,plain,(
    ! [C_76] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_76)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_76)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_76) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_76,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_51,c_51,c_51,c_51,c_370])).

tff(c_399,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_390])).

tff(c_403,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60,c_66,c_61,c_28,c_399])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_403])).

tff(c_406,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_412,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_415,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_412])).

tff(c_419,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_36,c_28,c_415])).

tff(c_420,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_26,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_93,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_51,c_51,c_50,c_50,c_50,c_26])).

tff(c_153,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_93])).

tff(c_425,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_153])).

tff(c_503,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_425])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_36,c_28,c_106,c_503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:34:00 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.48  
% 3.12/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.48  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.12/1.48  
% 3.12/1.48  %Foreground sorts:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Background operators:
% 3.12/1.48  
% 3.12/1.48  
% 3.12/1.48  %Foreground operators:
% 3.12/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.12/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.12/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.12/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.12/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.48  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.12/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.12/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.12/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.12/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.12/1.48  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.12/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.48  
% 3.29/1.50  tff(f_134, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.29/1.50  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.29/1.50  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.29/1.50  tff(f_61, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.29/1.50  tff(f_41, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.29/1.50  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_1)).
% 3.29/1.50  tff(f_77, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.29/1.50  tff(f_89, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.29/1.50  tff(f_112, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.29/1.50  tff(c_42, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.29/1.50  tff(c_43, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.50  tff(c_51, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_43])).
% 3.29/1.50  tff(c_38, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.29/1.50  tff(c_50, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_43])).
% 3.29/1.50  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.29/1.50  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_32])).
% 3.29/1.50  tff(c_67, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.29/1.50  tff(c_71, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_67])).
% 3.29/1.50  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.29/1.50  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.29/1.50  tff(c_34, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.29/1.50  tff(c_60, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_34])).
% 3.29/1.50  tff(c_101, plain, (![A_37, B_38, D_39]: (r2_funct_2(A_37, B_38, D_39, D_39) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_2(D_39, A_37, B_38) | ~v1_funct_1(D_39))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.29/1.50  tff(c_103, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_101])).
% 3.29/1.50  tff(c_106, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_103])).
% 3.29/1.50  tff(c_4, plain, (![A_2]: (k2_funct_1(k2_funct_1(A_2))=A_2 | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.50  tff(c_2, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.50  tff(c_30, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.29/1.50  tff(c_61, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_50, c_30])).
% 3.29/1.50  tff(c_139, plain, (![A_49, B_50, C_51]: (k2_tops_2(A_49, B_50, C_51)=k2_funct_1(C_51) | ~v2_funct_1(C_51) | k2_relset_1(A_49, B_50, C_51)!=B_50 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(C_51, A_49, B_50) | ~v1_funct_1(C_51))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.29/1.50  tff(c_145, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_139])).
% 3.29/1.50  tff(c_149, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_61, c_28, c_145])).
% 3.29/1.50  tff(c_94, plain, (![A_34, B_35, C_36]: (v1_funct_1(k2_tops_2(A_34, B_35, C_36)) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_2(C_36, A_34, B_35) | ~v1_funct_1(C_36))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.50  tff(c_97, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_94])).
% 3.29/1.50  tff(c_100, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_97])).
% 3.29/1.50  tff(c_152, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_100])).
% 3.29/1.50  tff(c_107, plain, (![A_40, B_41, C_42]: (v1_funct_2(k2_tops_2(A_40, B_41, C_42), B_41, A_40) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(C_42, A_40, B_41) | ~v1_funct_1(C_42))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.50  tff(c_109, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_107])).
% 3.29/1.50  tff(c_112, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_109])).
% 3.29/1.50  tff(c_151, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_112])).
% 3.29/1.50  tff(c_16, plain, (![A_14, B_15, C_16]: (m1_subset_1(k2_tops_2(A_14, B_15, C_16), k1_zfmisc_1(k2_zfmisc_1(B_15, A_14))) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.50  tff(c_157, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_149, c_16])).
% 3.29/1.50  tff(c_161, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_66, c_157])).
% 3.29/1.50  tff(c_14, plain, (![A_11, B_12, C_13]: (k2_tops_2(A_11, B_12, C_13)=k2_funct_1(C_13) | ~v2_funct_1(C_13) | k2_relset_1(A_11, B_12, C_13)!=B_12 | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_2(C_13, A_11, B_12) | ~v1_funct_1(C_13))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.29/1.50  tff(c_165, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_161, c_14])).
% 3.29/1.50  tff(c_181, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_151, c_165])).
% 3.29/1.50  tff(c_209, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_181])).
% 3.29/1.50  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.29/1.50  tff(c_210, plain, (![B_56, A_57, C_58]: (k2_relset_1(u1_struct_0(B_56), u1_struct_0(A_57), k2_tops_2(u1_struct_0(A_57), u1_struct_0(B_56), C_58))=k2_struct_0(A_57) | ~v2_funct_1(C_58) | k2_relset_1(u1_struct_0(A_57), u1_struct_0(B_56), C_58)!=k2_struct_0(B_56) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_57), u1_struct_0(B_56)))) | ~v1_funct_2(C_58, u1_struct_0(A_57), u1_struct_0(B_56)) | ~v1_funct_1(C_58) | ~l1_struct_0(B_56) | v2_struct_0(B_56) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.29/1.50  tff(c_240, plain, (![A_57, C_58]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_57), k2_tops_2(u1_struct_0(A_57), k2_struct_0('#skF_2'), C_58))=k2_struct_0(A_57) | ~v2_funct_1(C_58) | k2_relset_1(u1_struct_0(A_57), u1_struct_0('#skF_2'), C_58)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_57), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_58, u1_struct_0(A_57), u1_struct_0('#skF_2')) | ~v1_funct_1(C_58) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_57))), inference(superposition, [status(thm), theory('equality')], [c_50, c_210])).
% 3.29/1.50  tff(c_259, plain, (![A_57, C_58]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_57), k2_tops_2(u1_struct_0(A_57), k2_struct_0('#skF_2'), C_58))=k2_struct_0(A_57) | ~v2_funct_1(C_58) | k2_relset_1(u1_struct_0(A_57), k2_struct_0('#skF_2'), C_58)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_57), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_58, u1_struct_0(A_57), k2_struct_0('#skF_2')) | ~v1_funct_1(C_58) | v2_struct_0('#skF_2') | ~l1_struct_0(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50, c_50, c_50, c_50, c_240])).
% 3.29/1.50  tff(c_361, plain, (![A_74, C_75]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_74), k2_tops_2(u1_struct_0(A_74), k2_struct_0('#skF_2'), C_75))=k2_struct_0(A_74) | ~v2_funct_1(C_75) | k2_relset_1(u1_struct_0(A_74), k2_struct_0('#skF_2'), C_75)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_74), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_75, u1_struct_0(A_74), k2_struct_0('#skF_2')) | ~v1_funct_1(C_75) | ~l1_struct_0(A_74))), inference(negUnitSimplification, [status(thm)], [c_40, c_259])).
% 3.29/1.50  tff(c_370, plain, (![C_75]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_75))=k2_struct_0('#skF_1') | ~v2_funct_1(C_75) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_75)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_75, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_75) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_51, c_361])).
% 3.29/1.50  tff(c_390, plain, (![C_76]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_76))=k2_struct_0('#skF_1') | ~v2_funct_1(C_76) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_76)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_76, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_76))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_51, c_51, c_51, c_51, c_370])).
% 3.29/1.50  tff(c_399, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_149, c_390])).
% 3.29/1.50  tff(c_403, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60, c_66, c_61, c_28, c_399])).
% 3.29/1.50  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_403])).
% 3.29/1.50  tff(c_406, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_181])).
% 3.29/1.50  tff(c_412, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_406])).
% 3.29/1.50  tff(c_415, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_412])).
% 3.29/1.50  tff(c_419, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_36, c_28, c_415])).
% 3.29/1.50  tff(c_420, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_406])).
% 3.29/1.50  tff(c_26, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.29/1.50  tff(c_93, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_51, c_51, c_50, c_50, c_50, c_26])).
% 3.29/1.50  tff(c_153, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_93])).
% 3.29/1.50  tff(c_425, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_420, c_153])).
% 3.29/1.50  tff(c_503, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_425])).
% 3.29/1.50  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_36, c_28, c_106, c_503])).
% 3.29/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.50  
% 3.29/1.50  Inference rules
% 3.29/1.50  ----------------------
% 3.29/1.50  #Ref     : 0
% 3.29/1.50  #Sup     : 95
% 3.29/1.50  #Fact    : 0
% 3.29/1.50  #Define  : 0
% 3.29/1.50  #Split   : 2
% 3.29/1.50  #Chain   : 0
% 3.29/1.50  #Close   : 0
% 3.29/1.50  
% 3.29/1.50  Ordering : KBO
% 3.29/1.50  
% 3.29/1.50  Simplification rules
% 3.29/1.50  ----------------------
% 3.29/1.50  #Subsume      : 0
% 3.29/1.50  #Demod        : 269
% 3.29/1.50  #Tautology    : 39
% 3.29/1.50  #SimpNegUnit  : 7
% 3.29/1.50  #BackRed      : 8
% 3.29/1.50  
% 3.29/1.50  #Partial instantiations: 0
% 3.29/1.50  #Strategies tried      : 1
% 3.29/1.50  
% 3.29/1.50  Timing (in seconds)
% 3.29/1.50  ----------------------
% 3.29/1.51  Preprocessing        : 0.35
% 3.29/1.51  Parsing              : 0.19
% 3.29/1.51  CNF conversion       : 0.02
% 3.29/1.51  Main loop            : 0.36
% 3.29/1.51  Inferencing          : 0.12
% 3.29/1.51  Reduction            : 0.14
% 3.29/1.51  Demodulation         : 0.10
% 3.29/1.51  BG Simplification    : 0.02
% 3.29/1.51  Subsumption          : 0.06
% 3.29/1.51  Abstraction          : 0.02
% 3.29/1.51  MUC search           : 0.00
% 3.29/1.51  Cooper               : 0.00
% 3.29/1.51  Total                : 0.75
% 3.29/1.51  Index Insertion      : 0.00
% 3.29/1.51  Index Deletion       : 0.00
% 3.29/1.51  Index Matching       : 0.00
% 3.29/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
