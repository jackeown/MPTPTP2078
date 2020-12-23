%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:22 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  141 (2283 expanded)
%              Number of leaves         :   42 ( 840 expanded)
%              Depth                    :   15
%              Number of atoms          :  258 (7223 expanded)
%              Number of equality atoms :  104 (2655 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
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
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_64,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_30,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_80,axiom,(
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

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_56,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_86,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_94,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_86])).

tff(c_52,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_93,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_86])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_106,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_93,c_46])).

tff(c_107,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_111,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_107])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_8,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_611,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_615,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_611])).

tff(c_44,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_112,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_93,c_44])).

tff(c_616,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_112])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_95,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_48])).

tff(c_104,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_95])).

tff(c_625,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_104])).

tff(c_621,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_615])).

tff(c_624,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_106])).

tff(c_740,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_tops_2(A_99,B_100,C_101) = k2_funct_1(C_101)
      | ~ v2_funct_1(C_101)
      | k2_relset_1(A_99,B_100,C_101) != B_100
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_2(C_101,A_99,B_100)
      | ~ v1_funct_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_746,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_624,c_740])).

tff(c_750,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_625,c_621,c_42,c_746])).

tff(c_700,plain,(
    ! [A_90,B_91,C_92] :
      ( m1_subset_1(k2_tops_2(A_90,B_91,C_92),k1_zfmisc_1(k2_zfmisc_1(B_91,A_90)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_2(C_92,A_90,B_91)
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_731,plain,(
    ! [B_96,A_97,C_98] :
      ( k2_relset_1(B_96,A_97,k2_tops_2(A_97,B_96,C_98)) = k2_relat_1(k2_tops_2(A_97,B_96,C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_2(C_98,A_97,B_96)
      | ~ v1_funct_1(C_98) ) ),
    inference(resolution,[status(thm)],[c_700,c_20])).

tff(c_735,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_624,c_731])).

tff(c_739,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) = k2_relat_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_625,c_735])).

tff(c_862,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_750,c_739])).

tff(c_10,plain,(
    ! [A_2] :
      ( k1_relat_1(k2_funct_1(A_2)) = k2_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_13] : k6_relat_1(A_13) = k6_partfun1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_57,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_146,plain,(
    ! [A_42,B_43,C_44] :
      ( k2_relset_1(A_42,B_43,C_44) = k2_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_146])).

tff(c_160,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_112])).

tff(c_168,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_104])).

tff(c_165,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_150])).

tff(c_167,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_106])).

tff(c_325,plain,(
    ! [A_62,C_63,B_64] :
      ( k6_partfun1(A_62) = k5_relat_1(C_63,k2_funct_1(C_63))
      | k1_xboole_0 = B_64
      | ~ v2_funct_1(C_63)
      | k2_relset_1(A_62,B_64,C_63) != B_64
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_62,B_64)))
      | ~ v1_funct_2(C_63,A_62,B_64)
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_331,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_167,c_325])).

tff(c_338,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_168,c_165,c_42,c_331])).

tff(c_339,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_30,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k2_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_173,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_30])).

tff(c_177,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_173])).

tff(c_178,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_177])).

tff(c_352,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_178])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_352])).

tff(c_357,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_12,plain,(
    ! [A_3] :
      ( k2_relat_1(k5_relat_1(A_3,k2_funct_1(A_3))) = k1_relat_1(A_3)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_362,plain,
    ( k2_relat_1(k6_partfun1(k2_struct_0('#skF_1'))) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_12])).

tff(c_369,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_50,c_42,c_57,c_362])).

tff(c_261,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_tops_2(A_59,B_60,C_61) = k2_funct_1(C_61)
      | ~ v2_funct_1(C_61)
      | k2_relset_1(A_59,B_60,C_61) != B_60
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_2(C_61,A_59,B_60)
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_267,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_167,c_261])).

tff(c_271,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_168,c_165,c_42,c_267])).

tff(c_34,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k2_tops_2(A_22,B_23,C_24),k1_zfmisc_1(k2_zfmisc_1(B_23,A_22)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_279,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_34])).

tff(c_283,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_168,c_167,c_279])).

tff(c_18,plain,(
    ! [A_7,B_8,C_9] :
      ( k1_relset_1(A_7,B_8,C_9) = k1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_318,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_283,c_18])).

tff(c_555,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_318])).

tff(c_40,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_117,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_93,c_93,c_94,c_94,c_93,c_93,c_40])).

tff(c_118,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_216,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_160,c_160,c_118])).

tff(c_275,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_216])).

tff(c_379,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_275])).

tff(c_556,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_379])).

tff(c_577,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_556])).

tff(c_581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_50,c_42,c_577])).

tff(c_582,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_623,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_616,c_582])).

tff(c_753,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_623])).

tff(c_863,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_753])).

tff(c_870,plain,
    ( k2_struct_0('#skF_1') != k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_863])).

tff(c_872,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_50,c_42,c_870])).

tff(c_827,plain,(
    ! [B_102,C_103,A_104] :
      ( k6_partfun1(B_102) = k5_relat_1(k2_funct_1(C_103),C_103)
      | k1_xboole_0 = B_102
      | ~ v2_funct_1(C_103)
      | k2_relset_1(A_104,B_102,C_103) != B_102
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102)))
      | ~ v1_funct_2(C_103,A_104,B_102)
      | ~ v1_funct_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_833,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_624,c_827])).

tff(c_840,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_625,c_621,c_42,c_833])).

tff(c_841,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_840])).

tff(c_630,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_30])).

tff(c_634,plain,
    ( ~ v1_xboole_0(k2_relat_1('#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_630])).

tff(c_635,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_634])).

tff(c_855,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_635])).

tff(c_859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_855])).

tff(c_861,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_840])).

tff(c_878,plain,(
    ! [A_105,C_106,B_107] :
      ( k6_partfun1(A_105) = k5_relat_1(C_106,k2_funct_1(C_106))
      | k1_xboole_0 = B_107
      | ~ v2_funct_1(C_106)
      | k2_relset_1(A_105,B_107,C_106) != B_107
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_105,B_107)))
      | ~ v1_funct_2(C_106,A_105,B_107)
      | ~ v1_funct_1(C_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_884,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_624,c_878])).

tff(c_891,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1'))
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_625,c_621,c_42,c_884])).

tff(c_892,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_861,c_891])).

tff(c_896,plain,
    ( k2_relat_1(k6_partfun1(k2_struct_0('#skF_1'))) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_12])).

tff(c_903,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_50,c_42,c_57,c_896])).

tff(c_905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_872,c_903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.48  
% 3.15/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.48  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k6_partfun1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.15/1.48  
% 3.15/1.48  %Foreground sorts:
% 3.15/1.48  
% 3.15/1.48  
% 3.15/1.48  %Background operators:
% 3.15/1.48  
% 3.15/1.48  
% 3.15/1.48  %Foreground operators:
% 3.15/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.15/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.15/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.15/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.15/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.48  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.15/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.15/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.15/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.48  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.15/1.48  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.15/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.15/1.48  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.15/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.48  
% 3.15/1.50  tff(f_140, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 3.15/1.50  tff(f_84, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.15/1.50  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.15/1.50  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.15/1.50  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.15/1.50  tff(f_104, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 3.15/1.50  tff(f_116, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.15/1.50  tff(f_64, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.15/1.50  tff(f_30, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.15/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.15/1.50  tff(f_80, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 3.15/1.50  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.15/1.50  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 3.15/1.50  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.15/1.50  tff(c_56, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.50  tff(c_86, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.15/1.50  tff(c_94, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_86])).
% 3.15/1.50  tff(c_52, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.50  tff(c_93, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_86])).
% 3.15/1.50  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.50  tff(c_106, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_93, c_46])).
% 3.15/1.50  tff(c_107, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.50  tff(c_111, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_107])).
% 3.15/1.50  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.50  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.50  tff(c_8, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.50  tff(c_611, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.50  tff(c_615, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_611])).
% 3.15/1.50  tff(c_44, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.50  tff(c_112, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_93, c_44])).
% 3.15/1.50  tff(c_616, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_615, c_112])).
% 3.15/1.50  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.50  tff(c_95, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_48])).
% 3.15/1.50  tff(c_104, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_95])).
% 3.15/1.50  tff(c_625, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_104])).
% 3.15/1.50  tff(c_621, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_615])).
% 3.15/1.50  tff(c_624, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_616, c_106])).
% 3.15/1.50  tff(c_740, plain, (![A_99, B_100, C_101]: (k2_tops_2(A_99, B_100, C_101)=k2_funct_1(C_101) | ~v2_funct_1(C_101) | k2_relset_1(A_99, B_100, C_101)!=B_100 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_2(C_101, A_99, B_100) | ~v1_funct_1(C_101))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.15/1.50  tff(c_746, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_624, c_740])).
% 3.15/1.50  tff(c_750, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_625, c_621, c_42, c_746])).
% 3.15/1.50  tff(c_700, plain, (![A_90, B_91, C_92]: (m1_subset_1(k2_tops_2(A_90, B_91, C_92), k1_zfmisc_1(k2_zfmisc_1(B_91, A_90))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_2(C_92, A_90, B_91) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.15/1.50  tff(c_20, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.50  tff(c_731, plain, (![B_96, A_97, C_98]: (k2_relset_1(B_96, A_97, k2_tops_2(A_97, B_96, C_98))=k2_relat_1(k2_tops_2(A_97, B_96, C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_2(C_98, A_97, B_96) | ~v1_funct_1(C_98))), inference(resolution, [status(thm)], [c_700, c_20])).
% 3.15/1.50  tff(c_735, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_624, c_731])).
% 3.15/1.50  tff(c_739, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))=k2_relat_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_625, c_735])).
% 3.15/1.50  tff(c_862, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_750, c_750, c_739])).
% 3.15/1.50  tff(c_10, plain, (![A_2]: (k1_relat_1(k2_funct_1(A_2))=k2_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.50  tff(c_22, plain, (![A_13]: (k6_relat_1(A_13)=k6_partfun1(A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.15/1.50  tff(c_6, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.15/1.50  tff(c_57, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6])).
% 3.15/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.15/1.50  tff(c_146, plain, (![A_42, B_43, C_44]: (k2_relset_1(A_42, B_43, C_44)=k2_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.15/1.50  tff(c_150, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_146])).
% 3.15/1.50  tff(c_160, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_112])).
% 3.15/1.50  tff(c_168, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_104])).
% 3.15/1.50  tff(c_165, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_150])).
% 3.15/1.50  tff(c_167, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_106])).
% 3.15/1.50  tff(c_325, plain, (![A_62, C_63, B_64]: (k6_partfun1(A_62)=k5_relat_1(C_63, k2_funct_1(C_63)) | k1_xboole_0=B_64 | ~v2_funct_1(C_63) | k2_relset_1(A_62, B_64, C_63)!=B_64 | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_62, B_64))) | ~v1_funct_2(C_63, A_62, B_64) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.15/1.50  tff(c_331, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_167, c_325])).
% 3.15/1.50  tff(c_338, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_168, c_165, c_42, c_331])).
% 3.15/1.50  tff(c_339, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_338])).
% 3.15/1.50  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.50  tff(c_30, plain, (![A_18]: (~v1_xboole_0(k2_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.15/1.50  tff(c_173, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_160, c_30])).
% 3.15/1.50  tff(c_177, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_173])).
% 3.15/1.50  tff(c_178, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_177])).
% 3.15/1.50  tff(c_352, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_339, c_178])).
% 3.15/1.50  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_352])).
% 3.15/1.50  tff(c_357, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_338])).
% 3.15/1.50  tff(c_12, plain, (![A_3]: (k2_relat_1(k5_relat_1(A_3, k2_funct_1(A_3)))=k1_relat_1(A_3) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.15/1.50  tff(c_362, plain, (k2_relat_1(k6_partfun1(k2_struct_0('#skF_1')))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_357, c_12])).
% 3.15/1.50  tff(c_369, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_50, c_42, c_57, c_362])).
% 3.15/1.50  tff(c_261, plain, (![A_59, B_60, C_61]: (k2_tops_2(A_59, B_60, C_61)=k2_funct_1(C_61) | ~v2_funct_1(C_61) | k2_relset_1(A_59, B_60, C_61)!=B_60 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_2(C_61, A_59, B_60) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.15/1.50  tff(c_267, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_167, c_261])).
% 3.15/1.50  tff(c_271, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_168, c_165, c_42, c_267])).
% 3.15/1.50  tff(c_34, plain, (![A_22, B_23, C_24]: (m1_subset_1(k2_tops_2(A_22, B_23, C_24), k1_zfmisc_1(k2_zfmisc_1(B_23, A_22))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.15/1.50  tff(c_279, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_271, c_34])).
% 3.15/1.50  tff(c_283, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_168, c_167, c_279])).
% 3.15/1.50  tff(c_18, plain, (![A_7, B_8, C_9]: (k1_relset_1(A_7, B_8, C_9)=k1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.15/1.50  tff(c_318, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_283, c_18])).
% 3.15/1.50  tff(c_555, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_318])).
% 3.15/1.50  tff(c_40, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.15/1.50  tff(c_117, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_93, c_93, c_94, c_94, c_93, c_93, c_40])).
% 3.15/1.50  tff(c_118, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_117])).
% 3.15/1.50  tff(c_216, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_160, c_160, c_118])).
% 3.15/1.50  tff(c_275, plain, (k1_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_216])).
% 3.15/1.50  tff(c_379, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_275])).
% 3.15/1.50  tff(c_556, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_555, c_379])).
% 3.15/1.50  tff(c_577, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10, c_556])).
% 3.15/1.50  tff(c_581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_50, c_42, c_577])).
% 3.15/1.50  tff(c_582, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_117])).
% 3.15/1.50  tff(c_623, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_616, c_582])).
% 3.15/1.50  tff(c_753, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_750, c_623])).
% 3.15/1.50  tff(c_863, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_862, c_753])).
% 3.15/1.50  tff(c_870, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_863])).
% 3.15/1.50  tff(c_872, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_50, c_42, c_870])).
% 3.15/1.50  tff(c_827, plain, (![B_102, C_103, A_104]: (k6_partfun1(B_102)=k5_relat_1(k2_funct_1(C_103), C_103) | k1_xboole_0=B_102 | ~v2_funct_1(C_103) | k2_relset_1(A_104, B_102, C_103)!=B_102 | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))) | ~v1_funct_2(C_103, A_104, B_102) | ~v1_funct_1(C_103))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.15/1.50  tff(c_833, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_624, c_827])).
% 3.15/1.50  tff(c_840, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_625, c_621, c_42, c_833])).
% 3.15/1.50  tff(c_841, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_840])).
% 3.15/1.50  tff(c_630, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_616, c_30])).
% 3.15/1.50  tff(c_634, plain, (~v1_xboole_0(k2_relat_1('#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_630])).
% 3.15/1.50  tff(c_635, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_634])).
% 3.15/1.50  tff(c_855, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_841, c_635])).
% 3.15/1.50  tff(c_859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_855])).
% 3.15/1.50  tff(c_861, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_840])).
% 3.15/1.50  tff(c_878, plain, (![A_105, C_106, B_107]: (k6_partfun1(A_105)=k5_relat_1(C_106, k2_funct_1(C_106)) | k1_xboole_0=B_107 | ~v2_funct_1(C_106) | k2_relset_1(A_105, B_107, C_106)!=B_107 | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_105, B_107))) | ~v1_funct_2(C_106, A_105, B_107) | ~v1_funct_1(C_106))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.15/1.50  tff(c_884, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0 | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_624, c_878])).
% 3.15/1.50  tff(c_891, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1')) | k2_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_625, c_621, c_42, c_884])).
% 3.15/1.50  tff(c_892, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_861, c_891])).
% 3.15/1.50  tff(c_896, plain, (k2_relat_1(k6_partfun1(k2_struct_0('#skF_1')))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_892, c_12])).
% 3.15/1.50  tff(c_903, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_50, c_42, c_57, c_896])).
% 3.15/1.50  tff(c_905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_872, c_903])).
% 3.15/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.50  
% 3.15/1.50  Inference rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Ref     : 0
% 3.15/1.50  #Sup     : 190
% 3.15/1.50  #Fact    : 0
% 3.15/1.50  #Define  : 0
% 3.15/1.50  #Split   : 4
% 3.15/1.50  #Chain   : 0
% 3.15/1.50  #Close   : 0
% 3.15/1.50  
% 3.15/1.50  Ordering : KBO
% 3.15/1.50  
% 3.15/1.50  Simplification rules
% 3.15/1.50  ----------------------
% 3.15/1.50  #Subsume      : 3
% 3.15/1.50  #Demod        : 265
% 3.15/1.50  #Tautology    : 112
% 3.15/1.50  #SimpNegUnit  : 6
% 3.15/1.50  #BackRed      : 69
% 3.15/1.50  
% 3.15/1.50  #Partial instantiations: 0
% 3.15/1.50  #Strategies tried      : 1
% 3.15/1.50  
% 3.15/1.50  Timing (in seconds)
% 3.15/1.50  ----------------------
% 3.15/1.51  Preprocessing        : 0.34
% 3.15/1.51  Parsing              : 0.18
% 3.15/1.51  CNF conversion       : 0.02
% 3.15/1.51  Main loop            : 0.40
% 3.15/1.51  Inferencing          : 0.13
% 3.15/1.51  Reduction            : 0.15
% 3.15/1.51  Demodulation         : 0.11
% 3.15/1.51  BG Simplification    : 0.02
% 3.15/1.51  Subsumption          : 0.06
% 3.15/1.51  Abstraction          : 0.02
% 3.15/1.51  MUC search           : 0.00
% 3.15/1.51  Cooper               : 0.00
% 3.15/1.51  Total                : 0.78
% 3.15/1.51  Index Insertion      : 0.00
% 3.15/1.51  Index Deletion       : 0.00
% 3.15/1.51  Index Matching       : 0.00
% 3.15/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
