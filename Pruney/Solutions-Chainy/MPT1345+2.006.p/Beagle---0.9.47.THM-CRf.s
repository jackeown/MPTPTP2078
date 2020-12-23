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
% DateTime   : Thu Dec  3 10:23:49 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :  205 (9189 expanded)
%              Number of leaves         :   35 (3122 expanded)
%              Depth                    :   23
%              Number of atoms          :  744 (25795 expanded)
%              Number of equality atoms :  127 (4351 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v3_tops_2,type,(
    v3_tops_2: ( $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_tops_2(C,A,B)
                 => v3_tops_2(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
              <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & v5_pre_topc(C,A,B)
                  & v5_pre_topc(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_133,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_16,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_59,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_16,c_59])).

tff(c_72,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_64])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_71,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_64])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_74,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_48])).

tff(c_83,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_73,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_46])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_73])).

tff(c_160,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_tops_2(A_57,B_58,C_59) = k2_funct_1(C_59)
      | ~ v2_funct_1(C_59)
      | k2_relset_1(A_57,B_58,C_59) != B_58
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_166,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_160])).

tff(c_170,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_166])).

tff(c_171,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_44,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_340,plain,(
    ! [A_81,B_82,C_83] :
      ( k2_relset_1(u1_struct_0(A_81),u1_struct_0(B_82),C_83) = k2_struct_0(B_82)
      | ~ v3_tops_2(C_83,A_81,B_82)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81),u1_struct_0(B_82))))
      | ~ v1_funct_2(C_83,u1_struct_0(A_81),u1_struct_0(B_82))
      | ~ v1_funct_1(C_83)
      | ~ l1_pre_topc(B_82)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_347,plain,(
    ! [B_82,C_83] :
      ( k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_82),C_83) = k2_struct_0(B_82)
      | ~ v3_tops_2(C_83,'#skF_1',B_82)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_82))))
      | ~ v1_funct_2(C_83,u1_struct_0('#skF_1'),u1_struct_0(B_82))
      | ~ v1_funct_1(C_83)
      | ~ l1_pre_topc(B_82)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_340])).

tff(c_438,plain,(
    ! [B_93,C_94] :
      ( k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_93),C_94) = k2_struct_0(B_93)
      | ~ v3_tops_2(C_94,'#skF_1',B_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_93))))
      | ~ v1_funct_2(C_94,k2_struct_0('#skF_1'),u1_struct_0(B_93))
      | ~ v1_funct_1(C_94)
      | ~ l1_pre_topc(B_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_72,c_72,c_347])).

tff(c_448,plain,(
    ! [C_94] :
      ( k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_94) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_94,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_94,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_94)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_438])).

tff(c_486,plain,(
    ! [C_99] :
      ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_99) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_99,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_99,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71,c_71,c_448])).

tff(c_493,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_486])).

tff(c_497,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_44,c_493])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_497])).

tff(c_500,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_506,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_507,plain,(
    ! [C_100,A_101,B_102] :
      ( v2_funct_1(C_100)
      | ~ v3_tops_2(C_100,A_101,B_102)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101),u1_struct_0(B_102))))
      | ~ v1_funct_2(C_100,u1_struct_0(A_101),u1_struct_0(B_102))
      | ~ v1_funct_1(C_100)
      | ~ l1_pre_topc(B_102)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_514,plain,(
    ! [C_100,B_102] :
      ( v2_funct_1(C_100)
      | ~ v3_tops_2(C_100,'#skF_1',B_102)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_102))))
      | ~ v1_funct_2(C_100,u1_struct_0('#skF_1'),u1_struct_0(B_102))
      | ~ v1_funct_1(C_100)
      | ~ l1_pre_topc(B_102)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_507])).

tff(c_533,plain,(
    ! [C_103,B_104] :
      ( v2_funct_1(C_103)
      | ~ v3_tops_2(C_103,'#skF_1',B_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_104))))
      | ~ v1_funct_2(C_103,k2_struct_0('#skF_1'),u1_struct_0(B_104))
      | ~ v1_funct_1(C_103)
      | ~ l1_pre_topc(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_72,c_514])).

tff(c_543,plain,(
    ! [C_103] :
      ( v2_funct_1(C_103)
      | ~ v3_tops_2(C_103,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_103,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_103)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_533])).

tff(c_555,plain,(
    ! [C_106] :
      ( v2_funct_1(C_106)
      | ~ v3_tops_2(C_106,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_106,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71,c_543])).

tff(c_562,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_555])).

tff(c_566,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_44,c_562])).

tff(c_568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_506,c_566])).

tff(c_569,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_42,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_94,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_71,c_42])).

tff(c_600,plain,(
    ~ v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_94])).

tff(c_122,plain,(
    ! [A_45,B_46,C_47] :
      ( v1_funct_1(k2_tops_2(A_45,B_46,C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_125,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_122])).

tff(c_128,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_125])).

tff(c_599,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_128])).

tff(c_129,plain,(
    ! [A_48,B_49,C_50] :
      ( v1_funct_2(k2_tops_2(A_48,B_49,C_50),B_49,A_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_131,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_129])).

tff(c_134,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_131])).

tff(c_598,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_134])).

tff(c_501,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_570,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1908,plain,(
    ! [B_242,A_243,C_244] :
      ( k2_relset_1(u1_struct_0(B_242),u1_struct_0(A_243),k2_tops_2(u1_struct_0(A_243),u1_struct_0(B_242),C_244)) = k2_struct_0(A_243)
      | ~ v2_funct_1(C_244)
      | k2_relset_1(u1_struct_0(A_243),u1_struct_0(B_242),C_244) != k2_struct_0(B_242)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243),u1_struct_0(B_242))))
      | ~ v1_funct_2(C_244,u1_struct_0(A_243),u1_struct_0(B_242))
      | ~ v1_funct_1(C_244)
      | ~ l1_struct_0(B_242)
      | v2_struct_0(B_242)
      | ~ l1_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1929,plain,(
    ! [A_243,C_244] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_243),k2_tops_2(u1_struct_0(A_243),u1_struct_0('#skF_2'),C_244)) = k2_struct_0(A_243)
      | ~ v2_funct_1(C_244)
      | k2_relset_1(u1_struct_0(A_243),u1_struct_0('#skF_2'),C_244) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_244,u1_struct_0(A_243),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_244)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1908])).

tff(c_1945,plain,(
    ! [A_243,C_244] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_243),k2_tops_2(u1_struct_0(A_243),k2_struct_0('#skF_2'),C_244)) = k2_struct_0(A_243)
      | ~ v2_funct_1(C_244)
      | k2_relset_1(u1_struct_0(A_243),k2_struct_0('#skF_2'),C_244) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_244,u1_struct_0(A_243),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_244)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_71,c_71,c_1929])).

tff(c_1946,plain,(
    ! [A_243,C_244] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_243),k2_tops_2(u1_struct_0(A_243),k2_struct_0('#skF_2'),C_244)) = k2_struct_0(A_243)
      | ~ v2_funct_1(C_244)
      | k2_relset_1(u1_struct_0(A_243),k2_struct_0('#skF_2'),C_244) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_244,u1_struct_0(A_243),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_244)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_243) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1945])).

tff(c_1972,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1946])).

tff(c_1975,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1972])).

tff(c_1979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1975])).

tff(c_1981,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1946])).

tff(c_1938,plain,(
    ! [A_243,C_244] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_243),k2_tops_2(u1_struct_0(A_243),k2_struct_0('#skF_2'),C_244)) = k2_struct_0(A_243)
      | ~ v2_funct_1(C_244)
      | k2_relset_1(u1_struct_0(A_243),u1_struct_0('#skF_2'),C_244) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_244,u1_struct_0(A_243),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_244)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1908])).

tff(c_1949,plain,(
    ! [A_243,C_244] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_243),k2_tops_2(u1_struct_0(A_243),k2_struct_0('#skF_2'),C_244)) = k2_struct_0(A_243)
      | ~ v2_funct_1(C_244)
      | k2_relset_1(u1_struct_0(A_243),k2_struct_0('#skF_2'),C_244) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_244,u1_struct_0(A_243),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_244)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_71,c_71,c_1938])).

tff(c_1950,plain,(
    ! [A_243,C_244] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_243),k2_tops_2(u1_struct_0(A_243),k2_struct_0('#skF_2'),C_244)) = k2_struct_0(A_243)
      | ~ v2_funct_1(C_244)
      | k2_relset_1(u1_struct_0(A_243),k2_struct_0('#skF_2'),C_244) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_244,u1_struct_0(A_243),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_244)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_243) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1949])).

tff(c_2357,plain,(
    ! [A_272,C_273] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_272),k2_tops_2(u1_struct_0(A_272),k2_struct_0('#skF_2'),C_273)) = k2_struct_0(A_272)
      | ~ v2_funct_1(C_273)
      | k2_relset_1(u1_struct_0(A_272),k2_struct_0('#skF_2'),C_273) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_272),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_273,u1_struct_0(A_272),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_273)
      | ~ l1_struct_0(A_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1981,c_1950])).

tff(c_2369,plain,(
    ! [C_273] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_273)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_273)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_273) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_273,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_273)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2357])).

tff(c_2379,plain,(
    ! [C_273] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_273)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_273)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_273) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_273,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_273)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_72,c_72,c_2369])).

tff(c_2636,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2379])).

tff(c_2685,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_2636])).

tff(c_2689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2685])).

tff(c_2691,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2379])).

tff(c_2007,plain,(
    ! [B_247,A_248,C_249] :
      ( k1_relset_1(u1_struct_0(B_247),u1_struct_0(A_248),k2_tops_2(u1_struct_0(A_248),u1_struct_0(B_247),C_249)) = k2_struct_0(B_247)
      | ~ v2_funct_1(C_249)
      | k2_relset_1(u1_struct_0(A_248),u1_struct_0(B_247),C_249) != k2_struct_0(B_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_248),u1_struct_0(B_247))))
      | ~ v1_funct_2(C_249,u1_struct_0(A_248),u1_struct_0(B_247))
      | ~ v1_funct_1(C_249)
      | ~ l1_struct_0(B_247)
      | v2_struct_0(B_247)
      | ~ l1_struct_0(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2028,plain,(
    ! [A_248,C_249] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_248),k2_tops_2(u1_struct_0(A_248),u1_struct_0('#skF_2'),C_249)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_249)
      | k2_relset_1(u1_struct_0(A_248),u1_struct_0('#skF_2'),C_249) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_248),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_249,u1_struct_0(A_248),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_249)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_2007])).

tff(c_2045,plain,(
    ! [A_248,C_249] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_248),k2_tops_2(u1_struct_0(A_248),k2_struct_0('#skF_2'),C_249)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_249)
      | k2_relset_1(u1_struct_0(A_248),k2_struct_0('#skF_2'),C_249) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_248),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_249,u1_struct_0(A_248),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_249)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1981,c_71,c_71,c_71,c_71,c_2028])).

tff(c_2091,plain,(
    ! [A_250,C_251] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_250),k2_tops_2(u1_struct_0(A_250),k2_struct_0('#skF_2'),C_251)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_251)
      | k2_relset_1(u1_struct_0(A_250),k2_struct_0('#skF_2'),C_251) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_250),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_251,u1_struct_0(A_250),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_251)
      | ~ l1_struct_0(A_250) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2045])).

tff(c_2103,plain,(
    ! [C_251] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_251)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_251)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_251) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_251,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_251)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2091])).

tff(c_2113,plain,(
    ! [C_251] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_251)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_251)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_251) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_251,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_251)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_72,c_72,c_2103])).

tff(c_2718,plain,(
    ! [C_311] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_311)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_311)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_311) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_311,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2691,c_2113])).

tff(c_2730,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_2718])).

tff(c_2736,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_86,c_501,c_570,c_2730])).

tff(c_32,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_subset_1(k2_tops_2(A_20,B_21,C_22),k1_zfmisc_1(k2_zfmisc_1(B_21,A_20)))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_604,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_32])).

tff(c_608,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_86,c_604])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_tops_2(A_10,B_11,C_12) = k2_funct_1(C_12)
      | ~ v2_funct_1(C_12)
      | k2_relset_1(A_10,B_11,C_12) != B_11
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_2(C_12,A_10,B_11)
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_612,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_608,c_18])).

tff(c_626,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_598,c_612])).

tff(c_665,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_626])).

tff(c_1144,plain,(
    ! [B_170,A_171,C_172] :
      ( k1_relset_1(u1_struct_0(B_170),u1_struct_0(A_171),k2_tops_2(u1_struct_0(A_171),u1_struct_0(B_170),C_172)) = k2_struct_0(B_170)
      | ~ v2_funct_1(C_172)
      | k2_relset_1(u1_struct_0(A_171),u1_struct_0(B_170),C_172) != k2_struct_0(B_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),u1_struct_0(B_170))))
      | ~ v1_funct_2(C_172,u1_struct_0(A_171),u1_struct_0(B_170))
      | ~ v1_funct_1(C_172)
      | ~ l1_struct_0(B_170)
      | v2_struct_0(B_170)
      | ~ l1_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1174,plain,(
    ! [A_171,C_172] :
      ( k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_171),k2_tops_2(u1_struct_0(A_171),k2_struct_0('#skF_2'),C_172)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_172)
      | k2_relset_1(u1_struct_0(A_171),u1_struct_0('#skF_2'),C_172) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_172,u1_struct_0(A_171),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_172)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1144])).

tff(c_1185,plain,(
    ! [A_171,C_172] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_171),k2_tops_2(u1_struct_0(A_171),k2_struct_0('#skF_2'),C_172)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_172)
      | k2_relset_1(u1_struct_0(A_171),k2_struct_0('#skF_2'),C_172) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_172,u1_struct_0(A_171),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_172)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_71,c_71,c_1174])).

tff(c_1186,plain,(
    ! [A_171,C_172] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_171),k2_tops_2(u1_struct_0(A_171),k2_struct_0('#skF_2'),C_172)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_172)
      | k2_relset_1(u1_struct_0(A_171),k2_struct_0('#skF_2'),C_172) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_172,u1_struct_0(A_171),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_172)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1185])).

tff(c_1218,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1186])).

tff(c_1221,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1218])).

tff(c_1225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1221])).

tff(c_1227,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1186])).

tff(c_1165,plain,(
    ! [A_171,C_172] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_171),k2_tops_2(u1_struct_0(A_171),u1_struct_0('#skF_2'),C_172)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_172)
      | k2_relset_1(u1_struct_0(A_171),u1_struct_0('#skF_2'),C_172) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_172,u1_struct_0(A_171),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_172)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1144])).

tff(c_1181,plain,(
    ! [A_171,C_172] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_171),k2_tops_2(u1_struct_0(A_171),k2_struct_0('#skF_2'),C_172)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_172)
      | k2_relset_1(u1_struct_0(A_171),k2_struct_0('#skF_2'),C_172) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_172,u1_struct_0(A_171),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_172)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_71,c_71,c_71,c_1165])).

tff(c_1182,plain,(
    ! [A_171,C_172] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_171),k2_tops_2(u1_struct_0(A_171),k2_struct_0('#skF_2'),C_172)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_172)
      | k2_relset_1(u1_struct_0(A_171),k2_struct_0('#skF_2'),C_172) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_172,u1_struct_0(A_171),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_172)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1181])).

tff(c_1426,plain,(
    ! [A_203,C_204] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_203),k2_tops_2(u1_struct_0(A_203),k2_struct_0('#skF_2'),C_204)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_204)
      | k2_relset_1(u1_struct_0(A_203),k2_struct_0('#skF_2'),C_204) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_204,u1_struct_0(A_203),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_204)
      | ~ l1_struct_0(A_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1227,c_1182])).

tff(c_1438,plain,(
    ! [C_204] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_204)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_204)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_204) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_204,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_204)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1426])).

tff(c_1448,plain,(
    ! [C_204] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_204)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_204)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_204) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_204,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_204)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_72,c_72,c_1438])).

tff(c_1462,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1448])).

tff(c_1465,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1462])).

tff(c_1469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1465])).

tff(c_1471,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1448])).

tff(c_1258,plain,(
    ! [B_180,A_181,C_182] :
      ( k2_relset_1(u1_struct_0(B_180),u1_struct_0(A_181),k2_tops_2(u1_struct_0(A_181),u1_struct_0(B_180),C_182)) = k2_struct_0(A_181)
      | ~ v2_funct_1(C_182)
      | k2_relset_1(u1_struct_0(A_181),u1_struct_0(B_180),C_182) != k2_struct_0(B_180)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),u1_struct_0(B_180))))
      | ~ v1_funct_2(C_182,u1_struct_0(A_181),u1_struct_0(B_180))
      | ~ v1_funct_1(C_182)
      | ~ l1_struct_0(B_180)
      | v2_struct_0(B_180)
      | ~ l1_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1288,plain,(
    ! [A_181,C_182] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_181),k2_tops_2(u1_struct_0(A_181),k2_struct_0('#skF_2'),C_182)) = k2_struct_0(A_181)
      | ~ v2_funct_1(C_182)
      | k2_relset_1(u1_struct_0(A_181),u1_struct_0('#skF_2'),C_182) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_182,u1_struct_0(A_181),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_182)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1258])).

tff(c_1303,plain,(
    ! [A_181,C_182] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_181),k2_tops_2(u1_struct_0(A_181),k2_struct_0('#skF_2'),C_182)) = k2_struct_0(A_181)
      | ~ v2_funct_1(C_182)
      | k2_relset_1(u1_struct_0(A_181),k2_struct_0('#skF_2'),C_182) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_182,u1_struct_0(A_181),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_182)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1227,c_71,c_71,c_71,c_71,c_1288])).

tff(c_1337,plain,(
    ! [A_188,C_189] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_188),k2_tops_2(u1_struct_0(A_188),k2_struct_0('#skF_2'),C_189)) = k2_struct_0(A_188)
      | ~ v2_funct_1(C_189)
      | k2_relset_1(u1_struct_0(A_188),k2_struct_0('#skF_2'),C_189) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_189,u1_struct_0(A_188),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_189)
      | ~ l1_struct_0(A_188) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1303])).

tff(c_1346,plain,(
    ! [C_189] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_189)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_189)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_189) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_189,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_189)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1337])).

tff(c_1358,plain,(
    ! [C_189] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_189)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_189)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_189) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_189,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_189)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_72,c_72,c_1346])).

tff(c_1512,plain,(
    ! [C_210] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_210)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_210)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_210) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_210,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1471,c_1358])).

tff(c_1521,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_1512])).

tff(c_1525,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_86,c_501,c_570,c_1521])).

tff(c_1527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_665,c_1525])).

tff(c_1529,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_626])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_92,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_89])).

tff(c_6,plain,(
    ! [A_6] :
      ( v2_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1528,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_626])).

tff(c_1534,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1528])).

tff(c_1537,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1534])).

tff(c_1541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_50,c_570,c_1537])).

tff(c_1543,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1528])).

tff(c_1775,plain,(
    ! [A_226,B_227,C_228] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_226),u1_struct_0(B_227),C_228),B_227,A_226)
      | ~ v3_tops_2(C_228,A_226,B_227)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_226),u1_struct_0(B_227))))
      | ~ v1_funct_2(C_228,u1_struct_0(A_226),u1_struct_0(B_227))
      | ~ v1_funct_1(C_228)
      | ~ l1_pre_topc(B_227)
      | ~ l1_pre_topc(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1780,plain,(
    ! [B_227,C_228] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_227),C_228),B_227,'#skF_1')
      | ~ v3_tops_2(C_228,'#skF_1',B_227)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_227))))
      | ~ v1_funct_2(C_228,u1_struct_0('#skF_1'),u1_struct_0(B_227))
      | ~ v1_funct_1(C_228)
      | ~ l1_pre_topc(B_227)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1775])).

tff(c_2488,plain,(
    ! [B_287,C_288] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_287),C_288),B_287,'#skF_1')
      | ~ v3_tops_2(C_288,'#skF_1',B_287)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_287))))
      | ~ v1_funct_2(C_288,k2_struct_0('#skF_1'),u1_struct_0(B_287))
      | ~ v1_funct_1(C_288)
      | ~ l1_pre_topc(B_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_72,c_72,c_1780])).

tff(c_2495,plain,(
    ! [C_288] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_288),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_288,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_288,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_288)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_2488])).

tff(c_2507,plain,(
    ! [C_290] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_290),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_290,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_290,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71,c_71,c_2495])).

tff(c_2517,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_2507])).

tff(c_2524,plain,(
    v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_83,c_44,c_569,c_2517])).

tff(c_1542,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1528])).

tff(c_36,plain,(
    ! [A_20,B_21,C_22] :
      ( v1_funct_1(k2_tops_2(A_20,B_21,C_22))
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_620,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_608,c_36])).

tff(c_635,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_598,c_620])).

tff(c_1571,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1542,c_635])).

tff(c_34,plain,(
    ! [A_20,B_21,C_22] :
      ( v1_funct_2(k2_tops_2(A_20,B_21,C_22),B_21,A_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_2(C_22,A_20,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_617,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_608,c_34])).

tff(c_632,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_598,c_617])).

tff(c_1570,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1542,c_632])).

tff(c_12,plain,(
    ! [A_7] :
      ( k2_funct_1(k2_funct_1(A_7)) = A_7
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1576,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1542,c_32])).

tff(c_1580,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_598,c_608,c_1576])).

tff(c_571,plain,(
    ! [C_107,A_108,B_109] :
      ( v2_funct_1(C_107)
      | ~ v3_tops_2(C_107,A_108,B_109)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),u1_struct_0(B_109))))
      | ~ v1_funct_2(C_107,u1_struct_0(A_108),u1_struct_0(B_109))
      | ~ v1_funct_1(C_107)
      | ~ l1_pre_topc(B_109)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_578,plain,(
    ! [C_107,B_109] :
      ( v2_funct_1(C_107)
      | ~ v3_tops_2(C_107,'#skF_1',B_109)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_109))))
      | ~ v1_funct_2(C_107,u1_struct_0('#skF_1'),u1_struct_0(B_109))
      | ~ v1_funct_1(C_107)
      | ~ l1_pre_topc(B_109)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_571])).

tff(c_1592,plain,(
    ! [C_214,B_215] :
      ( v2_funct_1(C_214)
      | ~ v3_tops_2(C_214,'#skF_1',B_215)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_215))))
      | ~ v1_funct_2(C_214,k2_struct_0('#skF_1'),u1_struct_0(B_215))
      | ~ v1_funct_1(C_214)
      | ~ l1_pre_topc(B_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_72,c_578])).

tff(c_1602,plain,(
    ! [C_214] :
      ( v2_funct_1(C_214)
      | ~ v3_tops_2(C_214,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_214,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_214)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1592])).

tff(c_1688,plain,(
    ! [C_219] :
      ( v2_funct_1(C_219)
      | ~ v3_tops_2(C_219,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_219,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71,c_1602])).

tff(c_1691,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1580,c_1688])).

tff(c_1701,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_1570,c_1691])).

tff(c_1706,plain,(
    ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1701])).

tff(c_1709,plain,
    ( ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1706])).

tff(c_1712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_50,c_570,c_44,c_1709])).

tff(c_1714,plain,(
    v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1701])).

tff(c_639,plain,(
    ! [C_110,A_111,B_112] :
      ( v5_pre_topc(C_110,A_111,B_112)
      | ~ v3_tops_2(C_110,A_111,B_112)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_111),u1_struct_0(B_112))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc(B_112)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_646,plain,(
    ! [C_110,B_112] :
      ( v5_pre_topc(C_110,'#skF_1',B_112)
      | ~ v3_tops_2(C_110,'#skF_1',B_112)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_110,u1_struct_0('#skF_1'),u1_struct_0(B_112))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc(B_112)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_639])).

tff(c_1874,plain,(
    ! [C_239,B_240] :
      ( v5_pre_topc(C_239,'#skF_1',B_240)
      | ~ v3_tops_2(C_239,'#skF_1',B_240)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_240))))
      | ~ v1_funct_2(C_239,k2_struct_0('#skF_1'),u1_struct_0(B_240))
      | ~ v1_funct_1(C_239)
      | ~ l1_pre_topc(B_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_72,c_646])).

tff(c_1884,plain,(
    ! [C_239] :
      ( v5_pre_topc(C_239,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_239,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_239,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_239)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1874])).

tff(c_1890,plain,(
    ! [C_241] :
      ( v5_pre_topc(C_241,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_241,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_241,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71,c_1884])).

tff(c_1893,plain,
    ( v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1580,c_1890])).

tff(c_1903,plain,(
    v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1571,c_1570,c_1714,c_1893])).

tff(c_2198,plain,(
    ! [C_254,A_255,B_256] :
      ( v3_tops_2(C_254,A_255,B_256)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_255),u1_struct_0(B_256),C_254),B_256,A_255)
      | ~ v5_pre_topc(C_254,A_255,B_256)
      | ~ v2_funct_1(C_254)
      | k2_relset_1(u1_struct_0(A_255),u1_struct_0(B_256),C_254) != k2_struct_0(B_256)
      | k1_relset_1(u1_struct_0(A_255),u1_struct_0(B_256),C_254) != k2_struct_0(A_255)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_255),u1_struct_0(B_256))))
      | ~ v1_funct_2(C_254,u1_struct_0(A_255),u1_struct_0(B_256))
      | ~ v1_funct_1(C_254)
      | ~ l1_pre_topc(B_256)
      | ~ l1_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2202,plain,(
    ! [C_254,A_255] :
      ( v3_tops_2(C_254,A_255,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_255),k2_struct_0('#skF_1'),C_254),'#skF_1',A_255)
      | ~ v5_pre_topc(C_254,A_255,'#skF_1')
      | ~ v2_funct_1(C_254)
      | k2_relset_1(u1_struct_0(A_255),u1_struct_0('#skF_1'),C_254) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_255),u1_struct_0('#skF_1'),C_254) != k2_struct_0(A_255)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_255),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_254,u1_struct_0(A_255),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_254)
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2198])).

tff(c_3219,plain,(
    ! [C_344,A_345] :
      ( v3_tops_2(C_344,A_345,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_345),k2_struct_0('#skF_1'),C_344),'#skF_1',A_345)
      | ~ v5_pre_topc(C_344,A_345,'#skF_1')
      | ~ v2_funct_1(C_344)
      | k2_relset_1(u1_struct_0(A_345),k2_struct_0('#skF_1'),C_344) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_345),k2_struct_0('#skF_1'),C_344) != k2_struct_0(A_345)
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_345),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_344,u1_struct_0(A_345),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_344)
      | ~ l1_pre_topc(A_345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_72,c_72,c_72,c_72,c_2202])).

tff(c_3223,plain,(
    ! [C_344] :
      ( v3_tops_2(C_344,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_344),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_344,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_344)
      | k2_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_344) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_344) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_344,u1_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_344)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_3219])).

tff(c_3234,plain,(
    ! [C_347] :
      ( v3_tops_2(C_347,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_347),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_347,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_347)
      | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_347) != k2_struct_0('#skF_1')
      | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_347) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_347,k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71,c_71,c_71,c_71,c_3223])).

tff(c_3237,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_608,c_3234])).

tff(c_3244,plain,(
    v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_598,c_2736,c_1529,c_1543,c_2524,c_1903,c_1542,c_3237])).

tff(c_3246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_600,c_3244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.80/2.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.22  
% 5.80/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.23  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.80/2.23  
% 5.80/2.23  %Foreground sorts:
% 5.80/2.23  
% 5.80/2.23  
% 5.80/2.23  %Background operators:
% 5.80/2.23  
% 5.80/2.23  
% 5.80/2.23  %Foreground operators:
% 5.80/2.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.80/2.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.80/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.80/2.23  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.80/2.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.80/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.23  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 5.80/2.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.80/2.23  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.80/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.80/2.23  tff('#skF_2', type, '#skF_2': $i).
% 5.80/2.23  tff('#skF_3', type, '#skF_3': $i).
% 5.80/2.23  tff('#skF_1', type, '#skF_1': $i).
% 5.80/2.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.80/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.80/2.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.80/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.80/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.80/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.23  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.80/2.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.80/2.23  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.80/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.80/2.23  
% 5.80/2.26  tff(f_153, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_tops_2)).
% 5.80/2.26  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.80/2.26  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.80/2.26  tff(f_74, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 5.80/2.26  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_2)).
% 5.80/2.26  tff(f_110, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 5.80/2.26  tff(f_133, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 5.80/2.26  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.80/2.26  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.80/2.26  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 5.80/2.26  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 5.80/2.26  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.80/2.26  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.80/2.26  tff(c_16, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.80/2.26  tff(c_59, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.80/2.26  tff(c_64, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_16, c_59])).
% 5.80/2.26  tff(c_72, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_64])).
% 5.80/2.26  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.80/2.26  tff(c_71, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_64])).
% 5.80/2.26  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.80/2.26  tff(c_74, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_48])).
% 5.80/2.26  tff(c_83, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74])).
% 5.80/2.26  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.80/2.26  tff(c_73, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_46])).
% 5.80/2.26  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_73])).
% 5.80/2.26  tff(c_160, plain, (![A_57, B_58, C_59]: (k2_tops_2(A_57, B_58, C_59)=k2_funct_1(C_59) | ~v2_funct_1(C_59) | k2_relset_1(A_57, B_58, C_59)!=B_58 | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.80/2.26  tff(c_166, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_160])).
% 5.80/2.26  tff(c_170, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_166])).
% 5.80/2.26  tff(c_171, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_170])).
% 5.80/2.26  tff(c_44, plain, (v3_tops_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.80/2.26  tff(c_340, plain, (![A_81, B_82, C_83]: (k2_relset_1(u1_struct_0(A_81), u1_struct_0(B_82), C_83)=k2_struct_0(B_82) | ~v3_tops_2(C_83, A_81, B_82) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81), u1_struct_0(B_82)))) | ~v1_funct_2(C_83, u1_struct_0(A_81), u1_struct_0(B_82)) | ~v1_funct_1(C_83) | ~l1_pre_topc(B_82) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.80/2.26  tff(c_347, plain, (![B_82, C_83]: (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_82), C_83)=k2_struct_0(B_82) | ~v3_tops_2(C_83, '#skF_1', B_82) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_82)))) | ~v1_funct_2(C_83, u1_struct_0('#skF_1'), u1_struct_0(B_82)) | ~v1_funct_1(C_83) | ~l1_pre_topc(B_82) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_340])).
% 5.80/2.26  tff(c_438, plain, (![B_93, C_94]: (k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_93), C_94)=k2_struct_0(B_93) | ~v3_tops_2(C_94, '#skF_1', B_93) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_93)))) | ~v1_funct_2(C_94, k2_struct_0('#skF_1'), u1_struct_0(B_93)) | ~v1_funct_1(C_94) | ~l1_pre_topc(B_93))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_72, c_72, c_347])).
% 5.80/2.26  tff(c_448, plain, (![C_94]: (k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_94)=k2_struct_0('#skF_2') | ~v3_tops_2(C_94, '#skF_1', '#skF_2') | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_94, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_94) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_438])).
% 5.80/2.26  tff(c_486, plain, (![C_99]: (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_99)=k2_struct_0('#skF_2') | ~v3_tops_2(C_99, '#skF_1', '#skF_2') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_99, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_99))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_71, c_71, c_448])).
% 5.80/2.26  tff(c_493, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_486])).
% 5.80/2.26  tff(c_497, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_44, c_493])).
% 5.80/2.26  tff(c_499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_497])).
% 5.80/2.26  tff(c_500, plain, (~v2_funct_1('#skF_3') | k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_170])).
% 5.80/2.26  tff(c_506, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_500])).
% 5.80/2.26  tff(c_507, plain, (![C_100, A_101, B_102]: (v2_funct_1(C_100) | ~v3_tops_2(C_100, A_101, B_102) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101), u1_struct_0(B_102)))) | ~v1_funct_2(C_100, u1_struct_0(A_101), u1_struct_0(B_102)) | ~v1_funct_1(C_100) | ~l1_pre_topc(B_102) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.80/2.26  tff(c_514, plain, (![C_100, B_102]: (v2_funct_1(C_100) | ~v3_tops_2(C_100, '#skF_1', B_102) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_102)))) | ~v1_funct_2(C_100, u1_struct_0('#skF_1'), u1_struct_0(B_102)) | ~v1_funct_1(C_100) | ~l1_pre_topc(B_102) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_507])).
% 5.80/2.26  tff(c_533, plain, (![C_103, B_104]: (v2_funct_1(C_103) | ~v3_tops_2(C_103, '#skF_1', B_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_104)))) | ~v1_funct_2(C_103, k2_struct_0('#skF_1'), u1_struct_0(B_104)) | ~v1_funct_1(C_103) | ~l1_pre_topc(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_72, c_514])).
% 5.80/2.26  tff(c_543, plain, (![C_103]: (v2_funct_1(C_103) | ~v3_tops_2(C_103, '#skF_1', '#skF_2') | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_103, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_103) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_533])).
% 5.80/2.26  tff(c_555, plain, (![C_106]: (v2_funct_1(C_106) | ~v3_tops_2(C_106, '#skF_1', '#skF_2') | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_106, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_106))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_71, c_543])).
% 5.80/2.26  tff(c_562, plain, (v2_funct_1('#skF_3') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_555])).
% 5.80/2.26  tff(c_566, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_44, c_562])).
% 5.80/2.26  tff(c_568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_506, c_566])).
% 5.80/2.26  tff(c_569, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_500])).
% 5.80/2.26  tff(c_42, plain, (~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.80/2.26  tff(c_94, plain, (~v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_71, c_42])).
% 5.80/2.26  tff(c_600, plain, (~v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_569, c_94])).
% 5.80/2.26  tff(c_122, plain, (![A_45, B_46, C_47]: (v1_funct_1(k2_tops_2(A_45, B_46, C_47)) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(C_47, A_45, B_46) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.80/2.26  tff(c_125, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_122])).
% 5.80/2.26  tff(c_128, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_125])).
% 5.80/2.26  tff(c_599, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_128])).
% 5.80/2.26  tff(c_129, plain, (![A_48, B_49, C_50]: (v1_funct_2(k2_tops_2(A_48, B_49, C_50), B_49, A_48) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(C_50, A_48, B_49) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.80/2.26  tff(c_131, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_129])).
% 5.80/2.26  tff(c_134, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_131])).
% 5.80/2.26  tff(c_598, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_134])).
% 5.80/2.26  tff(c_501, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_170])).
% 5.80/2.26  tff(c_570, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_500])).
% 5.80/2.26  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 5.80/2.26  tff(c_1908, plain, (![B_242, A_243, C_244]: (k2_relset_1(u1_struct_0(B_242), u1_struct_0(A_243), k2_tops_2(u1_struct_0(A_243), u1_struct_0(B_242), C_244))=k2_struct_0(A_243) | ~v2_funct_1(C_244) | k2_relset_1(u1_struct_0(A_243), u1_struct_0(B_242), C_244)!=k2_struct_0(B_242) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243), u1_struct_0(B_242)))) | ~v1_funct_2(C_244, u1_struct_0(A_243), u1_struct_0(B_242)) | ~v1_funct_1(C_244) | ~l1_struct_0(B_242) | v2_struct_0(B_242) | ~l1_struct_0(A_243))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.80/2.26  tff(c_1929, plain, (![A_243, C_244]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_243), k2_tops_2(u1_struct_0(A_243), u1_struct_0('#skF_2'), C_244))=k2_struct_0(A_243) | ~v2_funct_1(C_244) | k2_relset_1(u1_struct_0(A_243), u1_struct_0('#skF_2'), C_244)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_244, u1_struct_0(A_243), u1_struct_0('#skF_2')) | ~v1_funct_1(C_244) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_243))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1908])).
% 5.80/2.26  tff(c_1945, plain, (![A_243, C_244]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_243), k2_tops_2(u1_struct_0(A_243), k2_struct_0('#skF_2'), C_244))=k2_struct_0(A_243) | ~v2_funct_1(C_244) | k2_relset_1(u1_struct_0(A_243), k2_struct_0('#skF_2'), C_244)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_244, u1_struct_0(A_243), k2_struct_0('#skF_2')) | ~v1_funct_1(C_244) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_243))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_71, c_71, c_1929])).
% 5.80/2.26  tff(c_1946, plain, (![A_243, C_244]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_243), k2_tops_2(u1_struct_0(A_243), k2_struct_0('#skF_2'), C_244))=k2_struct_0(A_243) | ~v2_funct_1(C_244) | k2_relset_1(u1_struct_0(A_243), k2_struct_0('#skF_2'), C_244)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_244, u1_struct_0(A_243), k2_struct_0('#skF_2')) | ~v1_funct_1(C_244) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_243))), inference(negUnitSimplification, [status(thm)], [c_54, c_1945])).
% 5.80/2.26  tff(c_1972, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1946])).
% 5.80/2.26  tff(c_1975, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1972])).
% 5.80/2.26  tff(c_1979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1975])).
% 5.80/2.26  tff(c_1981, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1946])).
% 5.80/2.26  tff(c_1938, plain, (![A_243, C_244]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_243), k2_tops_2(u1_struct_0(A_243), k2_struct_0('#skF_2'), C_244))=k2_struct_0(A_243) | ~v2_funct_1(C_244) | k2_relset_1(u1_struct_0(A_243), u1_struct_0('#skF_2'), C_244)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_244, u1_struct_0(A_243), u1_struct_0('#skF_2')) | ~v1_funct_1(C_244) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_243))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1908])).
% 5.80/2.26  tff(c_1949, plain, (![A_243, C_244]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_243), k2_tops_2(u1_struct_0(A_243), k2_struct_0('#skF_2'), C_244))=k2_struct_0(A_243) | ~v2_funct_1(C_244) | k2_relset_1(u1_struct_0(A_243), k2_struct_0('#skF_2'), C_244)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_244, u1_struct_0(A_243), k2_struct_0('#skF_2')) | ~v1_funct_1(C_244) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_243))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_71, c_71, c_1938])).
% 5.80/2.26  tff(c_1950, plain, (![A_243, C_244]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_243), k2_tops_2(u1_struct_0(A_243), k2_struct_0('#skF_2'), C_244))=k2_struct_0(A_243) | ~v2_funct_1(C_244) | k2_relset_1(u1_struct_0(A_243), k2_struct_0('#skF_2'), C_244)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_244, u1_struct_0(A_243), k2_struct_0('#skF_2')) | ~v1_funct_1(C_244) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_243))), inference(negUnitSimplification, [status(thm)], [c_54, c_1949])).
% 5.80/2.26  tff(c_2357, plain, (![A_272, C_273]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_272), k2_tops_2(u1_struct_0(A_272), k2_struct_0('#skF_2'), C_273))=k2_struct_0(A_272) | ~v2_funct_1(C_273) | k2_relset_1(u1_struct_0(A_272), k2_struct_0('#skF_2'), C_273)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_272), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_273, u1_struct_0(A_272), k2_struct_0('#skF_2')) | ~v1_funct_1(C_273) | ~l1_struct_0(A_272))), inference(demodulation, [status(thm), theory('equality')], [c_1981, c_1950])).
% 5.80/2.26  tff(c_2369, plain, (![C_273]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_273))=k2_struct_0('#skF_1') | ~v2_funct_1(C_273) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_273)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_273, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_273) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2357])).
% 5.80/2.26  tff(c_2379, plain, (![C_273]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_273))=k2_struct_0('#skF_1') | ~v2_funct_1(C_273) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_273)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_273, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_273) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_72, c_72, c_2369])).
% 5.80/2.26  tff(c_2636, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2379])).
% 5.80/2.26  tff(c_2685, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_2636])).
% 5.80/2.26  tff(c_2689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2685])).
% 5.80/2.26  tff(c_2691, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2379])).
% 5.80/2.26  tff(c_2007, plain, (![B_247, A_248, C_249]: (k1_relset_1(u1_struct_0(B_247), u1_struct_0(A_248), k2_tops_2(u1_struct_0(A_248), u1_struct_0(B_247), C_249))=k2_struct_0(B_247) | ~v2_funct_1(C_249) | k2_relset_1(u1_struct_0(A_248), u1_struct_0(B_247), C_249)!=k2_struct_0(B_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_248), u1_struct_0(B_247)))) | ~v1_funct_2(C_249, u1_struct_0(A_248), u1_struct_0(B_247)) | ~v1_funct_1(C_249) | ~l1_struct_0(B_247) | v2_struct_0(B_247) | ~l1_struct_0(A_248))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.80/2.26  tff(c_2028, plain, (![A_248, C_249]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_248), k2_tops_2(u1_struct_0(A_248), u1_struct_0('#skF_2'), C_249))=k2_struct_0('#skF_2') | ~v2_funct_1(C_249) | k2_relset_1(u1_struct_0(A_248), u1_struct_0('#skF_2'), C_249)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_248), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_249, u1_struct_0(A_248), u1_struct_0('#skF_2')) | ~v1_funct_1(C_249) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_248))), inference(superposition, [status(thm), theory('equality')], [c_71, c_2007])).
% 5.80/2.26  tff(c_2045, plain, (![A_248, C_249]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_248), k2_tops_2(u1_struct_0(A_248), k2_struct_0('#skF_2'), C_249))=k2_struct_0('#skF_2') | ~v2_funct_1(C_249) | k2_relset_1(u1_struct_0(A_248), k2_struct_0('#skF_2'), C_249)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_248), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_249, u1_struct_0(A_248), k2_struct_0('#skF_2')) | ~v1_funct_1(C_249) | v2_struct_0('#skF_2') | ~l1_struct_0(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_1981, c_71, c_71, c_71, c_71, c_2028])).
% 5.80/2.26  tff(c_2091, plain, (![A_250, C_251]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_250), k2_tops_2(u1_struct_0(A_250), k2_struct_0('#skF_2'), C_251))=k2_struct_0('#skF_2') | ~v2_funct_1(C_251) | k2_relset_1(u1_struct_0(A_250), k2_struct_0('#skF_2'), C_251)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_250), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_251, u1_struct_0(A_250), k2_struct_0('#skF_2')) | ~v1_funct_1(C_251) | ~l1_struct_0(A_250))), inference(negUnitSimplification, [status(thm)], [c_54, c_2045])).
% 5.80/2.26  tff(c_2103, plain, (![C_251]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_251))=k2_struct_0('#skF_2') | ~v2_funct_1(C_251) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_251)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_251, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_251) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2091])).
% 5.80/2.26  tff(c_2113, plain, (![C_251]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_251))=k2_struct_0('#skF_2') | ~v2_funct_1(C_251) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_251)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_251, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_251) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_72, c_72, c_2103])).
% 5.80/2.26  tff(c_2718, plain, (![C_311]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_311))=k2_struct_0('#skF_2') | ~v2_funct_1(C_311) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_311)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_311, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_311))), inference(demodulation, [status(thm), theory('equality')], [c_2691, c_2113])).
% 5.80/2.26  tff(c_2730, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_569, c_2718])).
% 5.80/2.26  tff(c_2736, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_86, c_501, c_570, c_2730])).
% 5.80/2.26  tff(c_32, plain, (![A_20, B_21, C_22]: (m1_subset_1(k2_tops_2(A_20, B_21, C_22), k1_zfmisc_1(k2_zfmisc_1(B_21, A_20))) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.80/2.26  tff(c_604, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_569, c_32])).
% 5.80/2.26  tff(c_608, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_86, c_604])).
% 5.80/2.26  tff(c_18, plain, (![A_10, B_11, C_12]: (k2_tops_2(A_10, B_11, C_12)=k2_funct_1(C_12) | ~v2_funct_1(C_12) | k2_relset_1(A_10, B_11, C_12)!=B_11 | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_2(C_12, A_10, B_11) | ~v1_funct_1(C_12))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.80/2.26  tff(c_612, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_608, c_18])).
% 5.80/2.26  tff(c_626, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_598, c_612])).
% 5.80/2.26  tff(c_665, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_626])).
% 5.80/2.26  tff(c_1144, plain, (![B_170, A_171, C_172]: (k1_relset_1(u1_struct_0(B_170), u1_struct_0(A_171), k2_tops_2(u1_struct_0(A_171), u1_struct_0(B_170), C_172))=k2_struct_0(B_170) | ~v2_funct_1(C_172) | k2_relset_1(u1_struct_0(A_171), u1_struct_0(B_170), C_172)!=k2_struct_0(B_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), u1_struct_0(B_170)))) | ~v1_funct_2(C_172, u1_struct_0(A_171), u1_struct_0(B_170)) | ~v1_funct_1(C_172) | ~l1_struct_0(B_170) | v2_struct_0(B_170) | ~l1_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.80/2.26  tff(c_1174, plain, (![A_171, C_172]: (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_171), k2_tops_2(u1_struct_0(A_171), k2_struct_0('#skF_2'), C_172))=k2_struct_0('#skF_2') | ~v2_funct_1(C_172) | k2_relset_1(u1_struct_0(A_171), u1_struct_0('#skF_2'), C_172)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_172, u1_struct_0(A_171), u1_struct_0('#skF_2')) | ~v1_funct_1(C_172) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_171))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1144])).
% 5.80/2.26  tff(c_1185, plain, (![A_171, C_172]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_171), k2_tops_2(u1_struct_0(A_171), k2_struct_0('#skF_2'), C_172))=k2_struct_0('#skF_2') | ~v2_funct_1(C_172) | k2_relset_1(u1_struct_0(A_171), k2_struct_0('#skF_2'), C_172)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_172, u1_struct_0(A_171), k2_struct_0('#skF_2')) | ~v1_funct_1(C_172) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_171))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_71, c_71, c_1174])).
% 5.80/2.26  tff(c_1186, plain, (![A_171, C_172]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_171), k2_tops_2(u1_struct_0(A_171), k2_struct_0('#skF_2'), C_172))=k2_struct_0('#skF_2') | ~v2_funct_1(C_172) | k2_relset_1(u1_struct_0(A_171), k2_struct_0('#skF_2'), C_172)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_172, u1_struct_0(A_171), k2_struct_0('#skF_2')) | ~v1_funct_1(C_172) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_171))), inference(negUnitSimplification, [status(thm)], [c_54, c_1185])).
% 5.80/2.26  tff(c_1218, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1186])).
% 5.80/2.26  tff(c_1221, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1218])).
% 5.80/2.26  tff(c_1225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1221])).
% 5.80/2.26  tff(c_1227, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1186])).
% 5.80/2.26  tff(c_1165, plain, (![A_171, C_172]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_171), k2_tops_2(u1_struct_0(A_171), u1_struct_0('#skF_2'), C_172))=k2_struct_0('#skF_2') | ~v2_funct_1(C_172) | k2_relset_1(u1_struct_0(A_171), u1_struct_0('#skF_2'), C_172)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_172, u1_struct_0(A_171), u1_struct_0('#skF_2')) | ~v1_funct_1(C_172) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_171))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1144])).
% 5.80/2.26  tff(c_1181, plain, (![A_171, C_172]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_171), k2_tops_2(u1_struct_0(A_171), k2_struct_0('#skF_2'), C_172))=k2_struct_0('#skF_2') | ~v2_funct_1(C_172) | k2_relset_1(u1_struct_0(A_171), k2_struct_0('#skF_2'), C_172)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_172, u1_struct_0(A_171), k2_struct_0('#skF_2')) | ~v1_funct_1(C_172) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_171))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_71, c_71, c_71, c_1165])).
% 5.80/2.26  tff(c_1182, plain, (![A_171, C_172]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_171), k2_tops_2(u1_struct_0(A_171), k2_struct_0('#skF_2'), C_172))=k2_struct_0('#skF_2') | ~v2_funct_1(C_172) | k2_relset_1(u1_struct_0(A_171), k2_struct_0('#skF_2'), C_172)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_172, u1_struct_0(A_171), k2_struct_0('#skF_2')) | ~v1_funct_1(C_172) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_171))), inference(negUnitSimplification, [status(thm)], [c_54, c_1181])).
% 5.80/2.26  tff(c_1426, plain, (![A_203, C_204]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_203), k2_tops_2(u1_struct_0(A_203), k2_struct_0('#skF_2'), C_204))=k2_struct_0('#skF_2') | ~v2_funct_1(C_204) | k2_relset_1(u1_struct_0(A_203), k2_struct_0('#skF_2'), C_204)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_203), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_204, u1_struct_0(A_203), k2_struct_0('#skF_2')) | ~v1_funct_1(C_204) | ~l1_struct_0(A_203))), inference(demodulation, [status(thm), theory('equality')], [c_1227, c_1182])).
% 5.80/2.26  tff(c_1438, plain, (![C_204]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_204))=k2_struct_0('#skF_2') | ~v2_funct_1(C_204) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_204)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_204, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_204) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1426])).
% 5.80/2.26  tff(c_1448, plain, (![C_204]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_204))=k2_struct_0('#skF_2') | ~v2_funct_1(C_204) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_204)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_204, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_204) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_72, c_72, c_1438])).
% 5.80/2.26  tff(c_1462, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1448])).
% 5.80/2.26  tff(c_1465, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1462])).
% 5.80/2.26  tff(c_1469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1465])).
% 5.80/2.26  tff(c_1471, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1448])).
% 5.80/2.26  tff(c_1258, plain, (![B_180, A_181, C_182]: (k2_relset_1(u1_struct_0(B_180), u1_struct_0(A_181), k2_tops_2(u1_struct_0(A_181), u1_struct_0(B_180), C_182))=k2_struct_0(A_181) | ~v2_funct_1(C_182) | k2_relset_1(u1_struct_0(A_181), u1_struct_0(B_180), C_182)!=k2_struct_0(B_180) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181), u1_struct_0(B_180)))) | ~v1_funct_2(C_182, u1_struct_0(A_181), u1_struct_0(B_180)) | ~v1_funct_1(C_182) | ~l1_struct_0(B_180) | v2_struct_0(B_180) | ~l1_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.80/2.26  tff(c_1288, plain, (![A_181, C_182]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_181), k2_tops_2(u1_struct_0(A_181), k2_struct_0('#skF_2'), C_182))=k2_struct_0(A_181) | ~v2_funct_1(C_182) | k2_relset_1(u1_struct_0(A_181), u1_struct_0('#skF_2'), C_182)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_182, u1_struct_0(A_181), u1_struct_0('#skF_2')) | ~v1_funct_1(C_182) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_181))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1258])).
% 5.80/2.26  tff(c_1303, plain, (![A_181, C_182]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_181), k2_tops_2(u1_struct_0(A_181), k2_struct_0('#skF_2'), C_182))=k2_struct_0(A_181) | ~v2_funct_1(C_182) | k2_relset_1(u1_struct_0(A_181), k2_struct_0('#skF_2'), C_182)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_182, u1_struct_0(A_181), k2_struct_0('#skF_2')) | ~v1_funct_1(C_182) | v2_struct_0('#skF_2') | ~l1_struct_0(A_181))), inference(demodulation, [status(thm), theory('equality')], [c_1227, c_71, c_71, c_71, c_71, c_1288])).
% 5.80/2.26  tff(c_1337, plain, (![A_188, C_189]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_188), k2_tops_2(u1_struct_0(A_188), k2_struct_0('#skF_2'), C_189))=k2_struct_0(A_188) | ~v2_funct_1(C_189) | k2_relset_1(u1_struct_0(A_188), k2_struct_0('#skF_2'), C_189)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_189, u1_struct_0(A_188), k2_struct_0('#skF_2')) | ~v1_funct_1(C_189) | ~l1_struct_0(A_188))), inference(negUnitSimplification, [status(thm)], [c_54, c_1303])).
% 5.80/2.26  tff(c_1346, plain, (![C_189]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_189))=k2_struct_0('#skF_1') | ~v2_funct_1(C_189) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_189)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_189, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_189) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1337])).
% 5.80/2.26  tff(c_1358, plain, (![C_189]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_189))=k2_struct_0('#skF_1') | ~v2_funct_1(C_189) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_189)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_189, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_189) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_72, c_72, c_1346])).
% 5.80/2.26  tff(c_1512, plain, (![C_210]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_210))=k2_struct_0('#skF_1') | ~v2_funct_1(C_210) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_210)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_210, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_210))), inference(demodulation, [status(thm), theory('equality')], [c_1471, c_1358])).
% 5.80/2.26  tff(c_1521, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_569, c_1512])).
% 5.80/2.26  tff(c_1525, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_86, c_501, c_570, c_1521])).
% 5.80/2.26  tff(c_1527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_665, c_1525])).
% 5.80/2.26  tff(c_1529, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_626])).
% 5.80/2.26  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.80/2.26  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.80/2.26  tff(c_89, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_86, c_2])).
% 5.80/2.26  tff(c_92, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_89])).
% 5.80/2.26  tff(c_6, plain, (![A_6]: (v2_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.80/2.26  tff(c_1528, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_626])).
% 5.80/2.26  tff(c_1534, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1528])).
% 5.80/2.26  tff(c_1537, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1534])).
% 5.80/2.26  tff(c_1541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_50, c_570, c_1537])).
% 5.80/2.26  tff(c_1543, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1528])).
% 5.80/2.26  tff(c_1775, plain, (![A_226, B_227, C_228]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_226), u1_struct_0(B_227), C_228), B_227, A_226) | ~v3_tops_2(C_228, A_226, B_227) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_226), u1_struct_0(B_227)))) | ~v1_funct_2(C_228, u1_struct_0(A_226), u1_struct_0(B_227)) | ~v1_funct_1(C_228) | ~l1_pre_topc(B_227) | ~l1_pre_topc(A_226))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.80/2.26  tff(c_1780, plain, (![B_227, C_228]: (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_227), C_228), B_227, '#skF_1') | ~v3_tops_2(C_228, '#skF_1', B_227) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_227)))) | ~v1_funct_2(C_228, u1_struct_0('#skF_1'), u1_struct_0(B_227)) | ~v1_funct_1(C_228) | ~l1_pre_topc(B_227) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1775])).
% 5.80/2.26  tff(c_2488, plain, (![B_287, C_288]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_287), C_288), B_287, '#skF_1') | ~v3_tops_2(C_288, '#skF_1', B_287) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_287)))) | ~v1_funct_2(C_288, k2_struct_0('#skF_1'), u1_struct_0(B_287)) | ~v1_funct_1(C_288) | ~l1_pre_topc(B_287))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_72, c_72, c_1780])).
% 5.80/2.26  tff(c_2495, plain, (![C_288]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_288), '#skF_2', '#skF_1') | ~v3_tops_2(C_288, '#skF_1', '#skF_2') | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_288, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_288) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_2488])).
% 5.80/2.26  tff(c_2507, plain, (![C_290]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_290), '#skF_2', '#skF_1') | ~v3_tops_2(C_290, '#skF_1', '#skF_2') | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_290, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_290))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_71, c_71, c_2495])).
% 5.80/2.26  tff(c_2517, plain, (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_2507])).
% 5.80/2.26  tff(c_2524, plain, (v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_83, c_44, c_569, c_2517])).
% 5.80/2.26  tff(c_1542, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1528])).
% 5.80/2.26  tff(c_36, plain, (![A_20, B_21, C_22]: (v1_funct_1(k2_tops_2(A_20, B_21, C_22)) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.80/2.26  tff(c_620, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_608, c_36])).
% 5.80/2.26  tff(c_635, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_598, c_620])).
% 5.80/2.26  tff(c_1571, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1542, c_635])).
% 5.80/2.26  tff(c_34, plain, (![A_20, B_21, C_22]: (v1_funct_2(k2_tops_2(A_20, B_21, C_22), B_21, A_20) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_2(C_22, A_20, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.80/2.26  tff(c_617, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_608, c_34])).
% 5.80/2.26  tff(c_632, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_598, c_617])).
% 5.80/2.26  tff(c_1570, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1542, c_632])).
% 5.80/2.26  tff(c_12, plain, (![A_7]: (k2_funct_1(k2_funct_1(A_7))=A_7 | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.80/2.26  tff(c_1576, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1542, c_32])).
% 5.80/2.26  tff(c_1580, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_598, c_608, c_1576])).
% 5.80/2.26  tff(c_571, plain, (![C_107, A_108, B_109]: (v2_funct_1(C_107) | ~v3_tops_2(C_107, A_108, B_109) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108), u1_struct_0(B_109)))) | ~v1_funct_2(C_107, u1_struct_0(A_108), u1_struct_0(B_109)) | ~v1_funct_1(C_107) | ~l1_pre_topc(B_109) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.80/2.26  tff(c_578, plain, (![C_107, B_109]: (v2_funct_1(C_107) | ~v3_tops_2(C_107, '#skF_1', B_109) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_109)))) | ~v1_funct_2(C_107, u1_struct_0('#skF_1'), u1_struct_0(B_109)) | ~v1_funct_1(C_107) | ~l1_pre_topc(B_109) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_571])).
% 5.80/2.26  tff(c_1592, plain, (![C_214, B_215]: (v2_funct_1(C_214) | ~v3_tops_2(C_214, '#skF_1', B_215) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_215)))) | ~v1_funct_2(C_214, k2_struct_0('#skF_1'), u1_struct_0(B_215)) | ~v1_funct_1(C_214) | ~l1_pre_topc(B_215))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_72, c_578])).
% 5.80/2.26  tff(c_1602, plain, (![C_214]: (v2_funct_1(C_214) | ~v3_tops_2(C_214, '#skF_1', '#skF_2') | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_214, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_214) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1592])).
% 5.80/2.26  tff(c_1688, plain, (![C_219]: (v2_funct_1(C_219) | ~v3_tops_2(C_219, '#skF_1', '#skF_2') | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_219, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_219))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_71, c_1602])).
% 5.80/2.26  tff(c_1691, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1580, c_1688])).
% 5.80/2.26  tff(c_1701, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1571, c_1570, c_1691])).
% 5.80/2.26  tff(c_1706, plain, (~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_1701])).
% 5.80/2.26  tff(c_1709, plain, (~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_1706])).
% 5.80/2.26  tff(c_1712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_50, c_570, c_44, c_1709])).
% 5.80/2.26  tff(c_1714, plain, (v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1701])).
% 5.80/2.26  tff(c_639, plain, (![C_110, A_111, B_112]: (v5_pre_topc(C_110, A_111, B_112) | ~v3_tops_2(C_110, A_111, B_112) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111), u1_struct_0(B_112)))) | ~v1_funct_2(C_110, u1_struct_0(A_111), u1_struct_0(B_112)) | ~v1_funct_1(C_110) | ~l1_pre_topc(B_112) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.80/2.26  tff(c_646, plain, (![C_110, B_112]: (v5_pre_topc(C_110, '#skF_1', B_112) | ~v3_tops_2(C_110, '#skF_1', B_112) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_112)))) | ~v1_funct_2(C_110, u1_struct_0('#skF_1'), u1_struct_0(B_112)) | ~v1_funct_1(C_110) | ~l1_pre_topc(B_112) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_639])).
% 5.80/2.26  tff(c_1874, plain, (![C_239, B_240]: (v5_pre_topc(C_239, '#skF_1', B_240) | ~v3_tops_2(C_239, '#skF_1', B_240) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_240)))) | ~v1_funct_2(C_239, k2_struct_0('#skF_1'), u1_struct_0(B_240)) | ~v1_funct_1(C_239) | ~l1_pre_topc(B_240))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_72, c_646])).
% 5.80/2.26  tff(c_1884, plain, (![C_239]: (v5_pre_topc(C_239, '#skF_1', '#skF_2') | ~v3_tops_2(C_239, '#skF_1', '#skF_2') | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_239, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_239) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_1874])).
% 5.80/2.26  tff(c_1890, plain, (![C_241]: (v5_pre_topc(C_241, '#skF_1', '#skF_2') | ~v3_tops_2(C_241, '#skF_1', '#skF_2') | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_241, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_241))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_71, c_1884])).
% 5.80/2.26  tff(c_1893, plain, (v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1580, c_1890])).
% 5.80/2.26  tff(c_1903, plain, (v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1571, c_1570, c_1714, c_1893])).
% 5.80/2.26  tff(c_2198, plain, (![C_254, A_255, B_256]: (v3_tops_2(C_254, A_255, B_256) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_255), u1_struct_0(B_256), C_254), B_256, A_255) | ~v5_pre_topc(C_254, A_255, B_256) | ~v2_funct_1(C_254) | k2_relset_1(u1_struct_0(A_255), u1_struct_0(B_256), C_254)!=k2_struct_0(B_256) | k1_relset_1(u1_struct_0(A_255), u1_struct_0(B_256), C_254)!=k2_struct_0(A_255) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_255), u1_struct_0(B_256)))) | ~v1_funct_2(C_254, u1_struct_0(A_255), u1_struct_0(B_256)) | ~v1_funct_1(C_254) | ~l1_pre_topc(B_256) | ~l1_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.80/2.26  tff(c_2202, plain, (![C_254, A_255]: (v3_tops_2(C_254, A_255, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_255), k2_struct_0('#skF_1'), C_254), '#skF_1', A_255) | ~v5_pre_topc(C_254, A_255, '#skF_1') | ~v2_funct_1(C_254) | k2_relset_1(u1_struct_0(A_255), u1_struct_0('#skF_1'), C_254)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_255), u1_struct_0('#skF_1'), C_254)!=k2_struct_0(A_255) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_255), u1_struct_0('#skF_1')))) | ~v1_funct_2(C_254, u1_struct_0(A_255), u1_struct_0('#skF_1')) | ~v1_funct_1(C_254) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_255))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2198])).
% 5.80/2.26  tff(c_3219, plain, (![C_344, A_345]: (v3_tops_2(C_344, A_345, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_345), k2_struct_0('#skF_1'), C_344), '#skF_1', A_345) | ~v5_pre_topc(C_344, A_345, '#skF_1') | ~v2_funct_1(C_344) | k2_relset_1(u1_struct_0(A_345), k2_struct_0('#skF_1'), C_344)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_345), k2_struct_0('#skF_1'), C_344)!=k2_struct_0(A_345) | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_345), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_344, u1_struct_0(A_345), k2_struct_0('#skF_1')) | ~v1_funct_1(C_344) | ~l1_pre_topc(A_345))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_72, c_72, c_72, c_72, c_2202])).
% 5.80/2.26  tff(c_3223, plain, (![C_344]: (v3_tops_2(C_344, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_344), '#skF_1', '#skF_2') | ~v5_pre_topc(C_344, '#skF_2', '#skF_1') | ~v2_funct_1(C_344) | k2_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_344)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_344)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_344, u1_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_344) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_3219])).
% 5.80/2.26  tff(c_3234, plain, (![C_347]: (v3_tops_2(C_347, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_347), '#skF_1', '#skF_2') | ~v5_pre_topc(C_347, '#skF_2', '#skF_1') | ~v2_funct_1(C_347) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_347)!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_347)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_347, k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_347))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_71, c_71, c_71, c_71, c_3223])).
% 5.80/2.26  tff(c_3237, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_608, c_3234])).
% 5.80/2.26  tff(c_3244, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_599, c_598, c_2736, c_1529, c_1543, c_2524, c_1903, c_1542, c_3237])).
% 5.80/2.26  tff(c_3246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_600, c_3244])).
% 5.80/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.26  
% 5.80/2.26  Inference rules
% 5.80/2.26  ----------------------
% 5.80/2.26  #Ref     : 0
% 5.80/2.26  #Sup     : 616
% 5.80/2.26  #Fact    : 0
% 5.80/2.26  #Define  : 0
% 5.80/2.26  #Split   : 11
% 5.80/2.26  #Chain   : 0
% 5.80/2.26  #Close   : 0
% 5.80/2.26  
% 5.80/2.26  Ordering : KBO
% 6.17/2.26  
% 6.17/2.26  Simplification rules
% 6.17/2.26  ----------------------
% 6.17/2.26  #Subsume      : 108
% 6.17/2.26  #Demod        : 1672
% 6.17/2.26  #Tautology    : 148
% 6.17/2.26  #SimpNegUnit  : 21
% 6.17/2.26  #BackRed      : 15
% 6.17/2.26  
% 6.17/2.26  #Partial instantiations: 0
% 6.17/2.26  #Strategies tried      : 1
% 6.17/2.26  
% 6.17/2.26  Timing (in seconds)
% 6.17/2.26  ----------------------
% 6.17/2.27  Preprocessing        : 0.35
% 6.17/2.27  Parsing              : 0.18
% 6.17/2.27  CNF conversion       : 0.03
% 6.17/2.27  Main loop            : 0.99
% 6.17/2.27  Inferencing          : 0.34
% 6.17/2.27  Reduction            : 0.39
% 6.17/2.27  Demodulation         : 0.29
% 6.17/2.27  BG Simplification    : 0.04
% 6.17/2.27  Subsumption          : 0.16
% 6.17/2.27  Abstraction          : 0.05
% 6.17/2.27  MUC search           : 0.00
% 6.17/2.27  Cooper               : 0.00
% 6.17/2.27  Total                : 1.42
% 6.17/2.27  Index Insertion      : 0.00
% 6.17/2.27  Index Deletion       : 0.00
% 6.17/2.27  Index Matching       : 0.00
% 6.17/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
