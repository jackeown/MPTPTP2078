%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:49 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  183 (8811 expanded)
%              Number of leaves         :   34 (2988 expanded)
%              Depth                    :   23
%              Number of atoms          :  608 (24629 expanded)
%              Number of equality atoms :   97 (4117 expanded)
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

tff(f_148,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_93,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_128,axiom,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_48,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_14,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_14,c_56])).

tff(c_69,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_61])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_68,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_61])).

tff(c_46,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_71,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46])).

tff(c_80,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_71])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_44])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_70])).

tff(c_153,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_tops_2(A_54,B_55,C_56) = k2_funct_1(C_56)
      | ~ v2_funct_1(C_56)
      | k2_relset_1(A_54,B_55,C_56) != B_55
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_159,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_153])).

tff(c_163,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_159])).

tff(c_164,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_42,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_345,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(u1_struct_0(A_79),u1_struct_0(B_80),C_81) = k2_struct_0(B_80)
      | ~ v3_tops_2(C_81,A_79,B_80)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_79),u1_struct_0(B_80))))
      | ~ v1_funct_2(C_81,u1_struct_0(A_79),u1_struct_0(B_80))
      | ~ v1_funct_1(C_81)
      | ~ l1_pre_topc(B_80)
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_352,plain,(
    ! [B_80,C_81] :
      ( k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_80),C_81) = k2_struct_0(B_80)
      | ~ v3_tops_2(C_81,'#skF_1',B_80)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_80))))
      | ~ v1_funct_2(C_81,u1_struct_0('#skF_1'),u1_struct_0(B_80))
      | ~ v1_funct_1(C_81)
      | ~ l1_pre_topc(B_80)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_345])).

tff(c_431,plain,(
    ! [B_90,C_91] :
      ( k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_90),C_91) = k2_struct_0(B_90)
      | ~ v3_tops_2(C_91,'#skF_1',B_90)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_90))))
      | ~ v1_funct_2(C_91,k2_struct_0('#skF_1'),u1_struct_0(B_90))
      | ~ v1_funct_1(C_91)
      | ~ l1_pre_topc(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69,c_69,c_352])).

tff(c_441,plain,(
    ! [C_91] :
      ( k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_91) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_91,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_91,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_91)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_431])).

tff(c_453,plain,(
    ! [C_93] :
      ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_93) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_93,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_93,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_68,c_441])).

tff(c_460,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_453])).

tff(c_464,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_42,c_460])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_464])).

tff(c_467,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_499,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_469,plain,(
    ! [C_94,A_95,B_96] :
      ( v2_funct_1(C_94)
      | ~ v3_tops_2(C_94,A_95,B_96)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95),u1_struct_0(B_96))))
      | ~ v1_funct_2(C_94,u1_struct_0(A_95),u1_struct_0(B_96))
      | ~ v1_funct_1(C_94)
      | ~ l1_pre_topc(B_96)
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_476,plain,(
    ! [C_94,B_96] :
      ( v2_funct_1(C_94)
      | ~ v3_tops_2(C_94,'#skF_1',B_96)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_96))))
      | ~ v1_funct_2(C_94,u1_struct_0('#skF_1'),u1_struct_0(B_96))
      | ~ v1_funct_1(C_94)
      | ~ l1_pre_topc(B_96)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_469])).

tff(c_528,plain,(
    ! [C_101,B_102] :
      ( v2_funct_1(C_101)
      | ~ v3_tops_2(C_101,'#skF_1',B_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_102))))
      | ~ v1_funct_2(C_101,k2_struct_0('#skF_1'),u1_struct_0(B_102))
      | ~ v1_funct_1(C_101)
      | ~ l1_pre_topc(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69,c_476])).

tff(c_538,plain,(
    ! [C_101] :
      ( v2_funct_1(C_101)
      | ~ v3_tops_2(C_101,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_101,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_101)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_528])).

tff(c_544,plain,(
    ! [C_103] :
      ( v2_funct_1(C_103)
      | ~ v3_tops_2(C_103,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_103,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_538])).

tff(c_551,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_544])).

tff(c_555,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_42,c_551])).

tff(c_557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_555])).

tff(c_558,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_40,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_88,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_68,c_40])).

tff(c_589,plain,(
    ~ v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_88])).

tff(c_117,plain,(
    ! [A_42,B_43,C_44] :
      ( v1_funct_1(k2_tops_2(A_42,B_43,C_44))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(C_44,A_42,B_43)
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_120,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_117])).

tff(c_123,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_120])).

tff(c_588,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_123])).

tff(c_124,plain,(
    ! [A_45,B_46,C_47] :
      ( v1_funct_2(k2_tops_2(A_45,B_46,C_47),B_46,A_45)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_126,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_124])).

tff(c_129,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_126])).

tff(c_587,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_129])).

tff(c_468,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_559,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1763,plain,(
    ! [B_226,A_227,C_228] :
      ( k1_relset_1(u1_struct_0(B_226),u1_struct_0(A_227),k2_tops_2(u1_struct_0(A_227),u1_struct_0(B_226),C_228)) = k2_struct_0(B_226)
      | ~ v2_funct_1(C_228)
      | k2_relset_1(u1_struct_0(A_227),u1_struct_0(B_226),C_228) != k2_struct_0(B_226)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227),u1_struct_0(B_226))))
      | ~ v1_funct_2(C_228,u1_struct_0(A_227),u1_struct_0(B_226))
      | ~ v1_funct_1(C_228)
      | ~ l1_struct_0(B_226)
      | v2_struct_0(B_226)
      | ~ l1_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1793,plain,(
    ! [A_227,C_228] :
      ( k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_227),k2_tops_2(u1_struct_0(A_227),k2_struct_0('#skF_2'),C_228)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_228)
      | k2_relset_1(u1_struct_0(A_227),u1_struct_0('#skF_2'),C_228) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_228,u1_struct_0(A_227),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_228)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1763])).

tff(c_1804,plain,(
    ! [A_227,C_228] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_227),k2_tops_2(u1_struct_0(A_227),k2_struct_0('#skF_2'),C_228)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_228)
      | k2_relset_1(u1_struct_0(A_227),k2_struct_0('#skF_2'),C_228) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_228,u1_struct_0(A_227),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_228)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_68,c_68,c_1793])).

tff(c_1805,plain,(
    ! [A_227,C_228] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_227),k2_tops_2(u1_struct_0(A_227),k2_struct_0('#skF_2'),C_228)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_228)
      | k2_relset_1(u1_struct_0(A_227),k2_struct_0('#skF_2'),C_228) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_228,u1_struct_0(A_227),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_228)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_227) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1804])).

tff(c_1840,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1805])).

tff(c_1843,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1840])).

tff(c_1847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1843])).

tff(c_1849,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1805])).

tff(c_1784,plain,(
    ! [A_227,C_228] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_227),k2_tops_2(u1_struct_0(A_227),u1_struct_0('#skF_2'),C_228)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_228)
      | k2_relset_1(u1_struct_0(A_227),u1_struct_0('#skF_2'),C_228) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_228,u1_struct_0(A_227),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_228)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1763])).

tff(c_1800,plain,(
    ! [A_227,C_228] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_227),k2_tops_2(u1_struct_0(A_227),k2_struct_0('#skF_2'),C_228)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_228)
      | k2_relset_1(u1_struct_0(A_227),k2_struct_0('#skF_2'),C_228) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_228,u1_struct_0(A_227),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_228)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_68,c_68,c_1784])).

tff(c_1801,plain,(
    ! [A_227,C_228] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_227),k2_tops_2(u1_struct_0(A_227),k2_struct_0('#skF_2'),C_228)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_228)
      | k2_relset_1(u1_struct_0(A_227),k2_struct_0('#skF_2'),C_228) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_228,u1_struct_0(A_227),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_228)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_227) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1800])).

tff(c_2223,plain,(
    ! [A_258,C_259] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_258),k2_tops_2(u1_struct_0(A_258),k2_struct_0('#skF_2'),C_259)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_259)
      | k2_relset_1(u1_struct_0(A_258),k2_struct_0('#skF_2'),C_259) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_258),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_259,u1_struct_0(A_258),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_259)
      | ~ l1_struct_0(A_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1849,c_1801])).

tff(c_2235,plain,(
    ! [C_259] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_259)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_259)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_259) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_259,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_259)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_2223])).

tff(c_2245,plain,(
    ! [C_259] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_259)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_259)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_259) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_259,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_259)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_69,c_69,c_2235])).

tff(c_2611,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2245])).

tff(c_2614,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_2611])).

tff(c_2618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2614])).

tff(c_2626,plain,(
    ! [C_302] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_302)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_302)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_302) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_302,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_302) ) ),
    inference(splitRight,[status(thm)],[c_2245])).

tff(c_2638,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_2626])).

tff(c_2644,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_82,c_468,c_559,c_2638])).

tff(c_30,plain,(
    ! [A_18,B_19,C_20] :
      ( m1_subset_1(k2_tops_2(A_18,B_19,C_20),k1_zfmisc_1(k2_zfmisc_1(B_19,A_18)))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_593,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_30])).

tff(c_597,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_82,c_593])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( k2_tops_2(A_8,B_9,C_10) = k2_funct_1(C_10)
      | ~ v2_funct_1(C_10)
      | k2_relset_1(A_8,B_9,C_10) != B_9
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_601,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_597,c_16])).

tff(c_615,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_587,c_601])).

tff(c_653,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_615])).

tff(c_991,plain,(
    ! [B_151,A_152,C_153] :
      ( k2_relset_1(u1_struct_0(B_151),u1_struct_0(A_152),k2_tops_2(u1_struct_0(A_152),u1_struct_0(B_151),C_153)) = k2_struct_0(A_152)
      | ~ v2_funct_1(C_153)
      | k2_relset_1(u1_struct_0(A_152),u1_struct_0(B_151),C_153) != k2_struct_0(B_151)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152),u1_struct_0(B_151))))
      | ~ v1_funct_2(C_153,u1_struct_0(A_152),u1_struct_0(B_151))
      | ~ v1_funct_1(C_153)
      | ~ l1_struct_0(B_151)
      | v2_struct_0(B_151)
      | ~ l1_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1012,plain,(
    ! [A_152,C_153] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_152),k2_tops_2(u1_struct_0(A_152),u1_struct_0('#skF_2'),C_153)) = k2_struct_0(A_152)
      | ~ v2_funct_1(C_153)
      | k2_relset_1(u1_struct_0(A_152),u1_struct_0('#skF_2'),C_153) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_153,u1_struct_0(A_152),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_153)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_991])).

tff(c_1028,plain,(
    ! [A_152,C_153] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_152),k2_tops_2(u1_struct_0(A_152),k2_struct_0('#skF_2'),C_153)) = k2_struct_0(A_152)
      | ~ v2_funct_1(C_153)
      | k2_relset_1(u1_struct_0(A_152),k2_struct_0('#skF_2'),C_153) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_153,u1_struct_0(A_152),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_153)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_68,c_68,c_1012])).

tff(c_1029,plain,(
    ! [A_152,C_153] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_152),k2_tops_2(u1_struct_0(A_152),k2_struct_0('#skF_2'),C_153)) = k2_struct_0(A_152)
      | ~ v2_funct_1(C_153)
      | k2_relset_1(u1_struct_0(A_152),k2_struct_0('#skF_2'),C_153) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_153,u1_struct_0(A_152),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_153)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_152) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1028])).

tff(c_1066,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1029])).

tff(c_1069,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1066])).

tff(c_1073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1069])).

tff(c_1386,plain,(
    ! [A_197,C_198] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_197),k2_tops_2(u1_struct_0(A_197),k2_struct_0('#skF_2'),C_198)) = k2_struct_0(A_197)
      | ~ v2_funct_1(C_198)
      | k2_relset_1(u1_struct_0(A_197),k2_struct_0('#skF_2'),C_198) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_197),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_198,u1_struct_0(A_197),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_198)
      | ~ l1_struct_0(A_197) ) ),
    inference(splitRight,[status(thm)],[c_1029])).

tff(c_1398,plain,(
    ! [C_198] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_198)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_198)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_198) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_198,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_198)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_1386])).

tff(c_1408,plain,(
    ! [C_198] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_198)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_198)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_198) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_198,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_198)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_69,c_69,c_1398])).

tff(c_1424,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1408])).

tff(c_1427,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_1424])).

tff(c_1431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1427])).

tff(c_1452,plain,(
    ! [C_203] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_203)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_203)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_203) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_203,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_203) ) ),
    inference(splitRight,[status(thm)],[c_1408])).

tff(c_1461,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_1452])).

tff(c_1465,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_82,c_468,c_559,c_1461])).

tff(c_1467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_653,c_1465])).

tff(c_1469,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_86,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_10])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1468,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_1474,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1468])).

tff(c_1493,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_1474])).

tff(c_1497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_48,c_559,c_1493])).

tff(c_1499,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1468])).

tff(c_1644,plain,(
    ! [A_212,B_213,C_214] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_212),u1_struct_0(B_213),C_214),B_213,A_212)
      | ~ v3_tops_2(C_214,A_212,B_213)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_212),u1_struct_0(B_213))))
      | ~ v1_funct_2(C_214,u1_struct_0(A_212),u1_struct_0(B_213))
      | ~ v1_funct_1(C_214)
      | ~ l1_pre_topc(B_213)
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1649,plain,(
    ! [B_213,C_214] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_213),C_214),B_213,'#skF_1')
      | ~ v3_tops_2(C_214,'#skF_1',B_213)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_213))))
      | ~ v1_funct_2(C_214,u1_struct_0('#skF_1'),u1_struct_0(B_213))
      | ~ v1_funct_1(C_214)
      | ~ l1_pre_topc(B_213)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_1644])).

tff(c_2417,plain,(
    ! [B_279,C_280] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_279),C_280),B_279,'#skF_1')
      | ~ v3_tops_2(C_280,'#skF_1',B_279)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_279))))
      | ~ v1_funct_2(C_280,k2_struct_0('#skF_1'),u1_struct_0(B_279))
      | ~ v1_funct_1(C_280)
      | ~ l1_pre_topc(B_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69,c_69,c_1649])).

tff(c_2424,plain,(
    ! [C_280] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_280),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_280,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_280,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_280)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2417])).

tff(c_2452,plain,(
    ! [C_285] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_285),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_285,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_285,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_68,c_2424])).

tff(c_2462,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2452])).

tff(c_2469,plain,(
    v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_80,c_42,c_558,c_2462])).

tff(c_1498,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1468])).

tff(c_34,plain,(
    ! [A_18,B_19,C_20] :
      ( v1_funct_1(k2_tops_2(A_18,B_19,C_20))
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_609,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_597,c_34])).

tff(c_624,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_587,c_609])).

tff(c_1501,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_624])).

tff(c_32,plain,(
    ! [A_18,B_19,C_20] :
      ( v1_funct_2(k2_tops_2(A_18,B_19,C_20),B_19,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_606,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_597,c_32])).

tff(c_621,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_587,c_606])).

tff(c_1500,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1498,c_621])).

tff(c_8,plain,(
    ! [A_2] :
      ( k2_funct_1(k2_funct_1(A_2)) = A_2
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1506,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_30])).

tff(c_1510,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_587,c_597,c_1506])).

tff(c_485,plain,(
    ! [C_94,A_95] :
      ( v2_funct_1(C_94)
      | ~ v3_tops_2(C_94,A_95,'#skF_2')
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_94,u1_struct_0(A_95),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_94)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_469])).

tff(c_1591,plain,(
    ! [C_209,A_210] :
      ( v2_funct_1(C_209)
      | ~ v3_tops_2(C_209,A_210,'#skF_2')
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_210),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_209,u1_struct_0(A_210),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_209)
      | ~ l1_pre_topc(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_485])).

tff(c_1598,plain,(
    ! [C_209] :
      ( v2_funct_1(C_209)
      | ~ v3_tops_2(C_209,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_209,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_209)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_1591])).

tff(c_1617,plain,(
    ! [C_211] :
      ( v2_funct_1(C_211)
      | ~ v3_tops_2(C_211,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_211,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69,c_1598])).

tff(c_1620,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1510,c_1617])).

tff(c_1630,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_1500,c_1620])).

tff(c_1635,plain,(
    ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1630])).

tff(c_1638,plain,
    ( ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1635])).

tff(c_1641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_48,c_559,c_42,c_1638])).

tff(c_1643,plain,(
    v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1630])).

tff(c_560,plain,(
    ! [C_104,A_105,B_106] :
      ( v5_pre_topc(C_104,A_105,B_106)
      | ~ v3_tops_2(C_104,A_105,B_106)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),u1_struct_0(B_106))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_105),u1_struct_0(B_106))
      | ~ v1_funct_1(C_104)
      | ~ l1_pre_topc(B_106)
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_576,plain,(
    ! [C_104,A_105] :
      ( v5_pre_topc(C_104,A_105,'#skF_2')
      | ~ v3_tops_2(C_104,A_105,'#skF_2')
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_105),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_104)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_560])).

tff(c_1824,plain,(
    ! [C_231,A_232] :
      ( v5_pre_topc(C_231,A_232,'#skF_2')
      | ~ v3_tops_2(C_231,A_232,'#skF_2')
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_232),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_231,u1_struct_0(A_232),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_231)
      | ~ l1_pre_topc(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_576])).

tff(c_1831,plain,(
    ! [C_231] :
      ( v5_pre_topc(C_231,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_231,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_231,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_231)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_1824])).

tff(c_1855,plain,(
    ! [C_233] :
      ( v5_pre_topc(C_233,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_233,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_233,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69,c_1831])).

tff(c_1858,plain,
    ( v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1510,c_1855])).

tff(c_1868,plain,(
    v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_1500,c_1643,c_1858])).

tff(c_2037,plain,(
    ! [C_244,A_245,B_246] :
      ( v3_tops_2(C_244,A_245,B_246)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_245),u1_struct_0(B_246),C_244),B_246,A_245)
      | ~ v5_pre_topc(C_244,A_245,B_246)
      | ~ v2_funct_1(C_244)
      | k2_relset_1(u1_struct_0(A_245),u1_struct_0(B_246),C_244) != k2_struct_0(B_246)
      | k1_relset_1(u1_struct_0(A_245),u1_struct_0(B_246),C_244) != k2_struct_0(A_245)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_245),u1_struct_0(B_246))))
      | ~ v1_funct_2(C_244,u1_struct_0(A_245),u1_struct_0(B_246))
      | ~ v1_funct_1(C_244)
      | ~ l1_pre_topc(B_246)
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2041,plain,(
    ! [C_244,A_245] :
      ( v3_tops_2(C_244,A_245,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_245),k2_struct_0('#skF_1'),C_244),'#skF_1',A_245)
      | ~ v5_pre_topc(C_244,A_245,'#skF_1')
      | ~ v2_funct_1(C_244)
      | k2_relset_1(u1_struct_0(A_245),u1_struct_0('#skF_1'),C_244) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_245),u1_struct_0('#skF_1'),C_244) != k2_struct_0(A_245)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_245),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_244,u1_struct_0(A_245),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_244)
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_2037])).

tff(c_3162,plain,(
    ! [C_339,A_340] :
      ( v3_tops_2(C_339,A_340,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_340),k2_struct_0('#skF_1'),C_339),'#skF_1',A_340)
      | ~ v5_pre_topc(C_339,A_340,'#skF_1')
      | ~ v2_funct_1(C_339)
      | k2_relset_1(u1_struct_0(A_340),k2_struct_0('#skF_1'),C_339) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_340),k2_struct_0('#skF_1'),C_339) != k2_struct_0(A_340)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_340),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_339,u1_struct_0(A_340),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_339)
      | ~ l1_pre_topc(A_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69,c_69,c_69,c_69,c_2041])).

tff(c_3166,plain,(
    ! [C_339] :
      ( v3_tops_2(C_339,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_339),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_339,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_339)
      | k2_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_339) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_339) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_339,u1_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_339)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_3162])).

tff(c_3177,plain,(
    ! [C_342] :
      ( v3_tops_2(C_342,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_342),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_342,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_342)
      | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_342) != k2_struct_0('#skF_1')
      | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_342) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_342,k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_342) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68,c_68,c_68,c_68,c_3166])).

tff(c_3180,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_597,c_3177])).

tff(c_3187,plain,(
    v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_587,c_2644,c_1469,c_1499,c_2469,c_1868,c_1498,c_3180])).

tff(c_3189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_3187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.02/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.15  
% 6.02/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.15  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.02/2.15  
% 6.02/2.15  %Foreground sorts:
% 6.02/2.15  
% 6.02/2.15  
% 6.02/2.15  %Background operators:
% 6.02/2.15  
% 6.02/2.15  
% 6.02/2.15  %Foreground operators:
% 6.02/2.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.02/2.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.02/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.02/2.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.02/2.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.02/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.02/2.15  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 6.02/2.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.02/2.15  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.02/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.02/2.15  tff('#skF_2', type, '#skF_2': $i).
% 6.02/2.15  tff('#skF_3', type, '#skF_3': $i).
% 6.02/2.15  tff('#skF_1', type, '#skF_1': $i).
% 6.02/2.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.02/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.02/2.15  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.02/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.02/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.02/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.02/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.02/2.15  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 6.02/2.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.02/2.15  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.02/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.02/2.15  
% 6.02/2.18  tff(f_148, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 6.02/2.18  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.02/2.18  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.02/2.18  tff(f_69, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 6.02/2.18  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 6.02/2.18  tff(f_105, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 6.02/2.18  tff(f_128, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 6.02/2.18  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.02/2.18  tff(f_37, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 6.02/2.18  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 6.02/2.18  tff(c_48, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.02/2.18  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.02/2.18  tff(c_14, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.02/2.18  tff(c_56, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.02/2.18  tff(c_61, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_14, c_56])).
% 6.02/2.18  tff(c_69, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_61])).
% 6.02/2.18  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.02/2.18  tff(c_68, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_61])).
% 6.02/2.18  tff(c_46, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.02/2.18  tff(c_71, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46])).
% 6.02/2.18  tff(c_80, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_71])).
% 6.02/2.18  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.02/2.18  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_44])).
% 6.02/2.18  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_70])).
% 6.02/2.18  tff(c_153, plain, (![A_54, B_55, C_56]: (k2_tops_2(A_54, B_55, C_56)=k2_funct_1(C_56) | ~v2_funct_1(C_56) | k2_relset_1(A_54, B_55, C_56)!=B_55 | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))) | ~v1_funct_2(C_56, A_54, B_55) | ~v1_funct_1(C_56))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.02/2.18  tff(c_159, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_153])).
% 6.02/2.18  tff(c_163, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_159])).
% 6.02/2.18  tff(c_164, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_163])).
% 6.02/2.18  tff(c_42, plain, (v3_tops_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.02/2.18  tff(c_345, plain, (![A_79, B_80, C_81]: (k2_relset_1(u1_struct_0(A_79), u1_struct_0(B_80), C_81)=k2_struct_0(B_80) | ~v3_tops_2(C_81, A_79, B_80) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_79), u1_struct_0(B_80)))) | ~v1_funct_2(C_81, u1_struct_0(A_79), u1_struct_0(B_80)) | ~v1_funct_1(C_81) | ~l1_pre_topc(B_80) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.02/2.18  tff(c_352, plain, (![B_80, C_81]: (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_80), C_81)=k2_struct_0(B_80) | ~v3_tops_2(C_81, '#skF_1', B_80) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_80)))) | ~v1_funct_2(C_81, u1_struct_0('#skF_1'), u1_struct_0(B_80)) | ~v1_funct_1(C_81) | ~l1_pre_topc(B_80) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_345])).
% 6.02/2.18  tff(c_431, plain, (![B_90, C_91]: (k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_90), C_91)=k2_struct_0(B_90) | ~v3_tops_2(C_91, '#skF_1', B_90) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_90)))) | ~v1_funct_2(C_91, k2_struct_0('#skF_1'), u1_struct_0(B_90)) | ~v1_funct_1(C_91) | ~l1_pre_topc(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_69, c_69, c_352])).
% 6.02/2.18  tff(c_441, plain, (![C_91]: (k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_91)=k2_struct_0('#skF_2') | ~v3_tops_2(C_91, '#skF_1', '#skF_2') | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_91, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_91) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_431])).
% 6.02/2.18  tff(c_453, plain, (![C_93]: (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_93)=k2_struct_0('#skF_2') | ~v3_tops_2(C_93, '#skF_1', '#skF_2') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_93, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_93))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_68, c_441])).
% 6.02/2.18  tff(c_460, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_453])).
% 6.02/2.18  tff(c_464, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_42, c_460])).
% 6.02/2.18  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_464])).
% 6.02/2.18  tff(c_467, plain, (~v2_funct_1('#skF_3') | k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_163])).
% 6.02/2.18  tff(c_499, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_467])).
% 6.02/2.18  tff(c_469, plain, (![C_94, A_95, B_96]: (v2_funct_1(C_94) | ~v3_tops_2(C_94, A_95, B_96) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95), u1_struct_0(B_96)))) | ~v1_funct_2(C_94, u1_struct_0(A_95), u1_struct_0(B_96)) | ~v1_funct_1(C_94) | ~l1_pre_topc(B_96) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.02/2.18  tff(c_476, plain, (![C_94, B_96]: (v2_funct_1(C_94) | ~v3_tops_2(C_94, '#skF_1', B_96) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_96)))) | ~v1_funct_2(C_94, u1_struct_0('#skF_1'), u1_struct_0(B_96)) | ~v1_funct_1(C_94) | ~l1_pre_topc(B_96) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_469])).
% 6.02/2.18  tff(c_528, plain, (![C_101, B_102]: (v2_funct_1(C_101) | ~v3_tops_2(C_101, '#skF_1', B_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_102)))) | ~v1_funct_2(C_101, k2_struct_0('#skF_1'), u1_struct_0(B_102)) | ~v1_funct_1(C_101) | ~l1_pre_topc(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_69, c_476])).
% 6.02/2.18  tff(c_538, plain, (![C_101]: (v2_funct_1(C_101) | ~v3_tops_2(C_101, '#skF_1', '#skF_2') | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_101, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_101) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_528])).
% 6.02/2.18  tff(c_544, plain, (![C_103]: (v2_funct_1(C_103) | ~v3_tops_2(C_103, '#skF_1', '#skF_2') | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_103, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_103))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_538])).
% 6.02/2.18  tff(c_551, plain, (v2_funct_1('#skF_3') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_544])).
% 6.02/2.18  tff(c_555, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_42, c_551])).
% 6.02/2.18  tff(c_557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_555])).
% 6.02/2.18  tff(c_558, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_467])).
% 6.02/2.18  tff(c_40, plain, (~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.02/2.18  tff(c_88, plain, (~v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_68, c_40])).
% 6.02/2.18  tff(c_589, plain, (~v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_558, c_88])).
% 6.02/2.18  tff(c_117, plain, (![A_42, B_43, C_44]: (v1_funct_1(k2_tops_2(A_42, B_43, C_44)) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(C_44, A_42, B_43) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.02/2.18  tff(c_120, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_117])).
% 6.02/2.18  tff(c_123, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_120])).
% 6.02/2.18  tff(c_588, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_123])).
% 6.02/2.18  tff(c_124, plain, (![A_45, B_46, C_47]: (v1_funct_2(k2_tops_2(A_45, B_46, C_47), B_46, A_45) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(C_47, A_45, B_46) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.02/2.18  tff(c_126, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_124])).
% 6.02/2.18  tff(c_129, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_126])).
% 6.02/2.18  tff(c_587, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_129])).
% 6.02/2.18  tff(c_468, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_163])).
% 6.02/2.18  tff(c_559, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_467])).
% 6.02/2.18  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.02/2.18  tff(c_1763, plain, (![B_226, A_227, C_228]: (k1_relset_1(u1_struct_0(B_226), u1_struct_0(A_227), k2_tops_2(u1_struct_0(A_227), u1_struct_0(B_226), C_228))=k2_struct_0(B_226) | ~v2_funct_1(C_228) | k2_relset_1(u1_struct_0(A_227), u1_struct_0(B_226), C_228)!=k2_struct_0(B_226) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227), u1_struct_0(B_226)))) | ~v1_funct_2(C_228, u1_struct_0(A_227), u1_struct_0(B_226)) | ~v1_funct_1(C_228) | ~l1_struct_0(B_226) | v2_struct_0(B_226) | ~l1_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.18  tff(c_1793, plain, (![A_227, C_228]: (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_227), k2_tops_2(u1_struct_0(A_227), k2_struct_0('#skF_2'), C_228))=k2_struct_0('#skF_2') | ~v2_funct_1(C_228) | k2_relset_1(u1_struct_0(A_227), u1_struct_0('#skF_2'), C_228)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_228, u1_struct_0(A_227), u1_struct_0('#skF_2')) | ~v1_funct_1(C_228) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_227))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1763])).
% 6.02/2.18  tff(c_1804, plain, (![A_227, C_228]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_227), k2_tops_2(u1_struct_0(A_227), k2_struct_0('#skF_2'), C_228))=k2_struct_0('#skF_2') | ~v2_funct_1(C_228) | k2_relset_1(u1_struct_0(A_227), k2_struct_0('#skF_2'), C_228)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_228, u1_struct_0(A_227), k2_struct_0('#skF_2')) | ~v1_funct_1(C_228) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_227))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_68, c_68, c_1793])).
% 6.02/2.18  tff(c_1805, plain, (![A_227, C_228]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_227), k2_tops_2(u1_struct_0(A_227), k2_struct_0('#skF_2'), C_228))=k2_struct_0('#skF_2') | ~v2_funct_1(C_228) | k2_relset_1(u1_struct_0(A_227), k2_struct_0('#skF_2'), C_228)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_228, u1_struct_0(A_227), k2_struct_0('#skF_2')) | ~v1_funct_1(C_228) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_227))), inference(negUnitSimplification, [status(thm)], [c_52, c_1804])).
% 6.02/2.18  tff(c_1840, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1805])).
% 6.02/2.18  tff(c_1843, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_1840])).
% 6.02/2.18  tff(c_1847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1843])).
% 6.02/2.18  tff(c_1849, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1805])).
% 6.02/2.18  tff(c_1784, plain, (![A_227, C_228]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_227), k2_tops_2(u1_struct_0(A_227), u1_struct_0('#skF_2'), C_228))=k2_struct_0('#skF_2') | ~v2_funct_1(C_228) | k2_relset_1(u1_struct_0(A_227), u1_struct_0('#skF_2'), C_228)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_228, u1_struct_0(A_227), u1_struct_0('#skF_2')) | ~v1_funct_1(C_228) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_227))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1763])).
% 6.02/2.18  tff(c_1800, plain, (![A_227, C_228]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_227), k2_tops_2(u1_struct_0(A_227), k2_struct_0('#skF_2'), C_228))=k2_struct_0('#skF_2') | ~v2_funct_1(C_228) | k2_relset_1(u1_struct_0(A_227), k2_struct_0('#skF_2'), C_228)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_228, u1_struct_0(A_227), k2_struct_0('#skF_2')) | ~v1_funct_1(C_228) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_227))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_68, c_68, c_1784])).
% 6.02/2.18  tff(c_1801, plain, (![A_227, C_228]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_227), k2_tops_2(u1_struct_0(A_227), k2_struct_0('#skF_2'), C_228))=k2_struct_0('#skF_2') | ~v2_funct_1(C_228) | k2_relset_1(u1_struct_0(A_227), k2_struct_0('#skF_2'), C_228)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_227), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_228, u1_struct_0(A_227), k2_struct_0('#skF_2')) | ~v1_funct_1(C_228) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_227))), inference(negUnitSimplification, [status(thm)], [c_52, c_1800])).
% 6.02/2.18  tff(c_2223, plain, (![A_258, C_259]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_258), k2_tops_2(u1_struct_0(A_258), k2_struct_0('#skF_2'), C_259))=k2_struct_0('#skF_2') | ~v2_funct_1(C_259) | k2_relset_1(u1_struct_0(A_258), k2_struct_0('#skF_2'), C_259)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_258), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_259, u1_struct_0(A_258), k2_struct_0('#skF_2')) | ~v1_funct_1(C_259) | ~l1_struct_0(A_258))), inference(demodulation, [status(thm), theory('equality')], [c_1849, c_1801])).
% 6.02/2.18  tff(c_2235, plain, (![C_259]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_259))=k2_struct_0('#skF_2') | ~v2_funct_1(C_259) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_259)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_259, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_259) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_2223])).
% 6.02/2.18  tff(c_2245, plain, (![C_259]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_259))=k2_struct_0('#skF_2') | ~v2_funct_1(C_259) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_259)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_259, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_259) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_69, c_69, c_2235])).
% 6.02/2.18  tff(c_2611, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2245])).
% 6.02/2.18  tff(c_2614, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_2611])).
% 6.02/2.18  tff(c_2618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_2614])).
% 6.02/2.18  tff(c_2626, plain, (![C_302]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_302))=k2_struct_0('#skF_2') | ~v2_funct_1(C_302) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_302)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_302, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_302))), inference(splitRight, [status(thm)], [c_2245])).
% 6.02/2.18  tff(c_2638, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_558, c_2626])).
% 6.02/2.18  tff(c_2644, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_82, c_468, c_559, c_2638])).
% 6.02/2.18  tff(c_30, plain, (![A_18, B_19, C_20]: (m1_subset_1(k2_tops_2(A_18, B_19, C_20), k1_zfmisc_1(k2_zfmisc_1(B_19, A_18))) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.02/2.18  tff(c_593, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_558, c_30])).
% 6.02/2.18  tff(c_597, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_82, c_593])).
% 6.02/2.18  tff(c_16, plain, (![A_8, B_9, C_10]: (k2_tops_2(A_8, B_9, C_10)=k2_funct_1(C_10) | ~v2_funct_1(C_10) | k2_relset_1(A_8, B_9, C_10)!=B_9 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_2(C_10, A_8, B_9) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.02/2.18  tff(c_601, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_597, c_16])).
% 6.02/2.18  tff(c_615, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_588, c_587, c_601])).
% 6.02/2.18  tff(c_653, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_615])).
% 6.02/2.18  tff(c_991, plain, (![B_151, A_152, C_153]: (k2_relset_1(u1_struct_0(B_151), u1_struct_0(A_152), k2_tops_2(u1_struct_0(A_152), u1_struct_0(B_151), C_153))=k2_struct_0(A_152) | ~v2_funct_1(C_153) | k2_relset_1(u1_struct_0(A_152), u1_struct_0(B_151), C_153)!=k2_struct_0(B_151) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152), u1_struct_0(B_151)))) | ~v1_funct_2(C_153, u1_struct_0(A_152), u1_struct_0(B_151)) | ~v1_funct_1(C_153) | ~l1_struct_0(B_151) | v2_struct_0(B_151) | ~l1_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.18  tff(c_1012, plain, (![A_152, C_153]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_152), k2_tops_2(u1_struct_0(A_152), u1_struct_0('#skF_2'), C_153))=k2_struct_0(A_152) | ~v2_funct_1(C_153) | k2_relset_1(u1_struct_0(A_152), u1_struct_0('#skF_2'), C_153)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_153, u1_struct_0(A_152), u1_struct_0('#skF_2')) | ~v1_funct_1(C_153) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_152))), inference(superposition, [status(thm), theory('equality')], [c_68, c_991])).
% 6.02/2.18  tff(c_1028, plain, (![A_152, C_153]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_152), k2_tops_2(u1_struct_0(A_152), k2_struct_0('#skF_2'), C_153))=k2_struct_0(A_152) | ~v2_funct_1(C_153) | k2_relset_1(u1_struct_0(A_152), k2_struct_0('#skF_2'), C_153)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_153, u1_struct_0(A_152), k2_struct_0('#skF_2')) | ~v1_funct_1(C_153) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_152))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_68, c_68, c_1012])).
% 6.02/2.18  tff(c_1029, plain, (![A_152, C_153]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_152), k2_tops_2(u1_struct_0(A_152), k2_struct_0('#skF_2'), C_153))=k2_struct_0(A_152) | ~v2_funct_1(C_153) | k2_relset_1(u1_struct_0(A_152), k2_struct_0('#skF_2'), C_153)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_152), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_153, u1_struct_0(A_152), k2_struct_0('#skF_2')) | ~v1_funct_1(C_153) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_152))), inference(negUnitSimplification, [status(thm)], [c_52, c_1028])).
% 6.02/2.18  tff(c_1066, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1029])).
% 6.02/2.18  tff(c_1069, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_1066])).
% 6.02/2.18  tff(c_1073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1069])).
% 6.02/2.18  tff(c_1386, plain, (![A_197, C_198]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_197), k2_tops_2(u1_struct_0(A_197), k2_struct_0('#skF_2'), C_198))=k2_struct_0(A_197) | ~v2_funct_1(C_198) | k2_relset_1(u1_struct_0(A_197), k2_struct_0('#skF_2'), C_198)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_197), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_198, u1_struct_0(A_197), k2_struct_0('#skF_2')) | ~v1_funct_1(C_198) | ~l1_struct_0(A_197))), inference(splitRight, [status(thm)], [c_1029])).
% 6.02/2.18  tff(c_1398, plain, (![C_198]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_198))=k2_struct_0('#skF_1') | ~v2_funct_1(C_198) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_198)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_198, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_198) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_1386])).
% 6.02/2.18  tff(c_1408, plain, (![C_198]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_198))=k2_struct_0('#skF_1') | ~v2_funct_1(C_198) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_198)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_198, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_198) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_69, c_69, c_1398])).
% 6.02/2.18  tff(c_1424, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1408])).
% 6.02/2.18  tff(c_1427, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_1424])).
% 6.02/2.18  tff(c_1431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1427])).
% 6.02/2.18  tff(c_1452, plain, (![C_203]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_203))=k2_struct_0('#skF_1') | ~v2_funct_1(C_203) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_203)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_203, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_203))), inference(splitRight, [status(thm)], [c_1408])).
% 6.02/2.18  tff(c_1461, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_558, c_1452])).
% 6.02/2.18  tff(c_1465, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_82, c_468, c_559, c_1461])).
% 6.02/2.18  tff(c_1467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_653, c_1465])).
% 6.02/2.18  tff(c_1469, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_615])).
% 6.02/2.18  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.02/2.18  tff(c_86, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_10])).
% 6.02/2.18  tff(c_2, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.02/2.18  tff(c_1468, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_615])).
% 6.02/2.18  tff(c_1474, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1468])).
% 6.02/2.18  tff(c_1493, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_1474])).
% 6.02/2.18  tff(c_1497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_48, c_559, c_1493])).
% 6.02/2.18  tff(c_1499, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1468])).
% 6.02/2.18  tff(c_1644, plain, (![A_212, B_213, C_214]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_212), u1_struct_0(B_213), C_214), B_213, A_212) | ~v3_tops_2(C_214, A_212, B_213) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_212), u1_struct_0(B_213)))) | ~v1_funct_2(C_214, u1_struct_0(A_212), u1_struct_0(B_213)) | ~v1_funct_1(C_214) | ~l1_pre_topc(B_213) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.02/2.18  tff(c_1649, plain, (![B_213, C_214]: (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_213), C_214), B_213, '#skF_1') | ~v3_tops_2(C_214, '#skF_1', B_213) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_213)))) | ~v1_funct_2(C_214, u1_struct_0('#skF_1'), u1_struct_0(B_213)) | ~v1_funct_1(C_214) | ~l1_pre_topc(B_213) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_1644])).
% 6.02/2.18  tff(c_2417, plain, (![B_279, C_280]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_279), C_280), B_279, '#skF_1') | ~v3_tops_2(C_280, '#skF_1', B_279) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_279)))) | ~v1_funct_2(C_280, k2_struct_0('#skF_1'), u1_struct_0(B_279)) | ~v1_funct_1(C_280) | ~l1_pre_topc(B_279))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_69, c_69, c_1649])).
% 6.02/2.18  tff(c_2424, plain, (![C_280]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_280), '#skF_2', '#skF_1') | ~v3_tops_2(C_280, '#skF_1', '#skF_2') | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_280, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_280) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2417])).
% 6.02/2.18  tff(c_2452, plain, (![C_285]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_285), '#skF_2', '#skF_1') | ~v3_tops_2(C_285, '#skF_1', '#skF_2') | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_285, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_285))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_68, c_2424])).
% 6.02/2.18  tff(c_2462, plain, (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2452])).
% 6.02/2.18  tff(c_2469, plain, (v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_80, c_42, c_558, c_2462])).
% 6.02/2.18  tff(c_1498, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1468])).
% 6.02/2.18  tff(c_34, plain, (![A_18, B_19, C_20]: (v1_funct_1(k2_tops_2(A_18, B_19, C_20)) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.02/2.18  tff(c_609, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_597, c_34])).
% 6.02/2.18  tff(c_624, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_587, c_609])).
% 6.02/2.18  tff(c_1501, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1498, c_624])).
% 6.02/2.18  tff(c_32, plain, (![A_18, B_19, C_20]: (v1_funct_2(k2_tops_2(A_18, B_19, C_20), B_19, A_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.02/2.18  tff(c_606, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_597, c_32])).
% 6.02/2.18  tff(c_621, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_587, c_606])).
% 6.02/2.18  tff(c_1500, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1498, c_621])).
% 6.02/2.18  tff(c_8, plain, (![A_2]: (k2_funct_1(k2_funct_1(A_2))=A_2 | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.02/2.18  tff(c_1506, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1498, c_30])).
% 6.02/2.18  tff(c_1510, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_587, c_597, c_1506])).
% 6.02/2.18  tff(c_485, plain, (![C_94, A_95]: (v2_funct_1(C_94) | ~v3_tops_2(C_94, A_95, '#skF_2') | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_94, u1_struct_0(A_95), u1_struct_0('#skF_2')) | ~v1_funct_1(C_94) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_95))), inference(superposition, [status(thm), theory('equality')], [c_68, c_469])).
% 6.02/2.18  tff(c_1591, plain, (![C_209, A_210]: (v2_funct_1(C_209) | ~v3_tops_2(C_209, A_210, '#skF_2') | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_210), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_209, u1_struct_0(A_210), k2_struct_0('#skF_2')) | ~v1_funct_1(C_209) | ~l1_pre_topc(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_485])).
% 6.02/2.18  tff(c_1598, plain, (![C_209]: (v2_funct_1(C_209) | ~v3_tops_2(C_209, '#skF_1', '#skF_2') | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_209, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_209) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_1591])).
% 6.02/2.18  tff(c_1617, plain, (![C_211]: (v2_funct_1(C_211) | ~v3_tops_2(C_211, '#skF_1', '#skF_2') | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_211, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_211))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_69, c_1598])).
% 6.02/2.18  tff(c_1620, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1510, c_1617])).
% 6.02/2.18  tff(c_1630, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_1500, c_1620])).
% 6.02/2.18  tff(c_1635, plain, (~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_1630])).
% 6.02/2.18  tff(c_1638, plain, (~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_1635])).
% 6.02/2.18  tff(c_1641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_48, c_559, c_42, c_1638])).
% 6.02/2.18  tff(c_1643, plain, (v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1630])).
% 6.02/2.18  tff(c_560, plain, (![C_104, A_105, B_106]: (v5_pre_topc(C_104, A_105, B_106) | ~v3_tops_2(C_104, A_105, B_106) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105), u1_struct_0(B_106)))) | ~v1_funct_2(C_104, u1_struct_0(A_105), u1_struct_0(B_106)) | ~v1_funct_1(C_104) | ~l1_pre_topc(B_106) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.02/2.18  tff(c_576, plain, (![C_104, A_105]: (v5_pre_topc(C_104, A_105, '#skF_2') | ~v3_tops_2(C_104, A_105, '#skF_2') | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_105), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_104, u1_struct_0(A_105), u1_struct_0('#skF_2')) | ~v1_funct_1(C_104) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_105))), inference(superposition, [status(thm), theory('equality')], [c_68, c_560])).
% 6.02/2.18  tff(c_1824, plain, (![C_231, A_232]: (v5_pre_topc(C_231, A_232, '#skF_2') | ~v3_tops_2(C_231, A_232, '#skF_2') | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_232), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_231, u1_struct_0(A_232), k2_struct_0('#skF_2')) | ~v1_funct_1(C_231) | ~l1_pre_topc(A_232))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_576])).
% 6.02/2.18  tff(c_1831, plain, (![C_231]: (v5_pre_topc(C_231, '#skF_1', '#skF_2') | ~v3_tops_2(C_231, '#skF_1', '#skF_2') | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_231, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_231) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_69, c_1824])).
% 6.02/2.18  tff(c_1855, plain, (![C_233]: (v5_pre_topc(C_233, '#skF_1', '#skF_2') | ~v3_tops_2(C_233, '#skF_1', '#skF_2') | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_233, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_233))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_69, c_1831])).
% 6.02/2.18  tff(c_1858, plain, (v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1510, c_1855])).
% 6.02/2.18  tff(c_1868, plain, (v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_1500, c_1643, c_1858])).
% 6.02/2.18  tff(c_2037, plain, (![C_244, A_245, B_246]: (v3_tops_2(C_244, A_245, B_246) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_245), u1_struct_0(B_246), C_244), B_246, A_245) | ~v5_pre_topc(C_244, A_245, B_246) | ~v2_funct_1(C_244) | k2_relset_1(u1_struct_0(A_245), u1_struct_0(B_246), C_244)!=k2_struct_0(B_246) | k1_relset_1(u1_struct_0(A_245), u1_struct_0(B_246), C_244)!=k2_struct_0(A_245) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_245), u1_struct_0(B_246)))) | ~v1_funct_2(C_244, u1_struct_0(A_245), u1_struct_0(B_246)) | ~v1_funct_1(C_244) | ~l1_pre_topc(B_246) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.02/2.18  tff(c_2041, plain, (![C_244, A_245]: (v3_tops_2(C_244, A_245, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_245), k2_struct_0('#skF_1'), C_244), '#skF_1', A_245) | ~v5_pre_topc(C_244, A_245, '#skF_1') | ~v2_funct_1(C_244) | k2_relset_1(u1_struct_0(A_245), u1_struct_0('#skF_1'), C_244)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_245), u1_struct_0('#skF_1'), C_244)!=k2_struct_0(A_245) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_245), u1_struct_0('#skF_1')))) | ~v1_funct_2(C_244, u1_struct_0(A_245), u1_struct_0('#skF_1')) | ~v1_funct_1(C_244) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_245))), inference(superposition, [status(thm), theory('equality')], [c_69, c_2037])).
% 6.02/2.18  tff(c_3162, plain, (![C_339, A_340]: (v3_tops_2(C_339, A_340, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_340), k2_struct_0('#skF_1'), C_339), '#skF_1', A_340) | ~v5_pre_topc(C_339, A_340, '#skF_1') | ~v2_funct_1(C_339) | k2_relset_1(u1_struct_0(A_340), k2_struct_0('#skF_1'), C_339)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_340), k2_struct_0('#skF_1'), C_339)!=k2_struct_0(A_340) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_340), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_339, u1_struct_0(A_340), k2_struct_0('#skF_1')) | ~v1_funct_1(C_339) | ~l1_pre_topc(A_340))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_69, c_69, c_69, c_69, c_2041])).
% 6.02/2.18  tff(c_3166, plain, (![C_339]: (v3_tops_2(C_339, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_339), '#skF_1', '#skF_2') | ~v5_pre_topc(C_339, '#skF_2', '#skF_1') | ~v2_funct_1(C_339) | k2_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_339)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_339)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_339, u1_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_339) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_3162])).
% 6.02/2.18  tff(c_3177, plain, (![C_342]: (v3_tops_2(C_342, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_342), '#skF_1', '#skF_2') | ~v5_pre_topc(C_342, '#skF_2', '#skF_1') | ~v2_funct_1(C_342) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_342)!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_342)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_342, k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_342))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68, c_68, c_68, c_68, c_3166])).
% 6.02/2.18  tff(c_3180, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_597, c_3177])).
% 6.02/2.18  tff(c_3187, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_588, c_587, c_2644, c_1469, c_1499, c_2469, c_1868, c_1498, c_3180])).
% 6.02/2.18  tff(c_3189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_589, c_3187])).
% 6.02/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.18  
% 6.02/2.18  Inference rules
% 6.02/2.18  ----------------------
% 6.02/2.18  #Ref     : 0
% 6.02/2.18  #Sup     : 606
% 6.02/2.18  #Fact    : 0
% 6.02/2.18  #Define  : 0
% 6.02/2.18  #Split   : 11
% 6.02/2.18  #Chain   : 0
% 6.02/2.18  #Close   : 0
% 6.02/2.18  
% 6.02/2.18  Ordering : KBO
% 6.02/2.18  
% 6.02/2.18  Simplification rules
% 6.02/2.18  ----------------------
% 6.02/2.18  #Subsume      : 107
% 6.02/2.18  #Demod        : 1693
% 6.02/2.18  #Tautology    : 148
% 6.02/2.18  #SimpNegUnit  : 21
% 6.02/2.18  #BackRed      : 15
% 6.02/2.18  
% 6.02/2.18  #Partial instantiations: 0
% 6.02/2.18  #Strategies tried      : 1
% 6.02/2.18  
% 6.02/2.18  Timing (in seconds)
% 6.02/2.18  ----------------------
% 6.02/2.19  Preprocessing        : 0.34
% 6.02/2.19  Parsing              : 0.18
% 6.02/2.19  CNF conversion       : 0.03
% 6.02/2.19  Main loop            : 1.05
% 6.02/2.19  Inferencing          : 0.35
% 6.02/2.19  Reduction            : 0.42
% 6.02/2.19  Demodulation         : 0.32
% 6.02/2.19  BG Simplification    : 0.05
% 6.02/2.19  Subsumption          : 0.17
% 6.02/2.19  Abstraction          : 0.05
% 6.02/2.19  MUC search           : 0.00
% 6.02/2.19  Cooper               : 0.00
% 6.02/2.19  Total                : 1.45
% 6.02/2.19  Index Insertion      : 0.00
% 6.02/2.19  Index Deletion       : 0.00
% 6.02/2.19  Index Matching       : 0.00
% 6.02/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
