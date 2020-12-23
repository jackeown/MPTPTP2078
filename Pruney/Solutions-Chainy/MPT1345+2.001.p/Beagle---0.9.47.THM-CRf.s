%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:48 EST 2020

% Result     : Theorem 13.25s
% Output     : CNFRefutation 13.25s
% Verified   : 
% Statistics : Number of formulae       :  218 (23357 expanded)
%              Number of leaves         :   40 (8162 expanded)
%              Depth                    :   21
%              Number of atoms          :  759 (66553 expanded)
%              Number of equality atoms :  150 (10867 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
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

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
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

tff(f_135,axiom,(
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

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_158,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_40,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_78,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_83,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_91,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_83])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_90,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_83])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_92,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_64])).

tff(c_130,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_92])).

tff(c_24,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_137,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_24])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_93,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_66])).

tff(c_102,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_93])).

tff(c_312,plain,(
    ! [C_109,A_110,B_111] :
      ( v1_funct_1(k2_funct_1(C_109))
      | k2_relset_1(A_110,B_111,C_109) != B_111
      | ~ v2_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_2(C_109,A_110,B_111)
      | ~ v1_funct_1(C_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_315,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_312])).

tff(c_322,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102,c_315])).

tff(c_392,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_62,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_496,plain,(
    ! [C_167,A_168,B_169] :
      ( v2_funct_1(C_167)
      | ~ v3_tops_2(C_167,A_168,B_169)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168),u1_struct_0(B_169))))
      | ~ v1_funct_2(C_167,u1_struct_0(A_168),u1_struct_0(B_169))
      | ~ v1_funct_1(C_167)
      | ~ l1_pre_topc(B_169)
      | ~ l1_pre_topc(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_503,plain,(
    ! [C_167,B_169] :
      ( v2_funct_1(C_167)
      | ~ v3_tops_2(C_167,'#skF_1',B_169)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_169))))
      | ~ v1_funct_2(C_167,u1_struct_0('#skF_1'),u1_struct_0(B_169))
      | ~ v1_funct_1(C_167)
      | ~ l1_pre_topc(B_169)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_496])).

tff(c_793,plain,(
    ! [C_242,B_243] :
      ( v2_funct_1(C_242)
      | ~ v3_tops_2(C_242,'#skF_1',B_243)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_243))))
      | ~ v1_funct_2(C_242,k2_struct_0('#skF_1'),u1_struct_0(B_243))
      | ~ v1_funct_1(C_242)
      | ~ l1_pre_topc(B_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_91,c_503])).

tff(c_807,plain,(
    ! [C_242] :
      ( v2_funct_1(C_242)
      | ~ v3_tops_2(C_242,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_242,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_242)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_793])).

tff(c_814,plain,(
    ! [C_244] :
      ( v2_funct_1(C_244)
      | ~ v3_tops_2(C_244,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_244,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_90,c_807])).

tff(c_821,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_814])).

tff(c_829,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102,c_62,c_821])).

tff(c_831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_392,c_829])).

tff(c_833,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_3958,plain,(
    ! [C_694,A_695,B_696] :
      ( v5_pre_topc(C_694,A_695,B_696)
      | ~ v3_tops_2(C_694,A_695,B_696)
      | ~ m1_subset_1(C_694,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_695),u1_struct_0(B_696))))
      | ~ v1_funct_2(C_694,u1_struct_0(A_695),u1_struct_0(B_696))
      | ~ v1_funct_1(C_694)
      | ~ l1_pre_topc(B_696)
      | ~ l1_pre_topc(A_695) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3978,plain,(
    ! [C_694,A_695] :
      ( v5_pre_topc(C_694,A_695,'#skF_2')
      | ~ v3_tops_2(C_694,A_695,'#skF_2')
      | ~ m1_subset_1(C_694,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_695),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_694,u1_struct_0(A_695),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_694)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_695) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_3958])).

tff(c_4908,plain,(
    ! [C_822,A_823] :
      ( v5_pre_topc(C_822,A_823,'#skF_2')
      | ~ v3_tops_2(C_822,A_823,'#skF_2')
      | ~ m1_subset_1(C_822,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_823),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_822,u1_struct_0(A_823),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_822)
      | ~ l1_pre_topc(A_823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_90,c_3978])).

tff(c_4919,plain,(
    ! [C_822] :
      ( v5_pre_topc(C_822,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_822,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_822,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_822,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_822)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_4908])).

tff(c_4929,plain,(
    ! [C_824] :
      ( v5_pre_topc(C_824,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_824,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_824,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_824,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_824) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_91,c_4919])).

tff(c_4936,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_4929])).

tff(c_4944,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102,c_62,c_4936])).

tff(c_22,plain,(
    ! [A_8] :
      ( k2_funct_1(k2_funct_1(A_8)) = A_8
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_281,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_289,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_281])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_130,c_8])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4088,plain,(
    ! [A_714,B_715,C_716] :
      ( k1_relset_1(u1_struct_0(A_714),u1_struct_0(B_715),C_716) = k2_struct_0(A_714)
      | ~ v3_tops_2(C_716,A_714,B_715)
      | ~ m1_subset_1(C_716,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_714),u1_struct_0(B_715))))
      | ~ v1_funct_2(C_716,u1_struct_0(A_714),u1_struct_0(B_715))
      | ~ v1_funct_1(C_716)
      | ~ l1_pre_topc(B_715)
      | ~ l1_pre_topc(A_714) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5149,plain,(
    ! [A_861,B_862,A_863] :
      ( k1_relset_1(u1_struct_0(A_861),u1_struct_0(B_862),A_863) = k2_struct_0(A_861)
      | ~ v3_tops_2(A_863,A_861,B_862)
      | ~ v1_funct_2(A_863,u1_struct_0(A_861),u1_struct_0(B_862))
      | ~ v1_funct_1(A_863)
      | ~ l1_pre_topc(B_862)
      | ~ l1_pre_topc(A_861)
      | ~ r1_tarski(A_863,k2_zfmisc_1(u1_struct_0(A_861),u1_struct_0(B_862))) ) ),
    inference(resolution,[status(thm)],[c_10,c_4088])).

tff(c_5160,plain,(
    ! [B_862,A_863] :
      ( k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_862),A_863) = k2_struct_0('#skF_1')
      | ~ v3_tops_2(A_863,'#skF_1',B_862)
      | ~ v1_funct_2(A_863,u1_struct_0('#skF_1'),u1_struct_0(B_862))
      | ~ v1_funct_1(A_863)
      | ~ l1_pre_topc(B_862)
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_863,k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_862))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_5149])).

tff(c_5581,plain,(
    ! [B_931,A_932] :
      ( k1_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_931),A_932) = k2_struct_0('#skF_1')
      | ~ v3_tops_2(A_932,'#skF_1',B_931)
      | ~ v1_funct_2(A_932,k2_struct_0('#skF_1'),u1_struct_0(B_931))
      | ~ v1_funct_1(A_932)
      | ~ l1_pre_topc(B_931)
      | ~ r1_tarski(A_932,k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_931))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_91,c_91,c_5160])).

tff(c_5595,plain,(
    ! [A_932] :
      ( k1_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),A_932) = k2_struct_0('#skF_1')
      | ~ v3_tops_2(A_932,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_932,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_932)
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_932,k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_5581])).

tff(c_5608,plain,(
    ! [A_933] :
      ( k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_933) = k2_struct_0('#skF_1')
      | ~ v3_tops_2(A_933,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_933,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_933)
      | ~ r1_tarski(A_933,k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_90,c_90,c_5595])).

tff(c_5619,plain,
    ( k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_5608])).

tff(c_5628,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102,c_62,c_289,c_5619])).

tff(c_5700,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_102])).

tff(c_5699,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_130])).

tff(c_1416,plain,(
    ! [A_376,B_377,C_378] :
      ( k1_relset_1(u1_struct_0(A_376),u1_struct_0(B_377),C_378) = k2_struct_0(A_376)
      | ~ v3_tops_2(C_378,A_376,B_377)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_376),u1_struct_0(B_377))))
      | ~ v1_funct_2(C_378,u1_struct_0(A_376),u1_struct_0(B_377))
      | ~ v1_funct_1(C_378)
      | ~ l1_pre_topc(B_377)
      | ~ l1_pre_topc(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2354,plain,(
    ! [A_534,B_535,A_536] :
      ( k1_relset_1(u1_struct_0(A_534),u1_struct_0(B_535),A_536) = k2_struct_0(A_534)
      | ~ v3_tops_2(A_536,A_534,B_535)
      | ~ v1_funct_2(A_536,u1_struct_0(A_534),u1_struct_0(B_535))
      | ~ v1_funct_1(A_536)
      | ~ l1_pre_topc(B_535)
      | ~ l1_pre_topc(A_534)
      | ~ r1_tarski(A_536,k2_zfmisc_1(u1_struct_0(A_534),u1_struct_0(B_535))) ) ),
    inference(resolution,[status(thm)],[c_10,c_1416])).

tff(c_2365,plain,(
    ! [B_535,A_536] :
      ( k1_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_535),A_536) = k2_struct_0('#skF_1')
      | ~ v3_tops_2(A_536,'#skF_1',B_535)
      | ~ v1_funct_2(A_536,u1_struct_0('#skF_1'),u1_struct_0(B_535))
      | ~ v1_funct_1(A_536)
      | ~ l1_pre_topc(B_535)
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_536,k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_535))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2354])).

tff(c_2391,plain,(
    ! [B_537,A_538] :
      ( k1_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_537),A_538) = k2_struct_0('#skF_1')
      | ~ v3_tops_2(A_538,'#skF_1',B_537)
      | ~ v1_funct_2(A_538,k2_struct_0('#skF_1'),u1_struct_0(B_537))
      | ~ v1_funct_1(A_538)
      | ~ l1_pre_topc(B_537)
      | ~ r1_tarski(A_538,k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_537))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_91,c_91,c_2365])).

tff(c_2405,plain,(
    ! [A_538] :
      ( k1_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),A_538) = k2_struct_0('#skF_1')
      | ~ v3_tops_2(A_538,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_538,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_538)
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_538,k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_2391])).

tff(c_2435,plain,(
    ! [A_540] :
      ( k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_540) = k2_struct_0('#skF_1')
      | ~ v3_tops_2(A_540,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_540,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_540)
      | ~ r1_tarski(A_540,k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_90,c_90,c_2405])).

tff(c_2446,plain,
    ( k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_2435])).

tff(c_2455,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102,c_62,c_289,c_2446])).

tff(c_832,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_834,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_832])).

tff(c_2513,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_834])).

tff(c_2520,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_102])).

tff(c_2517,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_138])).

tff(c_2521,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_91])).

tff(c_1699,plain,(
    ! [A_412,B_413,C_414] :
      ( k2_relset_1(u1_struct_0(A_412),u1_struct_0(B_413),C_414) = k2_struct_0(B_413)
      | ~ v3_tops_2(C_414,A_412,B_413)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412),u1_struct_0(B_413))))
      | ~ v1_funct_2(C_414,u1_struct_0(A_412),u1_struct_0(B_413))
      | ~ v1_funct_1(C_414)
      | ~ l1_pre_topc(B_413)
      | ~ l1_pre_topc(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2771,plain,(
    ! [A_543,B_544,A_545] :
      ( k2_relset_1(u1_struct_0(A_543),u1_struct_0(B_544),A_545) = k2_struct_0(B_544)
      | ~ v3_tops_2(A_545,A_543,B_544)
      | ~ v1_funct_2(A_545,u1_struct_0(A_543),u1_struct_0(B_544))
      | ~ v1_funct_1(A_545)
      | ~ l1_pre_topc(B_544)
      | ~ l1_pre_topc(A_543)
      | ~ r1_tarski(A_545,k2_zfmisc_1(u1_struct_0(A_543),u1_struct_0(B_544))) ) ),
    inference(resolution,[status(thm)],[c_10,c_1699])).

tff(c_2791,plain,(
    ! [A_543,A_545] :
      ( k2_relset_1(u1_struct_0(A_543),u1_struct_0('#skF_2'),A_545) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(A_545,A_543,'#skF_2')
      | ~ v1_funct_2(A_545,u1_struct_0(A_543),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_545)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_543)
      | ~ r1_tarski(A_545,k2_zfmisc_1(u1_struct_0(A_543),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_2771])).

tff(c_2915,plain,(
    ! [A_552,A_553] :
      ( k2_relset_1(u1_struct_0(A_552),k2_struct_0('#skF_2'),A_553) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(A_553,A_552,'#skF_2')
      | ~ v1_funct_2(A_553,u1_struct_0(A_552),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_553)
      | ~ l1_pre_topc(A_552)
      | ~ r1_tarski(A_553,k2_zfmisc_1(u1_struct_0(A_552),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_90,c_90,c_2791])).

tff(c_2918,plain,(
    ! [A_553] :
      ( k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_553) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(A_553,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_553,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_553)
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_553,k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2521,c_2915])).

tff(c_3637,plain,(
    ! [A_615] :
      ( k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),A_615) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(A_615,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_615,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_615)
      | ~ r1_tarski(A_615,k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2521,c_2521,c_2918])).

tff(c_3640,plain,
    ( k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2517,c_3637])).

tff(c_3655,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2520,c_62,c_3640])).

tff(c_3657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2513,c_3655])).

tff(c_3659,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_832])).

tff(c_5693,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_3659])).

tff(c_3694,plain,(
    ! [C_624,B_625,A_626] :
      ( m1_subset_1(k2_funct_1(C_624),k1_zfmisc_1(k2_zfmisc_1(B_625,A_626)))
      | k2_relset_1(A_626,B_625,C_624) != B_625
      | ~ v2_funct_1(C_624)
      | ~ m1_subset_1(C_624,k1_zfmisc_1(k2_zfmisc_1(A_626,B_625)))
      | ~ v1_funct_2(C_624,A_626,B_625)
      | ~ v1_funct_1(C_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3729,plain,(
    ! [C_624,B_625,A_626] :
      ( r1_tarski(k2_funct_1(C_624),k2_zfmisc_1(B_625,A_626))
      | k2_relset_1(A_626,B_625,C_624) != B_625
      | ~ v2_funct_1(C_624)
      | ~ m1_subset_1(C_624,k1_zfmisc_1(k2_zfmisc_1(A_626,B_625)))
      | ~ v1_funct_2(C_624,A_626,B_625)
      | ~ v1_funct_1(C_624) ) ),
    inference(resolution,[status(thm)],[c_3694,c_8])).

tff(c_3676,plain,(
    ! [A_616,B_617,C_618] :
      ( k2_tops_2(A_616,B_617,C_618) = k2_funct_1(C_618)
      | ~ v2_funct_1(C_618)
      | k2_relset_1(A_616,B_617,C_618) != B_617
      | ~ m1_subset_1(C_618,k1_zfmisc_1(k2_zfmisc_1(A_616,B_617)))
      | ~ v1_funct_2(C_618,A_616,B_617)
      | ~ v1_funct_1(C_618) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3679,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_3676])).

tff(c_3686,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102,c_3659,c_833,c_3679])).

tff(c_60,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_122,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_90,c_60])).

tff(c_3688,plain,(
    ~ v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3686,c_122])).

tff(c_3658,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_832])).

tff(c_368,plain,(
    ! [C_128,B_129,A_130] :
      ( v1_funct_2(k2_funct_1(C_128),B_129,A_130)
      | k2_relset_1(A_130,B_129,C_128) != B_129
      | ~ v2_funct_1(C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_130,B_129)))
      | ~ v1_funct_2(C_128,A_130,B_129)
      | ~ v1_funct_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_371,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_368])).

tff(c_378,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102,c_371])).

tff(c_3661,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_378])).

tff(c_3662,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3661])).

tff(c_3668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3659,c_3662])).

tff(c_3669,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3661])).

tff(c_5694,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_3669])).

tff(c_30,plain,(
    ! [A_15,B_16,C_17] :
      ( k1_relset_1(A_15,B_16,C_17) = k1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5129,plain,(
    ! [B_858,A_859,C_860] :
      ( k1_relset_1(B_858,A_859,k2_funct_1(C_860)) = k1_relat_1(k2_funct_1(C_860))
      | k2_relset_1(A_859,B_858,C_860) != B_858
      | ~ v2_funct_1(C_860)
      | ~ m1_subset_1(C_860,k1_zfmisc_1(k2_zfmisc_1(A_859,B_858)))
      | ~ v1_funct_2(C_860,A_859,B_858)
      | ~ v1_funct_1(C_860) ) ),
    inference(resolution,[status(thm)],[c_3694,c_30])).

tff(c_5135,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_5129])).

tff(c_5143,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102,c_833,c_3659,c_5135])).

tff(c_5670,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_5143])).

tff(c_5692,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_3686])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_4547,plain,(
    ! [B_789,A_790,C_791] :
      ( k2_relset_1(u1_struct_0(B_789),u1_struct_0(A_790),k2_tops_2(u1_struct_0(A_790),u1_struct_0(B_789),C_791)) = k2_struct_0(A_790)
      | ~ v2_funct_1(C_791)
      | k2_relset_1(u1_struct_0(A_790),u1_struct_0(B_789),C_791) != k2_struct_0(B_789)
      | ~ m1_subset_1(C_791,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790),u1_struct_0(B_789))))
      | ~ v1_funct_2(C_791,u1_struct_0(A_790),u1_struct_0(B_789))
      | ~ v1_funct_1(C_791)
      | ~ l1_struct_0(B_789)
      | v2_struct_0(B_789)
      | ~ l1_struct_0(A_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_4568,plain,(
    ! [A_790,C_791] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_790),k2_tops_2(u1_struct_0(A_790),u1_struct_0('#skF_2'),C_791)) = k2_struct_0(A_790)
      | ~ v2_funct_1(C_791)
      | k2_relset_1(u1_struct_0(A_790),u1_struct_0('#skF_2'),C_791) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_791,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_791,u1_struct_0(A_790),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_791)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_790) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_4547])).

tff(c_4584,plain,(
    ! [A_790,C_791] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_790),k2_tops_2(u1_struct_0(A_790),k2_struct_0('#skF_2'),C_791)) = k2_struct_0(A_790)
      | ~ v2_funct_1(C_791)
      | k2_relset_1(u1_struct_0(A_790),k2_struct_0('#skF_2'),C_791) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_791,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_791,u1_struct_0(A_790),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_791)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_790) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_90,c_90,c_4568])).

tff(c_4585,plain,(
    ! [A_790,C_791] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_790),k2_tops_2(u1_struct_0(A_790),k2_struct_0('#skF_2'),C_791)) = k2_struct_0(A_790)
      | ~ v2_funct_1(C_791)
      | k2_relset_1(u1_struct_0(A_790),k2_struct_0('#skF_2'),C_791) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_791,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_791,u1_struct_0(A_790),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_791)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_790) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4584])).

tff(c_4743,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4585])).

tff(c_4746,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_4743])).

tff(c_4750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4746])).

tff(c_4752,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4585])).

tff(c_4577,plain,(
    ! [A_790,C_791] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_790),k2_tops_2(u1_struct_0(A_790),k2_struct_0('#skF_2'),C_791)) = k2_struct_0(A_790)
      | ~ v2_funct_1(C_791)
      | k2_relset_1(u1_struct_0(A_790),u1_struct_0('#skF_2'),C_791) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_791,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_791,u1_struct_0(A_790),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_791)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_790) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_4547])).

tff(c_4588,plain,(
    ! [A_790,C_791] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_790),k2_tops_2(u1_struct_0(A_790),k2_struct_0('#skF_2'),C_791)) = k2_struct_0(A_790)
      | ~ v2_funct_1(C_791)
      | k2_relset_1(u1_struct_0(A_790),k2_struct_0('#skF_2'),C_791) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_791,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_791,u1_struct_0(A_790),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_791)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_790) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_90,c_90,c_4577])).

tff(c_4589,plain,(
    ! [A_790,C_791] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_790),k2_tops_2(u1_struct_0(A_790),k2_struct_0('#skF_2'),C_791)) = k2_struct_0(A_790)
      | ~ v2_funct_1(C_791)
      | k2_relset_1(u1_struct_0(A_790),k2_struct_0('#skF_2'),C_791) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_791,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_791,u1_struct_0(A_790),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_791)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_790) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4588])).

tff(c_5210,plain,(
    ! [A_869,C_870] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_869),k2_tops_2(u1_struct_0(A_869),k2_struct_0('#skF_2'),C_870)) = k2_struct_0(A_869)
      | ~ v2_funct_1(C_870)
      | k2_relset_1(u1_struct_0(A_869),k2_struct_0('#skF_2'),C_870) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_870,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_869),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_870,u1_struct_0(A_869),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_870)
      | ~ l1_struct_0(A_869) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4752,c_4589])).

tff(c_5222,plain,(
    ! [C_870] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_870)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_870)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_870) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_870,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_870,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_870)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_5210])).

tff(c_5232,plain,(
    ! [C_870] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_870)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_870)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_870) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_870,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_870,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_870)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_91,c_91,c_5222])).

tff(c_12650,plain,(
    ! [C_870] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),C_870)) = k1_relat_1('#skF_3')
      | ~ v2_funct_1(C_870)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),C_870) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_870,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_870,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_870)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_5628,c_5628,c_5628,c_5628,c_5628,c_5232])).

tff(c_12651,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12650])).

tff(c_12654,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_12651])).

tff(c_12658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12654])).

tff(c_12660,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_12650])).

tff(c_4781,plain,(
    ! [B_813,A_814,C_815] :
      ( k1_relset_1(u1_struct_0(B_813),u1_struct_0(A_814),k2_tops_2(u1_struct_0(A_814),u1_struct_0(B_813),C_815)) = k2_struct_0(B_813)
      | ~ v2_funct_1(C_815)
      | k2_relset_1(u1_struct_0(A_814),u1_struct_0(B_813),C_815) != k2_struct_0(B_813)
      | ~ m1_subset_1(C_815,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_814),u1_struct_0(B_813))))
      | ~ v1_funct_2(C_815,u1_struct_0(A_814),u1_struct_0(B_813))
      | ~ v1_funct_1(C_815)
      | ~ l1_struct_0(B_813)
      | v2_struct_0(B_813)
      | ~ l1_struct_0(A_814) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_4811,plain,(
    ! [A_814,C_815] :
      ( k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_814),k2_tops_2(u1_struct_0(A_814),k2_struct_0('#skF_2'),C_815)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_815)
      | k2_relset_1(u1_struct_0(A_814),u1_struct_0('#skF_2'),C_815) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_815,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_814),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_815,u1_struct_0(A_814),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_815)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_814) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_4781])).

tff(c_4826,plain,(
    ! [A_814,C_815] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_814),k2_tops_2(u1_struct_0(A_814),k2_struct_0('#skF_2'),C_815)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_815)
      | k2_relset_1(u1_struct_0(A_814),k2_struct_0('#skF_2'),C_815) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_815,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_814),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_815,u1_struct_0(A_814),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_815)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_814) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4752,c_90,c_90,c_90,c_90,c_4811])).

tff(c_4881,plain,(
    ! [A_820,C_821] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_820),k2_tops_2(u1_struct_0(A_820),k2_struct_0('#skF_2'),C_821)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_821)
      | k2_relset_1(u1_struct_0(A_820),k2_struct_0('#skF_2'),C_821) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_821,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_820),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_821,u1_struct_0(A_820),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_821)
      | ~ l1_struct_0(A_820) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4826])).

tff(c_4890,plain,(
    ! [C_821] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_821)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_821)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_821) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_821,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_821,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_821)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_4881])).

tff(c_4902,plain,(
    ! [C_821] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_821)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_821)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_821) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_821,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_821,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_821)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_91,c_91,c_4890])).

tff(c_12668,plain,(
    ! [C_1692] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),C_1692)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_1692)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),C_1692) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1692,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1692,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1692) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12660,c_5628,c_5628,c_5628,c_5628,c_5628,c_4902])).

tff(c_12677,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5692,c_12668])).

tff(c_12681,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5700,c_5699,c_5693,c_833,c_5670,c_12677])).

tff(c_12682,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12681,c_5670])).

tff(c_42,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_tops_2(A_23,B_24,C_25) = k2_funct_1(C_25)
      | ~ v2_funct_1(C_25)
      | k2_relset_1(A_23,B_24,C_25) != B_24
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_2(C_25,A_23,B_24)
      | ~ v1_funct_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6160,plain,(
    ! [B_946,A_947,C_948] :
      ( k2_tops_2(B_946,A_947,k2_funct_1(C_948)) = k2_funct_1(k2_funct_1(C_948))
      | ~ v2_funct_1(k2_funct_1(C_948))
      | k2_relset_1(B_946,A_947,k2_funct_1(C_948)) != A_947
      | ~ v1_funct_2(k2_funct_1(C_948),B_946,A_947)
      | ~ v1_funct_1(k2_funct_1(C_948))
      | k2_relset_1(A_947,B_946,C_948) != B_946
      | ~ v2_funct_1(C_948)
      | ~ m1_subset_1(C_948,k1_zfmisc_1(k2_zfmisc_1(A_947,B_946)))
      | ~ v1_funct_2(C_948,A_947,B_946)
      | ~ v1_funct_1(C_948) ) ),
    inference(resolution,[status(thm)],[c_3694,c_42])).

tff(c_6163,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5699,c_6160])).

tff(c_6173,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5700,c_833,c_5693,c_3658,c_5694,c_6163])).

tff(c_6259,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6173])).

tff(c_9074,plain,(
    ! [C_870] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),C_870)) = k1_relat_1('#skF_3')
      | ~ v2_funct_1(C_870)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),C_870) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_870,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_870,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_870)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_5628,c_5628,c_5628,c_5628,c_5628,c_5232])).

tff(c_9075,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_9074])).

tff(c_9078,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_9075])).

tff(c_9082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9078])).

tff(c_9158,plain,(
    ! [C_1362] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),C_1362)) = k1_relat_1('#skF_3')
      | ~ v2_funct_1(C_1362)
      | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),C_1362) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_1362,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_1362,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_1362) ) ),
    inference(splitRight,[status(thm)],[c_9074])).

tff(c_9167,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5692,c_9158])).

tff(c_9171,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5700,c_5699,c_5693,c_833,c_9167])).

tff(c_9173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6259,c_9171])).

tff(c_9175,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6173])).

tff(c_16,plain,(
    ! [A_7] :
      ( v2_funct_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_9174,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6173])).

tff(c_9180,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9174])).

tff(c_9194,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_9180])).

tff(c_9198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_68,c_833,c_9194])).

tff(c_9200,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9174])).

tff(c_5698,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_138])).

tff(c_5701,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_91])).

tff(c_4397,plain,(
    ! [A_765,B_766,C_767] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_765),u1_struct_0(B_766),C_767),B_766,A_765)
      | ~ v3_tops_2(C_767,A_765,B_766)
      | ~ m1_subset_1(C_767,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_765),u1_struct_0(B_766))))
      | ~ v1_funct_2(C_767,u1_struct_0(A_765),u1_struct_0(B_766))
      | ~ v1_funct_1(C_767)
      | ~ l1_pre_topc(B_766)
      | ~ l1_pre_topc(A_765) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5336,plain,(
    ! [A_911,B_912,A_913] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_911),u1_struct_0(B_912),A_913),B_912,A_911)
      | ~ v3_tops_2(A_913,A_911,B_912)
      | ~ v1_funct_2(A_913,u1_struct_0(A_911),u1_struct_0(B_912))
      | ~ v1_funct_1(A_913)
      | ~ l1_pre_topc(B_912)
      | ~ l1_pre_topc(A_911)
      | ~ r1_tarski(A_913,k2_zfmisc_1(u1_struct_0(A_911),u1_struct_0(B_912))) ) ),
    inference(resolution,[status(thm)],[c_10,c_4397])).

tff(c_5350,plain,(
    ! [A_911,A_913] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_911),k2_struct_0('#skF_2'),A_913),'#skF_2',A_911)
      | ~ v3_tops_2(A_913,A_911,'#skF_2')
      | ~ v1_funct_2(A_913,u1_struct_0(A_911),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_913)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_911)
      | ~ r1_tarski(A_913,k2_zfmisc_1(u1_struct_0(A_911),u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_5336])).

tff(c_10251,plain,(
    ! [A_1496,A_1497] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_1496),k2_struct_0('#skF_2'),A_1497),'#skF_2',A_1496)
      | ~ v3_tops_2(A_1497,A_1496,'#skF_2')
      | ~ v1_funct_2(A_1497,u1_struct_0(A_1496),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1497)
      | ~ l1_pre_topc(A_1496)
      | ~ r1_tarski(A_1497,k2_zfmisc_1(u1_struct_0(A_1496),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_70,c_90,c_5350])).

tff(c_10254,plain,(
    ! [A_1497] :
      ( v5_pre_topc(k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),A_1497),'#skF_2','#skF_1')
      | ~ v3_tops_2(A_1497,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_1497,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1497)
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_1497,k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5701,c_10251])).

tff(c_10274,plain,(
    ! [A_1501] :
      ( v5_pre_topc(k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),A_1501),'#skF_2','#skF_1')
      | ~ v3_tops_2(A_1501,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_1501,k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_1501)
      | ~ r1_tarski(A_1501,k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5701,c_74,c_5701,c_10254])).

tff(c_10277,plain,
    ( v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5692,c_10274])).

tff(c_10279,plain,(
    v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5698,c_68,c_5700,c_62,c_10277])).

tff(c_9199,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9174])).

tff(c_4994,plain,(
    ! [C_828,A_829,B_830] :
      ( v3_tops_2(C_828,A_829,B_830)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_829),u1_struct_0(B_830),C_828),B_830,A_829)
      | ~ v5_pre_topc(C_828,A_829,B_830)
      | ~ v2_funct_1(C_828)
      | k2_relset_1(u1_struct_0(A_829),u1_struct_0(B_830),C_828) != k2_struct_0(B_830)
      | k1_relset_1(u1_struct_0(A_829),u1_struct_0(B_830),C_828) != k2_struct_0(A_829)
      | ~ m1_subset_1(C_828,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_829),u1_struct_0(B_830))))
      | ~ v1_funct_2(C_828,u1_struct_0(A_829),u1_struct_0(B_830))
      | ~ v1_funct_1(C_828)
      | ~ l1_pre_topc(B_830)
      | ~ l1_pre_topc(A_829) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4998,plain,(
    ! [C_828,A_829] :
      ( v3_tops_2(C_828,A_829,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_829),k2_struct_0('#skF_1'),C_828),'#skF_1',A_829)
      | ~ v5_pre_topc(C_828,A_829,'#skF_1')
      | ~ v2_funct_1(C_828)
      | k2_relset_1(u1_struct_0(A_829),u1_struct_0('#skF_1'),C_828) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_829),u1_struct_0('#skF_1'),C_828) != k2_struct_0(A_829)
      | ~ m1_subset_1(C_828,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_829),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_828,u1_struct_0(A_829),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_828)
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_829) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_4994])).

tff(c_5006,plain,(
    ! [C_828,A_829] :
      ( v3_tops_2(C_828,A_829,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_829),k2_struct_0('#skF_1'),C_828),'#skF_1',A_829)
      | ~ v5_pre_topc(C_828,A_829,'#skF_1')
      | ~ v2_funct_1(C_828)
      | k2_relset_1(u1_struct_0(A_829),k2_struct_0('#skF_1'),C_828) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_829),k2_struct_0('#skF_1'),C_828) != k2_struct_0(A_829)
      | ~ m1_subset_1(C_828,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_829),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_828,u1_struct_0(A_829),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_828)
      | ~ l1_pre_topc(A_829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_91,c_91,c_91,c_91,c_4998])).

tff(c_16558,plain,(
    ! [C_2268,A_2269] :
      ( v3_tops_2(C_2268,A_2269,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_2269),k1_relat_1('#skF_3'),C_2268),'#skF_1',A_2269)
      | ~ v5_pre_topc(C_2268,A_2269,'#skF_1')
      | ~ v2_funct_1(C_2268)
      | k2_relset_1(u1_struct_0(A_2269),k1_relat_1('#skF_3'),C_2268) != k1_relat_1('#skF_3')
      | k1_relset_1(u1_struct_0(A_2269),k1_relat_1('#skF_3'),C_2268) != k2_struct_0(A_2269)
      | ~ m1_subset_1(C_2268,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2269),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_2268,u1_struct_0(A_2269),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_2268)
      | ~ l1_pre_topc(A_2269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5628,c_5628,c_5628,c_5628,c_5628,c_5628,c_5006])).

tff(c_16564,plain,(
    ! [C_2268] :
      ( v3_tops_2(C_2268,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_2268),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_2268,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_2268)
      | k2_relset_1(u1_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_2268) != k1_relat_1('#skF_3')
      | k1_relset_1(u1_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_2268) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_2268,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_2268,u1_struct_0('#skF_2'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_2268)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_16558])).

tff(c_17234,plain,(
    ! [C_2347] :
      ( v3_tops_2(C_2347,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_2347),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_2347,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_2347)
      | k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_2347) != k1_relat_1('#skF_3')
      | k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),C_2347) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_2347,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_2347,k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(C_2347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_90,c_90,c_90,c_90,c_16564])).

tff(c_17375,plain,(
    ! [A_2354] :
      ( v3_tops_2(A_2354,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),A_2354),'#skF_1','#skF_2')
      | ~ v5_pre_topc(A_2354,'#skF_2','#skF_1')
      | ~ v2_funct_1(A_2354)
      | k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),A_2354) != k1_relat_1('#skF_3')
      | k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),A_2354) != k2_struct_0('#skF_2')
      | ~ v1_funct_2(A_2354,k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(A_2354)
      | ~ r1_tarski(A_2354,k2_zfmisc_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_17234])).

tff(c_17385,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9199,c_17375])).

tff(c_17388,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3658,c_5694,c_12682,c_9175,c_9200,c_10279,c_17385])).

tff(c_17389,plain,
    ( ~ v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3688,c_17388])).

tff(c_17402,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_17389])).

tff(c_17405,plain,
    ( k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3729,c_17402])).

tff(c_17409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5700,c_5699,c_833,c_5693,c_17405])).

tff(c_17410,plain,(
    ~ v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_17389])).

tff(c_17414,plain,
    ( ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_17410])).

tff(c_17417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_68,c_833,c_4944,c_17414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.25/6.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.25/6.17  
% 13.25/6.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.25/6.17  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 13.25/6.17  
% 13.25/6.17  %Foreground sorts:
% 13.25/6.17  
% 13.25/6.17  
% 13.25/6.17  %Background operators:
% 13.25/6.17  
% 13.25/6.17  
% 13.25/6.17  %Foreground operators:
% 13.25/6.17  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.25/6.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.25/6.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.25/6.17  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.25/6.17  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.25/6.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.25/6.17  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 13.25/6.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.25/6.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.25/6.17  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 13.25/6.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.25/6.17  tff('#skF_2', type, '#skF_2': $i).
% 13.25/6.17  tff('#skF_3', type, '#skF_3': $i).
% 13.25/6.17  tff('#skF_1', type, '#skF_1': $i).
% 13.25/6.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.25/6.17  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.25/6.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.25/6.17  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 13.25/6.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.25/6.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.25/6.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.25/6.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.25/6.17  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 13.25/6.17  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.25/6.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.25/6.17  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 13.25/6.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.25/6.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.25/6.17  
% 13.25/6.20  tff(f_178, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 13.25/6.20  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 13.25/6.20  tff(f_95, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 13.25/6.20  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.25/6.20  tff(f_91, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 13.25/6.21  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 13.25/6.21  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 13.25/6.21  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.25/6.21  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.25/6.21  tff(f_111, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 13.25/6.21  tff(f_158, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 13.25/6.21  tff(f_53, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 13.25/6.21  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 13.25/6.21  tff(c_40, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.25/6.21  tff(c_78, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.25/6.21  tff(c_83, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_40, c_78])).
% 13.25/6.21  tff(c_91, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_83])).
% 13.25/6.21  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 13.25/6.21  tff(c_90, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_83])).
% 13.25/6.21  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 13.25/6.21  tff(c_92, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_64])).
% 13.25/6.21  tff(c_130, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_92])).
% 13.25/6.21  tff(c_24, plain, (![C_11, A_9, B_10]: (v1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.25/6.21  tff(c_137, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_24])).
% 13.25/6.21  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 13.25/6.21  tff(c_66, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 13.25/6.21  tff(c_93, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_66])).
% 13.25/6.21  tff(c_102, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_93])).
% 13.25/6.21  tff(c_312, plain, (![C_109, A_110, B_111]: (v1_funct_1(k2_funct_1(C_109)) | k2_relset_1(A_110, B_111, C_109)!=B_111 | ~v2_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_2(C_109, A_110, B_111) | ~v1_funct_1(C_109))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.25/6.21  tff(c_315, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_312])).
% 13.25/6.21  tff(c_322, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102, c_315])).
% 13.25/6.21  tff(c_392, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_322])).
% 13.25/6.21  tff(c_62, plain, (v3_tops_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 13.25/6.21  tff(c_496, plain, (![C_167, A_168, B_169]: (v2_funct_1(C_167) | ~v3_tops_2(C_167, A_168, B_169) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168), u1_struct_0(B_169)))) | ~v1_funct_2(C_167, u1_struct_0(A_168), u1_struct_0(B_169)) | ~v1_funct_1(C_167) | ~l1_pre_topc(B_169) | ~l1_pre_topc(A_168))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.25/6.21  tff(c_503, plain, (![C_167, B_169]: (v2_funct_1(C_167) | ~v3_tops_2(C_167, '#skF_1', B_169) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_169)))) | ~v1_funct_2(C_167, u1_struct_0('#skF_1'), u1_struct_0(B_169)) | ~v1_funct_1(C_167) | ~l1_pre_topc(B_169) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_496])).
% 13.25/6.21  tff(c_793, plain, (![C_242, B_243]: (v2_funct_1(C_242) | ~v3_tops_2(C_242, '#skF_1', B_243) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_243)))) | ~v1_funct_2(C_242, k2_struct_0('#skF_1'), u1_struct_0(B_243)) | ~v1_funct_1(C_242) | ~l1_pre_topc(B_243))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_91, c_503])).
% 13.25/6.21  tff(c_807, plain, (![C_242]: (v2_funct_1(C_242) | ~v3_tops_2(C_242, '#skF_1', '#skF_2') | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_242, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_242) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_793])).
% 13.25/6.21  tff(c_814, plain, (![C_244]: (v2_funct_1(C_244) | ~v3_tops_2(C_244, '#skF_1', '#skF_2') | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_244, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_244))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_90, c_807])).
% 13.25/6.21  tff(c_821, plain, (v2_funct_1('#skF_3') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_814])).
% 13.25/6.21  tff(c_829, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102, c_62, c_821])).
% 13.25/6.21  tff(c_831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_392, c_829])).
% 13.25/6.21  tff(c_833, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_322])).
% 13.25/6.21  tff(c_3958, plain, (![C_694, A_695, B_696]: (v5_pre_topc(C_694, A_695, B_696) | ~v3_tops_2(C_694, A_695, B_696) | ~m1_subset_1(C_694, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_695), u1_struct_0(B_696)))) | ~v1_funct_2(C_694, u1_struct_0(A_695), u1_struct_0(B_696)) | ~v1_funct_1(C_694) | ~l1_pre_topc(B_696) | ~l1_pre_topc(A_695))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.25/6.21  tff(c_3978, plain, (![C_694, A_695]: (v5_pre_topc(C_694, A_695, '#skF_2') | ~v3_tops_2(C_694, A_695, '#skF_2') | ~m1_subset_1(C_694, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_695), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_694, u1_struct_0(A_695), u1_struct_0('#skF_2')) | ~v1_funct_1(C_694) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_695))), inference(superposition, [status(thm), theory('equality')], [c_90, c_3958])).
% 13.25/6.21  tff(c_4908, plain, (![C_822, A_823]: (v5_pre_topc(C_822, A_823, '#skF_2') | ~v3_tops_2(C_822, A_823, '#skF_2') | ~m1_subset_1(C_822, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_823), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_822, u1_struct_0(A_823), k2_struct_0('#skF_2')) | ~v1_funct_1(C_822) | ~l1_pre_topc(A_823))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_90, c_3978])).
% 13.25/6.21  tff(c_4919, plain, (![C_822]: (v5_pre_topc(C_822, '#skF_1', '#skF_2') | ~v3_tops_2(C_822, '#skF_1', '#skF_2') | ~m1_subset_1(C_822, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_822, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_822) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_4908])).
% 13.25/6.21  tff(c_4929, plain, (![C_824]: (v5_pre_topc(C_824, '#skF_1', '#skF_2') | ~v3_tops_2(C_824, '#skF_1', '#skF_2') | ~m1_subset_1(C_824, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_824, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_824))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_91, c_4919])).
% 13.25/6.21  tff(c_4936, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_4929])).
% 13.25/6.21  tff(c_4944, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102, c_62, c_4936])).
% 13.25/6.21  tff(c_22, plain, (![A_8]: (k2_funct_1(k2_funct_1(A_8))=A_8 | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.25/6.21  tff(c_281, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.25/6.21  tff(c_289, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_281])).
% 13.25/6.21  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.25/6.21  tff(c_138, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_130, c_8])).
% 13.25/6.21  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.25/6.21  tff(c_4088, plain, (![A_714, B_715, C_716]: (k1_relset_1(u1_struct_0(A_714), u1_struct_0(B_715), C_716)=k2_struct_0(A_714) | ~v3_tops_2(C_716, A_714, B_715) | ~m1_subset_1(C_716, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_714), u1_struct_0(B_715)))) | ~v1_funct_2(C_716, u1_struct_0(A_714), u1_struct_0(B_715)) | ~v1_funct_1(C_716) | ~l1_pre_topc(B_715) | ~l1_pre_topc(A_714))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.25/6.21  tff(c_5149, plain, (![A_861, B_862, A_863]: (k1_relset_1(u1_struct_0(A_861), u1_struct_0(B_862), A_863)=k2_struct_0(A_861) | ~v3_tops_2(A_863, A_861, B_862) | ~v1_funct_2(A_863, u1_struct_0(A_861), u1_struct_0(B_862)) | ~v1_funct_1(A_863) | ~l1_pre_topc(B_862) | ~l1_pre_topc(A_861) | ~r1_tarski(A_863, k2_zfmisc_1(u1_struct_0(A_861), u1_struct_0(B_862))))), inference(resolution, [status(thm)], [c_10, c_4088])).
% 13.25/6.21  tff(c_5160, plain, (![B_862, A_863]: (k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_862), A_863)=k2_struct_0('#skF_1') | ~v3_tops_2(A_863, '#skF_1', B_862) | ~v1_funct_2(A_863, u1_struct_0('#skF_1'), u1_struct_0(B_862)) | ~v1_funct_1(A_863) | ~l1_pre_topc(B_862) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_863, k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_862))))), inference(superposition, [status(thm), theory('equality')], [c_91, c_5149])).
% 13.25/6.21  tff(c_5581, plain, (![B_931, A_932]: (k1_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_931), A_932)=k2_struct_0('#skF_1') | ~v3_tops_2(A_932, '#skF_1', B_931) | ~v1_funct_2(A_932, k2_struct_0('#skF_1'), u1_struct_0(B_931)) | ~v1_funct_1(A_932) | ~l1_pre_topc(B_931) | ~r1_tarski(A_932, k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_931))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_91, c_91, c_5160])).
% 13.25/6.21  tff(c_5595, plain, (![A_932]: (k1_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), A_932)=k2_struct_0('#skF_1') | ~v3_tops_2(A_932, '#skF_1', '#skF_2') | ~v1_funct_2(A_932, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_932) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_932, k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_90, c_5581])).
% 13.25/6.21  tff(c_5608, plain, (![A_933]: (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_933)=k2_struct_0('#skF_1') | ~v3_tops_2(A_933, '#skF_1', '#skF_2') | ~v1_funct_2(A_933, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_933) | ~r1_tarski(A_933, k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_90, c_90, c_5595])).
% 13.25/6.21  tff(c_5619, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_138, c_5608])).
% 13.25/6.21  tff(c_5628, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102, c_62, c_289, c_5619])).
% 13.25/6.21  tff(c_5700, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_102])).
% 13.25/6.21  tff(c_5699, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_130])).
% 13.25/6.21  tff(c_1416, plain, (![A_376, B_377, C_378]: (k1_relset_1(u1_struct_0(A_376), u1_struct_0(B_377), C_378)=k2_struct_0(A_376) | ~v3_tops_2(C_378, A_376, B_377) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_376), u1_struct_0(B_377)))) | ~v1_funct_2(C_378, u1_struct_0(A_376), u1_struct_0(B_377)) | ~v1_funct_1(C_378) | ~l1_pre_topc(B_377) | ~l1_pre_topc(A_376))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.25/6.21  tff(c_2354, plain, (![A_534, B_535, A_536]: (k1_relset_1(u1_struct_0(A_534), u1_struct_0(B_535), A_536)=k2_struct_0(A_534) | ~v3_tops_2(A_536, A_534, B_535) | ~v1_funct_2(A_536, u1_struct_0(A_534), u1_struct_0(B_535)) | ~v1_funct_1(A_536) | ~l1_pre_topc(B_535) | ~l1_pre_topc(A_534) | ~r1_tarski(A_536, k2_zfmisc_1(u1_struct_0(A_534), u1_struct_0(B_535))))), inference(resolution, [status(thm)], [c_10, c_1416])).
% 13.25/6.21  tff(c_2365, plain, (![B_535, A_536]: (k1_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_535), A_536)=k2_struct_0('#skF_1') | ~v3_tops_2(A_536, '#skF_1', B_535) | ~v1_funct_2(A_536, u1_struct_0('#skF_1'), u1_struct_0(B_535)) | ~v1_funct_1(A_536) | ~l1_pre_topc(B_535) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_536, k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_535))))), inference(superposition, [status(thm), theory('equality')], [c_91, c_2354])).
% 13.25/6.21  tff(c_2391, plain, (![B_537, A_538]: (k1_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_537), A_538)=k2_struct_0('#skF_1') | ~v3_tops_2(A_538, '#skF_1', B_537) | ~v1_funct_2(A_538, k2_struct_0('#skF_1'), u1_struct_0(B_537)) | ~v1_funct_1(A_538) | ~l1_pre_topc(B_537) | ~r1_tarski(A_538, k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_537))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_91, c_91, c_2365])).
% 13.25/6.21  tff(c_2405, plain, (![A_538]: (k1_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), A_538)=k2_struct_0('#skF_1') | ~v3_tops_2(A_538, '#skF_1', '#skF_2') | ~v1_funct_2(A_538, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_538) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_538, k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_90, c_2391])).
% 13.25/6.21  tff(c_2435, plain, (![A_540]: (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_540)=k2_struct_0('#skF_1') | ~v3_tops_2(A_540, '#skF_1', '#skF_2') | ~v1_funct_2(A_540, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_540) | ~r1_tarski(A_540, k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_90, c_90, c_2405])).
% 13.25/6.21  tff(c_2446, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_138, c_2435])).
% 13.25/6.21  tff(c_2455, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102, c_62, c_289, c_2446])).
% 13.25/6.21  tff(c_832, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_322])).
% 13.25/6.21  tff(c_834, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_832])).
% 13.25/6.21  tff(c_2513, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_834])).
% 13.25/6.21  tff(c_2520, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_102])).
% 13.25/6.21  tff(c_2517, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_138])).
% 13.25/6.21  tff(c_2521, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2455, c_91])).
% 13.25/6.21  tff(c_1699, plain, (![A_412, B_413, C_414]: (k2_relset_1(u1_struct_0(A_412), u1_struct_0(B_413), C_414)=k2_struct_0(B_413) | ~v3_tops_2(C_414, A_412, B_413) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412), u1_struct_0(B_413)))) | ~v1_funct_2(C_414, u1_struct_0(A_412), u1_struct_0(B_413)) | ~v1_funct_1(C_414) | ~l1_pre_topc(B_413) | ~l1_pre_topc(A_412))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.25/6.21  tff(c_2771, plain, (![A_543, B_544, A_545]: (k2_relset_1(u1_struct_0(A_543), u1_struct_0(B_544), A_545)=k2_struct_0(B_544) | ~v3_tops_2(A_545, A_543, B_544) | ~v1_funct_2(A_545, u1_struct_0(A_543), u1_struct_0(B_544)) | ~v1_funct_1(A_545) | ~l1_pre_topc(B_544) | ~l1_pre_topc(A_543) | ~r1_tarski(A_545, k2_zfmisc_1(u1_struct_0(A_543), u1_struct_0(B_544))))), inference(resolution, [status(thm)], [c_10, c_1699])).
% 13.25/6.21  tff(c_2791, plain, (![A_543, A_545]: (k2_relset_1(u1_struct_0(A_543), u1_struct_0('#skF_2'), A_545)=k2_struct_0('#skF_2') | ~v3_tops_2(A_545, A_543, '#skF_2') | ~v1_funct_2(A_545, u1_struct_0(A_543), u1_struct_0('#skF_2')) | ~v1_funct_1(A_545) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_543) | ~r1_tarski(A_545, k2_zfmisc_1(u1_struct_0(A_543), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_90, c_2771])).
% 13.25/6.21  tff(c_2915, plain, (![A_552, A_553]: (k2_relset_1(u1_struct_0(A_552), k2_struct_0('#skF_2'), A_553)=k2_struct_0('#skF_2') | ~v3_tops_2(A_553, A_552, '#skF_2') | ~v1_funct_2(A_553, u1_struct_0(A_552), k2_struct_0('#skF_2')) | ~v1_funct_1(A_553) | ~l1_pre_topc(A_552) | ~r1_tarski(A_553, k2_zfmisc_1(u1_struct_0(A_552), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_90, c_90, c_2791])).
% 13.25/6.21  tff(c_2918, plain, (![A_553]: (k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_553)=k2_struct_0('#skF_2') | ~v3_tops_2(A_553, '#skF_1', '#skF_2') | ~v1_funct_2(A_553, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_553) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_553, k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_2521, c_2915])).
% 13.25/6.21  tff(c_3637, plain, (![A_615]: (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), A_615)=k2_struct_0('#skF_2') | ~v3_tops_2(A_615, '#skF_1', '#skF_2') | ~v1_funct_2(A_615, k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_615) | ~r1_tarski(A_615, k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2521, c_2521, c_2918])).
% 13.25/6.21  tff(c_3640, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2517, c_3637])).
% 13.25/6.21  tff(c_3655, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2520, c_62, c_3640])).
% 13.25/6.21  tff(c_3657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2513, c_3655])).
% 13.25/6.21  tff(c_3659, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_832])).
% 13.25/6.21  tff(c_5693, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_3659])).
% 13.25/6.21  tff(c_3694, plain, (![C_624, B_625, A_626]: (m1_subset_1(k2_funct_1(C_624), k1_zfmisc_1(k2_zfmisc_1(B_625, A_626))) | k2_relset_1(A_626, B_625, C_624)!=B_625 | ~v2_funct_1(C_624) | ~m1_subset_1(C_624, k1_zfmisc_1(k2_zfmisc_1(A_626, B_625))) | ~v1_funct_2(C_624, A_626, B_625) | ~v1_funct_1(C_624))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.25/6.21  tff(c_3729, plain, (![C_624, B_625, A_626]: (r1_tarski(k2_funct_1(C_624), k2_zfmisc_1(B_625, A_626)) | k2_relset_1(A_626, B_625, C_624)!=B_625 | ~v2_funct_1(C_624) | ~m1_subset_1(C_624, k1_zfmisc_1(k2_zfmisc_1(A_626, B_625))) | ~v1_funct_2(C_624, A_626, B_625) | ~v1_funct_1(C_624))), inference(resolution, [status(thm)], [c_3694, c_8])).
% 13.25/6.21  tff(c_3676, plain, (![A_616, B_617, C_618]: (k2_tops_2(A_616, B_617, C_618)=k2_funct_1(C_618) | ~v2_funct_1(C_618) | k2_relset_1(A_616, B_617, C_618)!=B_617 | ~m1_subset_1(C_618, k1_zfmisc_1(k2_zfmisc_1(A_616, B_617))) | ~v1_funct_2(C_618, A_616, B_617) | ~v1_funct_1(C_618))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.25/6.21  tff(c_3679, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_3676])).
% 13.25/6.21  tff(c_3686, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102, c_3659, c_833, c_3679])).
% 13.25/6.21  tff(c_60, plain, (~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 13.25/6.21  tff(c_122, plain, (~v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_90, c_60])).
% 13.25/6.21  tff(c_3688, plain, (~v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3686, c_122])).
% 13.25/6.21  tff(c_3658, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_832])).
% 13.25/6.21  tff(c_368, plain, (![C_128, B_129, A_130]: (v1_funct_2(k2_funct_1(C_128), B_129, A_130) | k2_relset_1(A_130, B_129, C_128)!=B_129 | ~v2_funct_1(C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_130, B_129))) | ~v1_funct_2(C_128, A_130, B_129) | ~v1_funct_1(C_128))), inference(cnfTransformation, [status(thm)], [f_91])).
% 13.25/6.21  tff(c_371, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_368])).
% 13.25/6.21  tff(c_378, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102, c_371])).
% 13.25/6.21  tff(c_3661, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_833, c_378])).
% 13.25/6.21  tff(c_3662, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3661])).
% 13.25/6.21  tff(c_3668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3659, c_3662])).
% 13.25/6.21  tff(c_3669, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_3661])).
% 13.25/6.21  tff(c_5694, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_3669])).
% 13.25/6.21  tff(c_30, plain, (![A_15, B_16, C_17]: (k1_relset_1(A_15, B_16, C_17)=k1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.25/6.21  tff(c_5129, plain, (![B_858, A_859, C_860]: (k1_relset_1(B_858, A_859, k2_funct_1(C_860))=k1_relat_1(k2_funct_1(C_860)) | k2_relset_1(A_859, B_858, C_860)!=B_858 | ~v2_funct_1(C_860) | ~m1_subset_1(C_860, k1_zfmisc_1(k2_zfmisc_1(A_859, B_858))) | ~v1_funct_2(C_860, A_859, B_858) | ~v1_funct_1(C_860))), inference(resolution, [status(thm)], [c_3694, c_30])).
% 13.25/6.21  tff(c_5135, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_5129])).
% 13.25/6.21  tff(c_5143, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102, c_833, c_3659, c_5135])).
% 13.25/6.21  tff(c_5670, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_5143])).
% 13.25/6.21  tff(c_5692, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_3686])).
% 13.25/6.21  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 13.25/6.21  tff(c_4547, plain, (![B_789, A_790, C_791]: (k2_relset_1(u1_struct_0(B_789), u1_struct_0(A_790), k2_tops_2(u1_struct_0(A_790), u1_struct_0(B_789), C_791))=k2_struct_0(A_790) | ~v2_funct_1(C_791) | k2_relset_1(u1_struct_0(A_790), u1_struct_0(B_789), C_791)!=k2_struct_0(B_789) | ~m1_subset_1(C_791, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790), u1_struct_0(B_789)))) | ~v1_funct_2(C_791, u1_struct_0(A_790), u1_struct_0(B_789)) | ~v1_funct_1(C_791) | ~l1_struct_0(B_789) | v2_struct_0(B_789) | ~l1_struct_0(A_790))), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.25/6.21  tff(c_4568, plain, (![A_790, C_791]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_790), k2_tops_2(u1_struct_0(A_790), u1_struct_0('#skF_2'), C_791))=k2_struct_0(A_790) | ~v2_funct_1(C_791) | k2_relset_1(u1_struct_0(A_790), u1_struct_0('#skF_2'), C_791)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_791, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_791, u1_struct_0(A_790), u1_struct_0('#skF_2')) | ~v1_funct_1(C_791) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_790))), inference(superposition, [status(thm), theory('equality')], [c_90, c_4547])).
% 13.25/6.21  tff(c_4584, plain, (![A_790, C_791]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_790), k2_tops_2(u1_struct_0(A_790), k2_struct_0('#skF_2'), C_791))=k2_struct_0(A_790) | ~v2_funct_1(C_791) | k2_relset_1(u1_struct_0(A_790), k2_struct_0('#skF_2'), C_791)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_791, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_791, u1_struct_0(A_790), k2_struct_0('#skF_2')) | ~v1_funct_1(C_791) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_790))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_90, c_90, c_4568])).
% 13.25/6.21  tff(c_4585, plain, (![A_790, C_791]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_790), k2_tops_2(u1_struct_0(A_790), k2_struct_0('#skF_2'), C_791))=k2_struct_0(A_790) | ~v2_funct_1(C_791) | k2_relset_1(u1_struct_0(A_790), k2_struct_0('#skF_2'), C_791)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_791, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_791, u1_struct_0(A_790), k2_struct_0('#skF_2')) | ~v1_funct_1(C_791) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_790))), inference(negUnitSimplification, [status(thm)], [c_72, c_4584])).
% 13.25/6.21  tff(c_4743, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4585])).
% 13.25/6.21  tff(c_4746, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_4743])).
% 13.25/6.21  tff(c_4750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_4746])).
% 13.25/6.21  tff(c_4752, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_4585])).
% 13.25/6.21  tff(c_4577, plain, (![A_790, C_791]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_790), k2_tops_2(u1_struct_0(A_790), k2_struct_0('#skF_2'), C_791))=k2_struct_0(A_790) | ~v2_funct_1(C_791) | k2_relset_1(u1_struct_0(A_790), u1_struct_0('#skF_2'), C_791)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_791, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_791, u1_struct_0(A_790), u1_struct_0('#skF_2')) | ~v1_funct_1(C_791) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_790))), inference(superposition, [status(thm), theory('equality')], [c_90, c_4547])).
% 13.25/6.21  tff(c_4588, plain, (![A_790, C_791]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_790), k2_tops_2(u1_struct_0(A_790), k2_struct_0('#skF_2'), C_791))=k2_struct_0(A_790) | ~v2_funct_1(C_791) | k2_relset_1(u1_struct_0(A_790), k2_struct_0('#skF_2'), C_791)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_791, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_791, u1_struct_0(A_790), k2_struct_0('#skF_2')) | ~v1_funct_1(C_791) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_790))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_90, c_90, c_4577])).
% 13.25/6.21  tff(c_4589, plain, (![A_790, C_791]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_790), k2_tops_2(u1_struct_0(A_790), k2_struct_0('#skF_2'), C_791))=k2_struct_0(A_790) | ~v2_funct_1(C_791) | k2_relset_1(u1_struct_0(A_790), k2_struct_0('#skF_2'), C_791)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_791, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_790), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_791, u1_struct_0(A_790), k2_struct_0('#skF_2')) | ~v1_funct_1(C_791) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_790))), inference(negUnitSimplification, [status(thm)], [c_72, c_4588])).
% 13.25/6.21  tff(c_5210, plain, (![A_869, C_870]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_869), k2_tops_2(u1_struct_0(A_869), k2_struct_0('#skF_2'), C_870))=k2_struct_0(A_869) | ~v2_funct_1(C_870) | k2_relset_1(u1_struct_0(A_869), k2_struct_0('#skF_2'), C_870)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_870, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_869), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_870, u1_struct_0(A_869), k2_struct_0('#skF_2')) | ~v1_funct_1(C_870) | ~l1_struct_0(A_869))), inference(demodulation, [status(thm), theory('equality')], [c_4752, c_4589])).
% 13.25/6.21  tff(c_5222, plain, (![C_870]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_870))=k2_struct_0('#skF_1') | ~v2_funct_1(C_870) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_870)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_870, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_870, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_870) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_5210])).
% 13.25/6.21  tff(c_5232, plain, (![C_870]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_870))=k2_struct_0('#skF_1') | ~v2_funct_1(C_870) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_870)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_870, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_870, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_870) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_91, c_91, c_5222])).
% 13.25/6.21  tff(c_12650, plain, (![C_870]: (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), C_870))=k1_relat_1('#skF_3') | ~v2_funct_1(C_870) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), C_870)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_870, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_870, k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_870) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_5628, c_5628, c_5628, c_5628, c_5628, c_5232])).
% 13.25/6.21  tff(c_12651, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_12650])).
% 13.25/6.21  tff(c_12654, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_12651])).
% 13.25/6.21  tff(c_12658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_12654])).
% 13.25/6.21  tff(c_12660, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_12650])).
% 13.25/6.21  tff(c_4781, plain, (![B_813, A_814, C_815]: (k1_relset_1(u1_struct_0(B_813), u1_struct_0(A_814), k2_tops_2(u1_struct_0(A_814), u1_struct_0(B_813), C_815))=k2_struct_0(B_813) | ~v2_funct_1(C_815) | k2_relset_1(u1_struct_0(A_814), u1_struct_0(B_813), C_815)!=k2_struct_0(B_813) | ~m1_subset_1(C_815, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_814), u1_struct_0(B_813)))) | ~v1_funct_2(C_815, u1_struct_0(A_814), u1_struct_0(B_813)) | ~v1_funct_1(C_815) | ~l1_struct_0(B_813) | v2_struct_0(B_813) | ~l1_struct_0(A_814))), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.25/6.21  tff(c_4811, plain, (![A_814, C_815]: (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_814), k2_tops_2(u1_struct_0(A_814), k2_struct_0('#skF_2'), C_815))=k2_struct_0('#skF_2') | ~v2_funct_1(C_815) | k2_relset_1(u1_struct_0(A_814), u1_struct_0('#skF_2'), C_815)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_815, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_814), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_815, u1_struct_0(A_814), u1_struct_0('#skF_2')) | ~v1_funct_1(C_815) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_814))), inference(superposition, [status(thm), theory('equality')], [c_90, c_4781])).
% 13.25/6.21  tff(c_4826, plain, (![A_814, C_815]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_814), k2_tops_2(u1_struct_0(A_814), k2_struct_0('#skF_2'), C_815))=k2_struct_0('#skF_2') | ~v2_funct_1(C_815) | k2_relset_1(u1_struct_0(A_814), k2_struct_0('#skF_2'), C_815)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_815, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_814), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_815, u1_struct_0(A_814), k2_struct_0('#skF_2')) | ~v1_funct_1(C_815) | v2_struct_0('#skF_2') | ~l1_struct_0(A_814))), inference(demodulation, [status(thm), theory('equality')], [c_4752, c_90, c_90, c_90, c_90, c_4811])).
% 13.25/6.21  tff(c_4881, plain, (![A_820, C_821]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_820), k2_tops_2(u1_struct_0(A_820), k2_struct_0('#skF_2'), C_821))=k2_struct_0('#skF_2') | ~v2_funct_1(C_821) | k2_relset_1(u1_struct_0(A_820), k2_struct_0('#skF_2'), C_821)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_821, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_820), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_821, u1_struct_0(A_820), k2_struct_0('#skF_2')) | ~v1_funct_1(C_821) | ~l1_struct_0(A_820))), inference(negUnitSimplification, [status(thm)], [c_72, c_4826])).
% 13.25/6.21  tff(c_4890, plain, (![C_821]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_821))=k2_struct_0('#skF_2') | ~v2_funct_1(C_821) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_821)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_821, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_821, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_821) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_4881])).
% 13.25/6.21  tff(c_4902, plain, (![C_821]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_821))=k2_struct_0('#skF_2') | ~v2_funct_1(C_821) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_821)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_821, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_821, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_821) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_91, c_91, c_4890])).
% 13.25/6.21  tff(c_12668, plain, (![C_1692]: (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), C_1692))=k2_struct_0('#skF_2') | ~v2_funct_1(C_1692) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), C_1692)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_1692, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_1692, k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_1692))), inference(demodulation, [status(thm), theory('equality')], [c_12660, c_5628, c_5628, c_5628, c_5628, c_5628, c_4902])).
% 13.25/6.21  tff(c_12677, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5692, c_12668])).
% 13.25/6.21  tff(c_12681, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5700, c_5699, c_5693, c_833, c_5670, c_12677])).
% 13.25/6.21  tff(c_12682, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12681, c_5670])).
% 13.25/6.21  tff(c_42, plain, (![A_23, B_24, C_25]: (k2_tops_2(A_23, B_24, C_25)=k2_funct_1(C_25) | ~v2_funct_1(C_25) | k2_relset_1(A_23, B_24, C_25)!=B_24 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_2(C_25, A_23, B_24) | ~v1_funct_1(C_25))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.25/6.21  tff(c_6160, plain, (![B_946, A_947, C_948]: (k2_tops_2(B_946, A_947, k2_funct_1(C_948))=k2_funct_1(k2_funct_1(C_948)) | ~v2_funct_1(k2_funct_1(C_948)) | k2_relset_1(B_946, A_947, k2_funct_1(C_948))!=A_947 | ~v1_funct_2(k2_funct_1(C_948), B_946, A_947) | ~v1_funct_1(k2_funct_1(C_948)) | k2_relset_1(A_947, B_946, C_948)!=B_946 | ~v2_funct_1(C_948) | ~m1_subset_1(C_948, k1_zfmisc_1(k2_zfmisc_1(A_947, B_946))) | ~v1_funct_2(C_948, A_947, B_946) | ~v1_funct_1(C_948))), inference(resolution, [status(thm)], [c_3694, c_42])).
% 13.25/6.21  tff(c_6163, plain, (k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_5699, c_6160])).
% 13.25/6.21  tff(c_6173, plain, (k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5700, c_833, c_5693, c_3658, c_5694, c_6163])).
% 13.25/6.21  tff(c_6259, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_6173])).
% 13.25/6.21  tff(c_9074, plain, (![C_870]: (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), C_870))=k1_relat_1('#skF_3') | ~v2_funct_1(C_870) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), C_870)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_870, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_870, k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_870) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_5628, c_5628, c_5628, c_5628, c_5628, c_5232])).
% 13.25/6.21  tff(c_9075, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_9074])).
% 13.25/6.21  tff(c_9078, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_9075])).
% 13.25/6.21  tff(c_9082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_9078])).
% 13.25/6.21  tff(c_9158, plain, (![C_1362]: (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), C_1362))=k1_relat_1('#skF_3') | ~v2_funct_1(C_1362) | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), C_1362)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_1362, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_1362, k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_1362))), inference(splitRight, [status(thm)], [c_9074])).
% 13.25/6.21  tff(c_9167, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5692, c_9158])).
% 13.25/6.21  tff(c_9171, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5700, c_5699, c_5693, c_833, c_9167])).
% 13.25/6.21  tff(c_9173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6259, c_9171])).
% 13.25/6.21  tff(c_9175, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_6173])).
% 13.25/6.21  tff(c_16, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.25/6.21  tff(c_9174, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6173])).
% 13.25/6.21  tff(c_9180, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_9174])).
% 13.25/6.21  tff(c_9194, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_9180])).
% 13.25/6.21  tff(c_9198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_68, c_833, c_9194])).
% 13.25/6.21  tff(c_9200, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_9174])).
% 13.25/6.21  tff(c_5698, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_138])).
% 13.25/6.21  tff(c_5701, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_91])).
% 13.25/6.21  tff(c_4397, plain, (![A_765, B_766, C_767]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_765), u1_struct_0(B_766), C_767), B_766, A_765) | ~v3_tops_2(C_767, A_765, B_766) | ~m1_subset_1(C_767, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_765), u1_struct_0(B_766)))) | ~v1_funct_2(C_767, u1_struct_0(A_765), u1_struct_0(B_766)) | ~v1_funct_1(C_767) | ~l1_pre_topc(B_766) | ~l1_pre_topc(A_765))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.25/6.21  tff(c_5336, plain, (![A_911, B_912, A_913]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_911), u1_struct_0(B_912), A_913), B_912, A_911) | ~v3_tops_2(A_913, A_911, B_912) | ~v1_funct_2(A_913, u1_struct_0(A_911), u1_struct_0(B_912)) | ~v1_funct_1(A_913) | ~l1_pre_topc(B_912) | ~l1_pre_topc(A_911) | ~r1_tarski(A_913, k2_zfmisc_1(u1_struct_0(A_911), u1_struct_0(B_912))))), inference(resolution, [status(thm)], [c_10, c_4397])).
% 13.25/6.21  tff(c_5350, plain, (![A_911, A_913]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_911), k2_struct_0('#skF_2'), A_913), '#skF_2', A_911) | ~v3_tops_2(A_913, A_911, '#skF_2') | ~v1_funct_2(A_913, u1_struct_0(A_911), u1_struct_0('#skF_2')) | ~v1_funct_1(A_913) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_911) | ~r1_tarski(A_913, k2_zfmisc_1(u1_struct_0(A_911), u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_90, c_5336])).
% 13.25/6.21  tff(c_10251, plain, (![A_1496, A_1497]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_1496), k2_struct_0('#skF_2'), A_1497), '#skF_2', A_1496) | ~v3_tops_2(A_1497, A_1496, '#skF_2') | ~v1_funct_2(A_1497, u1_struct_0(A_1496), k2_struct_0('#skF_2')) | ~v1_funct_1(A_1497) | ~l1_pre_topc(A_1496) | ~r1_tarski(A_1497, k2_zfmisc_1(u1_struct_0(A_1496), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_70, c_90, c_5350])).
% 13.25/6.21  tff(c_10254, plain, (![A_1497]: (v5_pre_topc(k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), A_1497), '#skF_2', '#skF_1') | ~v3_tops_2(A_1497, '#skF_1', '#skF_2') | ~v1_funct_2(A_1497, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_1497) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_1497, k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_5701, c_10251])).
% 13.25/6.21  tff(c_10274, plain, (![A_1501]: (v5_pre_topc(k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), A_1501), '#skF_2', '#skF_1') | ~v3_tops_2(A_1501, '#skF_1', '#skF_2') | ~v1_funct_2(A_1501, k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_1501) | ~r1_tarski(A_1501, k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5701, c_74, c_5701, c_10254])).
% 13.25/6.21  tff(c_10277, plain, (v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_5692, c_10274])).
% 13.25/6.21  tff(c_10279, plain, (v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5698, c_68, c_5700, c_62, c_10277])).
% 13.25/6.21  tff(c_9199, plain, (k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_9174])).
% 13.25/6.21  tff(c_4994, plain, (![C_828, A_829, B_830]: (v3_tops_2(C_828, A_829, B_830) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_829), u1_struct_0(B_830), C_828), B_830, A_829) | ~v5_pre_topc(C_828, A_829, B_830) | ~v2_funct_1(C_828) | k2_relset_1(u1_struct_0(A_829), u1_struct_0(B_830), C_828)!=k2_struct_0(B_830) | k1_relset_1(u1_struct_0(A_829), u1_struct_0(B_830), C_828)!=k2_struct_0(A_829) | ~m1_subset_1(C_828, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_829), u1_struct_0(B_830)))) | ~v1_funct_2(C_828, u1_struct_0(A_829), u1_struct_0(B_830)) | ~v1_funct_1(C_828) | ~l1_pre_topc(B_830) | ~l1_pre_topc(A_829))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.25/6.21  tff(c_4998, plain, (![C_828, A_829]: (v3_tops_2(C_828, A_829, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_829), k2_struct_0('#skF_1'), C_828), '#skF_1', A_829) | ~v5_pre_topc(C_828, A_829, '#skF_1') | ~v2_funct_1(C_828) | k2_relset_1(u1_struct_0(A_829), u1_struct_0('#skF_1'), C_828)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_829), u1_struct_0('#skF_1'), C_828)!=k2_struct_0(A_829) | ~m1_subset_1(C_828, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_829), u1_struct_0('#skF_1')))) | ~v1_funct_2(C_828, u1_struct_0(A_829), u1_struct_0('#skF_1')) | ~v1_funct_1(C_828) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_829))), inference(superposition, [status(thm), theory('equality')], [c_91, c_4994])).
% 13.25/6.21  tff(c_5006, plain, (![C_828, A_829]: (v3_tops_2(C_828, A_829, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_829), k2_struct_0('#skF_1'), C_828), '#skF_1', A_829) | ~v5_pre_topc(C_828, A_829, '#skF_1') | ~v2_funct_1(C_828) | k2_relset_1(u1_struct_0(A_829), k2_struct_0('#skF_1'), C_828)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_829), k2_struct_0('#skF_1'), C_828)!=k2_struct_0(A_829) | ~m1_subset_1(C_828, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_829), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_828, u1_struct_0(A_829), k2_struct_0('#skF_1')) | ~v1_funct_1(C_828) | ~l1_pre_topc(A_829))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_91, c_91, c_91, c_91, c_4998])).
% 13.25/6.21  tff(c_16558, plain, (![C_2268, A_2269]: (v3_tops_2(C_2268, A_2269, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_2269), k1_relat_1('#skF_3'), C_2268), '#skF_1', A_2269) | ~v5_pre_topc(C_2268, A_2269, '#skF_1') | ~v2_funct_1(C_2268) | k2_relset_1(u1_struct_0(A_2269), k1_relat_1('#skF_3'), C_2268)!=k1_relat_1('#skF_3') | k1_relset_1(u1_struct_0(A_2269), k1_relat_1('#skF_3'), C_2268)!=k2_struct_0(A_2269) | ~m1_subset_1(C_2268, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2269), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_2268, u1_struct_0(A_2269), k1_relat_1('#skF_3')) | ~v1_funct_1(C_2268) | ~l1_pre_topc(A_2269))), inference(demodulation, [status(thm), theory('equality')], [c_5628, c_5628, c_5628, c_5628, c_5628, c_5628, c_5006])).
% 13.25/6.21  tff(c_16564, plain, (![C_2268]: (v3_tops_2(C_2268, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_2268), '#skF_1', '#skF_2') | ~v5_pre_topc(C_2268, '#skF_2', '#skF_1') | ~v2_funct_1(C_2268) | k2_relset_1(u1_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_2268)!=k1_relat_1('#skF_3') | k1_relset_1(u1_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_2268)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_2268, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_2268, u1_struct_0('#skF_2'), k1_relat_1('#skF_3')) | ~v1_funct_1(C_2268) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_16558])).
% 13.25/6.21  tff(c_17234, plain, (![C_2347]: (v3_tops_2(C_2347, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_2347), '#skF_1', '#skF_2') | ~v5_pre_topc(C_2347, '#skF_2', '#skF_1') | ~v2_funct_1(C_2347) | k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_2347)!=k1_relat_1('#skF_3') | k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), C_2347)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_2347, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3')))) | ~v1_funct_2(C_2347, k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | ~v1_funct_1(C_2347))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_90, c_90, c_90, c_90, c_16564])).
% 13.25/6.21  tff(c_17375, plain, (![A_2354]: (v3_tops_2(A_2354, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), A_2354), '#skF_1', '#skF_2') | ~v5_pre_topc(A_2354, '#skF_2', '#skF_1') | ~v2_funct_1(A_2354) | k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), A_2354)!=k1_relat_1('#skF_3') | k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), A_2354)!=k2_struct_0('#skF_2') | ~v1_funct_2(A_2354, k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | ~v1_funct_1(A_2354) | ~r1_tarski(A_2354, k2_zfmisc_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'))))), inference(resolution, [status(thm)], [c_10, c_17234])).
% 13.25/6.21  tff(c_17385, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_9199, c_17375])).
% 13.25/6.21  tff(c_17388, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3658, c_5694, c_12682, c_9175, c_9200, c_10279, c_17385])).
% 13.25/6.21  tff(c_17389, plain, (~v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_3688, c_17388])).
% 13.25/6.21  tff(c_17402, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_17389])).
% 13.25/6.21  tff(c_17405, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3729, c_17402])).
% 13.25/6.21  tff(c_17409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_5700, c_5699, c_833, c_5693, c_17405])).
% 13.25/6.21  tff(c_17410, plain, (~v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_17389])).
% 13.25/6.21  tff(c_17414, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_17410])).
% 13.25/6.21  tff(c_17417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_68, c_833, c_4944, c_17414])).
% 13.25/6.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.25/6.21  
% 13.25/6.21  Inference rules
% 13.25/6.21  ----------------------
% 13.25/6.21  #Ref     : 0
% 13.25/6.21  #Sup     : 3337
% 13.25/6.21  #Fact    : 0
% 13.25/6.21  #Define  : 0
% 13.25/6.21  #Split   : 35
% 13.25/6.21  #Chain   : 0
% 13.25/6.21  #Close   : 0
% 13.25/6.21  
% 13.25/6.21  Ordering : KBO
% 13.25/6.21  
% 13.25/6.21  Simplification rules
% 13.25/6.21  ----------------------
% 13.25/6.21  #Subsume      : 1385
% 13.25/6.21  #Demod        : 6673
% 13.25/6.21  #Tautology    : 330
% 13.25/6.21  #SimpNegUnit  : 20
% 13.25/6.21  #BackRed      : 83
% 13.25/6.21  
% 13.25/6.21  #Partial instantiations: 0
% 13.25/6.21  #Strategies tried      : 1
% 13.25/6.21  
% 13.25/6.21  Timing (in seconds)
% 13.25/6.21  ----------------------
% 13.25/6.21  Preprocessing        : 0.38
% 13.25/6.21  Parsing              : 0.19
% 13.25/6.21  CNF conversion       : 0.03
% 13.25/6.21  Main loop            : 5.03
% 13.25/6.21  Inferencing          : 1.34
% 13.25/6.21  Reduction            : 2.07
% 13.25/6.21  Demodulation         : 1.62
% 13.25/6.21  BG Simplification    : 0.13
% 13.25/6.21  Subsumption          : 1.22
% 13.25/6.21  Abstraction          : 0.20
% 13.25/6.21  MUC search           : 0.00
% 13.25/6.21  Cooper               : 0.00
% 13.25/6.21  Total                : 5.48
% 13.25/6.21  Index Insertion      : 0.00
% 13.25/6.21  Index Deletion       : 0.00
% 13.25/6.21  Index Matching       : 0.00
% 13.25/6.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
