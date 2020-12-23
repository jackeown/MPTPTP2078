%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:49 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :  195 (136552 expanded)
%              Number of leaves         :   34 (46417 expanded)
%              Depth                    :   29
%              Number of atoms          :  804 (395663 expanded)
%              Number of equality atoms :  152 (63129 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

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

tff(f_158,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
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

tff(f_97,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => v2_funct_1(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

tff(f_120,axiom,(
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

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_14,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_52,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_14,c_52])).

tff(c_65,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_64,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_57])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_66])).

tff(c_4,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_42,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_67,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_42])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_67])).

tff(c_101,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_funct_1(k2_funct_1(C_45))
      | k2_relset_1(A_46,B_47,C_45) != B_47
      | ~ v2_funct_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_2(C_45,A_46,B_47)
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_101])).

tff(c_107,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_104])).

tff(c_108,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_38,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_154,plain,(
    ! [C_60,A_61,B_62] :
      ( v2_funct_1(C_60)
      | ~ v3_tops_2(C_60,A_61,B_62)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61),u1_struct_0(B_62))))
      | ~ v1_funct_2(C_60,u1_struct_0(A_61),u1_struct_0(B_62))
      | ~ v1_funct_1(C_60)
      | ~ l1_pre_topc(B_62)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_161,plain,(
    ! [C_60,B_62] :
      ( v2_funct_1(C_60)
      | ~ v3_tops_2(C_60,'#skF_1',B_62)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_62))))
      | ~ v1_funct_2(C_60,u1_struct_0('#skF_1'),u1_struct_0(B_62))
      | ~ v1_funct_1(C_60)
      | ~ l1_pre_topc(B_62)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_154])).

tff(c_180,plain,(
    ! [C_63,B_64] :
      ( v2_funct_1(C_63)
      | ~ v3_tops_2(C_63,'#skF_1',B_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_64))))
      | ~ v1_funct_2(C_63,k2_struct_0('#skF_1'),u1_struct_0(B_64))
      | ~ v1_funct_1(C_63)
      | ~ l1_pre_topc(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_161])).

tff(c_190,plain,(
    ! [C_63] :
      ( v2_funct_1(C_63)
      | ~ v3_tops_2(C_63,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_63,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_63)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_180])).

tff(c_202,plain,(
    ! [C_66] :
      ( v2_funct_1(C_66)
      | ~ v3_tops_2(C_66,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_66,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_190])).

tff(c_209,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_202])).

tff(c_213,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_38,c_209])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_213])).

tff(c_217,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_704,plain,(
    ! [C_138,A_139,B_140] :
      ( v5_pre_topc(C_138,A_139,B_140)
      | ~ v3_tops_2(C_138,A_139,B_140)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_139),u1_struct_0(B_140))))
      | ~ v1_funct_2(C_138,u1_struct_0(A_139),u1_struct_0(B_140))
      | ~ v1_funct_1(C_138)
      | ~ l1_pre_topc(B_140)
      | ~ l1_pre_topc(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_711,plain,(
    ! [C_138,B_140] :
      ( v5_pre_topc(C_138,'#skF_1',B_140)
      | ~ v3_tops_2(C_138,'#skF_1',B_140)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_140))))
      | ~ v1_funct_2(C_138,u1_struct_0('#skF_1'),u1_struct_0(B_140))
      | ~ v1_funct_1(C_138)
      | ~ l1_pre_topc(B_140)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_704])).

tff(c_768,plain,(
    ! [C_146,B_147] :
      ( v5_pre_topc(C_146,'#skF_1',B_147)
      | ~ v3_tops_2(C_146,'#skF_1',B_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_147))))
      | ~ v1_funct_2(C_146,k2_struct_0('#skF_1'),u1_struct_0(B_147))
      | ~ v1_funct_1(C_146)
      | ~ l1_pre_topc(B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_711])).

tff(c_778,plain,(
    ! [C_146] :
      ( v5_pre_topc(C_146,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_146,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_146,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_146)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_768])).

tff(c_790,plain,(
    ! [C_149] :
      ( v5_pre_topc(C_149,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_149,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_149,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_778])).

tff(c_797,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_790])).

tff(c_801,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_38,c_797])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_funct_1(k2_funct_1(A_1)) = A_1
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_216,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_218,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_504,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(u1_struct_0(A_109),u1_struct_0(B_110),C_111) = k2_struct_0(B_110)
      | ~ v3_tops_2(C_111,A_109,B_110)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109),u1_struct_0(B_110))))
      | ~ v1_funct_2(C_111,u1_struct_0(A_109),u1_struct_0(B_110))
      | ~ v1_funct_1(C_111)
      | ~ l1_pre_topc(B_110)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_511,plain,(
    ! [B_110,C_111] :
      ( k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_110),C_111) = k2_struct_0(B_110)
      | ~ v3_tops_2(C_111,'#skF_1',B_110)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_110))))
      | ~ v1_funct_2(C_111,u1_struct_0('#skF_1'),u1_struct_0(B_110))
      | ~ v1_funct_1(C_111)
      | ~ l1_pre_topc(B_110)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_504])).

tff(c_530,plain,(
    ! [B_112,C_113] :
      ( k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_112),C_113) = k2_struct_0(B_112)
      | ~ v3_tops_2(C_113,'#skF_1',B_112)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_113,k2_struct_0('#skF_1'),u1_struct_0(B_112))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_65,c_511])).

tff(c_540,plain,(
    ! [C_113] :
      ( k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_113) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_113,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_113,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_530])).

tff(c_552,plain,(
    ! [C_115] :
      ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_115) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_115,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_115,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_64,c_540])).

tff(c_559,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_552])).

tff(c_563,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_38,c_559])).

tff(c_565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_563])).

tff(c_567,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_566,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_572,plain,(
    ! [C_116,B_117,A_118] :
      ( v1_funct_2(k2_funct_1(C_116),B_117,A_118)
      | k2_relset_1(A_118,B_117,C_116) != B_117
      | ~ v2_funct_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117)))
      | ~ v1_funct_2(C_116,A_118,B_117)
      | ~ v1_funct_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_575,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_572])).

tff(c_578,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_217,c_567,c_575])).

tff(c_579,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_tops_2(A_119,B_120,C_121) = k2_funct_1(C_121)
      | ~ v2_funct_1(C_121)
      | k2_relset_1(A_119,B_120,C_121) != B_120
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_2(C_121,A_119,B_120)
      | ~ v1_funct_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_582,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_579])).

tff(c_585,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_567,c_217,c_582])).

tff(c_1183,plain,(
    ! [A_199,B_200,C_201] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_199),u1_struct_0(B_200),C_201))
      | ~ v2_funct_1(C_201)
      | k2_relset_1(u1_struct_0(A_199),u1_struct_0(B_200),C_201) != k2_struct_0(B_200)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_199),u1_struct_0(B_200))))
      | ~ v1_funct_2(C_201,u1_struct_0(A_199),u1_struct_0(B_200))
      | ~ v1_funct_1(C_201)
      | ~ l1_struct_0(B_200)
      | ~ l1_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1190,plain,(
    ! [B_200,C_201] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_200),C_201))
      | ~ v2_funct_1(C_201)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_200),C_201) != k2_struct_0(B_200)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_200))))
      | ~ v1_funct_2(C_201,u1_struct_0('#skF_1'),u1_struct_0(B_200))
      | ~ v1_funct_1(C_201)
      | ~ l1_struct_0(B_200)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1183])).

tff(c_1201,plain,(
    ! [B_200,C_201] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_200),C_201))
      | ~ v2_funct_1(C_201)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_200),C_201) != k2_struct_0(B_200)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_200))))
      | ~ v1_funct_2(C_201,k2_struct_0('#skF_1'),u1_struct_0(B_200))
      | ~ v1_funct_1(C_201)
      | ~ l1_struct_0(B_200)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_65,c_1190])).

tff(c_1239,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1201])).

tff(c_1242,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_1239])).

tff(c_1246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1242])).

tff(c_1254,plain,(
    ! [B_209,C_210] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_209),C_210))
      | ~ v2_funct_1(C_210)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_209),C_210) != k2_struct_0(B_209)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_209))))
      | ~ v1_funct_2(C_210,k2_struct_0('#skF_1'),u1_struct_0(B_209))
      | ~ v1_funct_1(C_210)
      | ~ l1_struct_0(B_209) ) ),
    inference(splitRight,[status(thm)],[c_1201])).

tff(c_1264,plain,(
    ! [C_210] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_210))
      | ~ v2_funct_1(C_210)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_210) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_210,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_210)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1254])).

tff(c_1268,plain,(
    ! [C_210] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_210))
      | ~ v2_funct_1(C_210)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_210) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_210,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_210)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_1264])).

tff(c_1275,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1268])).

tff(c_1325,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_1275])).

tff(c_1329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1325])).

tff(c_1337,plain,(
    ! [C_215] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_215))
      | ~ v2_funct_1(C_215)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_215) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_215,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_215) ) ),
    inference(splitRight,[status(thm)],[c_1268])).

tff(c_1344,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1337])).

tff(c_1348,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_567,c_217,c_585,c_1344])).

tff(c_591,plain,(
    ! [C_122,B_123,A_124] :
      ( m1_subset_1(k2_funct_1(C_122),k1_zfmisc_1(k2_zfmisc_1(B_123,A_124)))
      | k2_relset_1(A_124,B_123,C_122) != B_123
      | ~ v2_funct_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123)))
      | ~ v1_funct_2(C_122,A_124,B_123)
      | ~ v1_funct_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_funct_1(k2_funct_1(C_7))
      | k2_relset_1(A_5,B_6,C_7) != B_6
      | ~ v2_funct_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(C_7,A_5,B_6)
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1466,plain,(
    ! [C_227,B_228,A_229] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_227)))
      | k2_relset_1(B_228,A_229,k2_funct_1(C_227)) != A_229
      | ~ v2_funct_1(k2_funct_1(C_227))
      | ~ v1_funct_2(k2_funct_1(C_227),B_228,A_229)
      | ~ v1_funct_1(k2_funct_1(C_227))
      | k2_relset_1(A_229,B_228,C_227) != B_228
      | ~ v2_funct_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_229,B_228)))
      | ~ v1_funct_2(C_227,A_229,B_228)
      | ~ v1_funct_1(C_227) ) ),
    inference(resolution,[status(thm)],[c_591,c_10])).

tff(c_1472,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1466])).

tff(c_1476,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_217,c_567,c_566,c_578,c_1348,c_1472])).

tff(c_1477,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1476])).

tff(c_1248,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1201])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1331,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1268])).

tff(c_1534,plain,(
    ! [B_234,A_235,C_236] :
      ( k2_relset_1(u1_struct_0(B_234),u1_struct_0(A_235),k2_tops_2(u1_struct_0(A_235),u1_struct_0(B_234),C_236)) = k2_struct_0(A_235)
      | ~ v2_funct_1(C_236)
      | k2_relset_1(u1_struct_0(A_235),u1_struct_0(B_234),C_236) != k2_struct_0(B_234)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235),u1_struct_0(B_234))))
      | ~ v1_funct_2(C_236,u1_struct_0(A_235),u1_struct_0(B_234))
      | ~ v1_funct_1(C_236)
      | ~ l1_struct_0(B_234)
      | v2_struct_0(B_234)
      | ~ l1_struct_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1555,plain,(
    ! [A_235,C_236] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_235),k2_tops_2(u1_struct_0(A_235),u1_struct_0('#skF_2'),C_236)) = k2_struct_0(A_235)
      | ~ v2_funct_1(C_236)
      | k2_relset_1(u1_struct_0(A_235),u1_struct_0('#skF_2'),C_236) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_236,u1_struct_0(A_235),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_236)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_235) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1534])).

tff(c_1576,plain,(
    ! [A_235,C_236] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_235),k2_tops_2(u1_struct_0(A_235),k2_struct_0('#skF_2'),C_236)) = k2_struct_0(A_235)
      | ~ v2_funct_1(C_236)
      | k2_relset_1(u1_struct_0(A_235),k2_struct_0('#skF_2'),C_236) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_236,u1_struct_0(A_235),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_236)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1331,c_64,c_64,c_64,c_64,c_1555])).

tff(c_1596,plain,(
    ! [A_240,C_241] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_240),k2_tops_2(u1_struct_0(A_240),k2_struct_0('#skF_2'),C_241)) = k2_struct_0(A_240)
      | ~ v2_funct_1(C_241)
      | k2_relset_1(u1_struct_0(A_240),k2_struct_0('#skF_2'),C_241) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_241,u1_struct_0(A_240),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_241)
      | ~ l1_struct_0(A_240) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1576])).

tff(c_1605,plain,(
    ! [C_241] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_241)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_241)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_241) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_241,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_241)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1596])).

tff(c_1625,plain,(
    ! [C_242] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_242)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_242)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_242) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_242,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_65,c_65,c_65,c_65,c_1605])).

tff(c_1634,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_1625])).

tff(c_1638,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_78,c_567,c_217,c_1634])).

tff(c_1640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1477,c_1638])).

tff(c_1642,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1476])).

tff(c_8,plain,(
    ! [C_7,B_6,A_5] :
      ( v1_funct_2(k2_funct_1(C_7),B_6,A_5)
      | k2_relset_1(A_5,B_6,C_7) != B_6
      | ~ v2_funct_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(C_7,A_5,B_6)
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_608,plain,(
    ! [C_122,A_124,B_123] :
      ( v1_funct_2(k2_funct_1(k2_funct_1(C_122)),A_124,B_123)
      | k2_relset_1(B_123,A_124,k2_funct_1(C_122)) != A_124
      | ~ v2_funct_1(k2_funct_1(C_122))
      | ~ v1_funct_2(k2_funct_1(C_122),B_123,A_124)
      | ~ v1_funct_1(k2_funct_1(C_122))
      | k2_relset_1(A_124,B_123,C_122) != B_123
      | ~ v2_funct_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_124,B_123)))
      | ~ v1_funct_2(C_122,A_124,B_123)
      | ~ v1_funct_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_591,c_8])).

tff(c_36,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_83,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_36])).

tff(c_586,plain,(
    ~ v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_83])).

tff(c_1641,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1476])).

tff(c_6,plain,(
    ! [C_7,B_6,A_5] :
      ( m1_subset_1(k2_funct_1(C_7),k1_zfmisc_1(k2_zfmisc_1(B_6,A_5)))
      | k2_relset_1(A_5,B_6,C_7) != B_6
      | ~ v2_funct_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(C_7,A_5,B_6)
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3040,plain,(
    ! [C_347,A_348,B_349] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(C_347))))
      | k2_relset_1(A_348,B_349,k2_funct_1(k2_funct_1(C_347))) != B_349
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(C_347)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(C_347)),A_348,B_349)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(C_347)))
      | k2_relset_1(B_349,A_348,k2_funct_1(C_347)) != A_348
      | ~ v2_funct_1(k2_funct_1(C_347))
      | ~ v1_funct_2(k2_funct_1(C_347),B_349,A_348)
      | ~ v1_funct_1(k2_funct_1(C_347))
      | k2_relset_1(A_348,B_349,C_347) != B_349
      | ~ v2_funct_1(C_347)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_348,B_349)))
      | ~ v1_funct_2(C_347,A_348,B_349)
      | ~ v1_funct_1(C_347) ) ),
    inference(resolution,[status(thm)],[c_6,c_1466])).

tff(c_3261,plain,(
    ! [C_378,A_379,B_380] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(C_378))))
      | k2_relset_1(A_379,B_380,k2_funct_1(k2_funct_1(C_378))) != B_380
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(C_378)))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(C_378)))
      | k2_relset_1(B_380,A_379,k2_funct_1(C_378)) != A_379
      | ~ v2_funct_1(k2_funct_1(C_378))
      | ~ v1_funct_2(k2_funct_1(C_378),B_380,A_379)
      | ~ v1_funct_1(k2_funct_1(C_378))
      | k2_relset_1(A_379,B_380,C_378) != B_380
      | ~ v2_funct_1(C_378)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_379,B_380)))
      | ~ v1_funct_2(C_378,A_379,B_380)
      | ~ v1_funct_1(C_378) ) ),
    inference(resolution,[status(thm)],[c_608,c_3040])).

tff(c_3267,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3261])).

tff(c_3272,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_217,c_567,c_566,c_578,c_1348,c_1642,c_1641,c_3267])).

tff(c_3273,plain,(
    ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3272])).

tff(c_3276,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3273])).

tff(c_3279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_44,c_217,c_217,c_3276])).

tff(c_3280,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2')
    | v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_3272])).

tff(c_3319,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3280])).

tff(c_3322,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3319])).

tff(c_3325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_44,c_217,c_567,c_3322])).

tff(c_3327,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3280])).

tff(c_1415,plain,(
    ! [B_224,A_225,C_226] :
      ( k1_relset_1(u1_struct_0(B_224),u1_struct_0(A_225),k2_tops_2(u1_struct_0(A_225),u1_struct_0(B_224),C_226)) = k2_struct_0(B_224)
      | ~ v2_funct_1(C_226)
      | k2_relset_1(u1_struct_0(A_225),u1_struct_0(B_224),C_226) != k2_struct_0(B_224)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225),u1_struct_0(B_224))))
      | ~ v1_funct_2(C_226,u1_struct_0(A_225),u1_struct_0(B_224))
      | ~ v1_funct_1(C_226)
      | ~ l1_struct_0(B_224)
      | v2_struct_0(B_224)
      | ~ l1_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1436,plain,(
    ! [A_225,C_226] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_225),k2_tops_2(u1_struct_0(A_225),u1_struct_0('#skF_2'),C_226)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_226)
      | k2_relset_1(u1_struct_0(A_225),u1_struct_0('#skF_2'),C_226) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_226,u1_struct_0(A_225),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_226)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1415])).

tff(c_1457,plain,(
    ! [A_225,C_226] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_225),k2_tops_2(u1_struct_0(A_225),k2_struct_0('#skF_2'),C_226)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_226)
      | k2_relset_1(u1_struct_0(A_225),k2_struct_0('#skF_2'),C_226) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_226,u1_struct_0(A_225),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_226)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1331,c_64,c_64,c_64,c_64,c_1436])).

tff(c_1719,plain,(
    ! [A_249,C_250] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_249),k2_tops_2(u1_struct_0(A_249),k2_struct_0('#skF_2'),C_250)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_250)
      | k2_relset_1(u1_struct_0(A_249),k2_struct_0('#skF_2'),C_250) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_250,u1_struct_0(A_249),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_250)
      | ~ l1_struct_0(A_249) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1457])).

tff(c_1728,plain,(
    ! [C_250] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_250)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_250)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_250) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_250,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_250)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1719])).

tff(c_1748,plain,(
    ! [C_251] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_251)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_251)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_251) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_251,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1248,c_65,c_65,c_65,c_65,c_1728])).

tff(c_1757,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_1748])).

tff(c_1761,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_78,c_567,c_217,c_1757])).

tff(c_1074,plain,(
    ! [A_184,B_185,C_186] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_184),u1_struct_0(B_185),C_186),B_185,A_184)
      | ~ v3_tops_2(C_186,A_184,B_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_184),u1_struct_0(B_185))))
      | ~ v1_funct_2(C_186,u1_struct_0(A_184),u1_struct_0(B_185))
      | ~ v1_funct_1(C_186)
      | ~ l1_pre_topc(B_185)
      | ~ l1_pre_topc(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1079,plain,(
    ! [B_185,C_186] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_185),C_186),B_185,'#skF_1')
      | ~ v3_tops_2(C_186,'#skF_1',B_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_185))))
      | ~ v1_funct_2(C_186,u1_struct_0('#skF_1'),u1_struct_0(B_185))
      | ~ v1_funct_1(C_186)
      | ~ l1_pre_topc(B_185)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1074])).

tff(c_1127,plain,(
    ! [B_191,C_192] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_191),C_192),B_191,'#skF_1')
      | ~ v3_tops_2(C_192,'#skF_1',B_191)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_191))))
      | ~ v1_funct_2(C_192,k2_struct_0('#skF_1'),u1_struct_0(B_191))
      | ~ v1_funct_1(C_192)
      | ~ l1_pre_topc(B_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_65,c_1079])).

tff(c_1134,plain,(
    ! [C_192] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_192),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_192,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_192,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_192)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1127])).

tff(c_1146,plain,(
    ! [C_194] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_194),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_194,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_194,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_64,c_1134])).

tff(c_1153,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1146])).

tff(c_1157,plain,(
    v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_38,c_585,c_1153])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_tops_2(A_10,B_11,C_12) = k2_funct_1(C_12)
      | ~ v2_funct_1(C_12)
      | k2_relset_1(A_10,B_11,C_12) != B_11
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_2(C_12,A_10,B_11)
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1884,plain,(
    ! [B_265,A_266,C_267] :
      ( k2_tops_2(B_265,A_266,k2_funct_1(C_267)) = k2_funct_1(k2_funct_1(C_267))
      | ~ v2_funct_1(k2_funct_1(C_267))
      | k2_relset_1(B_265,A_266,k2_funct_1(C_267)) != A_266
      | ~ v1_funct_2(k2_funct_1(C_267),B_265,A_266)
      | ~ v1_funct_1(k2_funct_1(C_267))
      | k2_relset_1(A_266,B_265,C_267) != B_265
      | ~ v2_funct_1(C_267)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_266,B_265)))
      | ~ v1_funct_2(C_267,A_266,B_265)
      | ~ v1_funct_1(C_267) ) ),
    inference(resolution,[status(thm)],[c_591,c_16])).

tff(c_1890,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1884])).

tff(c_1894,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_217,c_567,c_566,c_578,c_1642,c_1348,c_1890])).

tff(c_611,plain,(
    ! [C_125,A_126,B_127] :
      ( v1_relat_1(k2_funct_1(C_125))
      | k2_relset_1(A_126,B_127,C_125) != B_127
      | ~ v2_funct_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_2(C_125,A_126,B_127)
      | ~ v1_funct_1(C_125) ) ),
    inference(resolution,[status(thm)],[c_591,c_4])).

tff(c_1652,plain,(
    ! [C_243,B_244,A_245] :
      ( v1_relat_1(k2_funct_1(k2_funct_1(C_243)))
      | k2_relset_1(B_244,A_245,k2_funct_1(C_243)) != A_245
      | ~ v2_funct_1(k2_funct_1(C_243))
      | ~ v1_funct_2(k2_funct_1(C_243),B_244,A_245)
      | ~ v1_funct_1(k2_funct_1(C_243))
      | k2_relset_1(A_245,B_244,C_243) != B_244
      | ~ v2_funct_1(C_243)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_245,B_244)))
      | ~ v1_funct_2(C_243,A_245,B_244)
      | ~ v1_funct_1(C_243) ) ),
    inference(resolution,[status(thm)],[c_6,c_611])).

tff(c_1658,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1652])).

tff(c_1662,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_217,c_567,c_566,c_578,c_1348,c_1642,c_1658])).

tff(c_3281,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3272])).

tff(c_617,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_611])).

tff(c_621,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_217,c_567,c_617])).

tff(c_3085,plain,(
    ! [A_356,B_357,C_358] :
      ( k2_tops_2(A_356,B_357,k2_funct_1(k2_funct_1(C_358))) = k2_funct_1(k2_funct_1(k2_funct_1(C_358)))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(C_358)))
      | k2_relset_1(A_356,B_357,k2_funct_1(k2_funct_1(C_358))) != B_357
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(C_358)),A_356,B_357)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(C_358)))
      | k2_relset_1(B_357,A_356,k2_funct_1(C_358)) != A_356
      | ~ v2_funct_1(k2_funct_1(C_358))
      | ~ v1_funct_2(k2_funct_1(C_358),B_357,A_356)
      | ~ v1_funct_1(k2_funct_1(C_358))
      | k2_relset_1(A_356,B_357,C_358) != B_357
      | ~ v2_funct_1(C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357)))
      | ~ v1_funct_2(C_358,A_356,B_357)
      | ~ v1_funct_1(C_358) ) ),
    inference(resolution,[status(thm)],[c_6,c_1884])).

tff(c_3551,plain,(
    ! [A_409,B_410,C_411] :
      ( k2_tops_2(A_409,B_410,k2_funct_1(k2_funct_1(C_411))) = k2_funct_1(k2_funct_1(k2_funct_1(C_411)))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(C_411)))
      | k2_relset_1(A_409,B_410,k2_funct_1(k2_funct_1(C_411))) != B_410
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(C_411)))
      | k2_relset_1(B_410,A_409,k2_funct_1(C_411)) != A_409
      | ~ v2_funct_1(k2_funct_1(C_411))
      | ~ v1_funct_2(k2_funct_1(C_411),B_410,A_409)
      | ~ v1_funct_1(k2_funct_1(C_411))
      | k2_relset_1(A_409,B_410,C_411) != B_410
      | ~ v2_funct_1(C_411)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_409,B_410)))
      | ~ v1_funct_2(C_411,A_409,B_410)
      | ~ v1_funct_1(C_411) ) ),
    inference(resolution,[status(thm)],[c_608,c_3085])).

tff(c_3560,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3551])).

tff(c_3565,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_217,c_567,c_566,c_578,c_1348,c_1642,c_1641,c_3327,c_3281,c_3560])).

tff(c_3598,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3565])).

tff(c_3608,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_44,c_217,c_585,c_3598])).

tff(c_1231,plain,(
    ! [A_206,B_207,A_208] :
      ( m1_subset_1(A_206,k1_zfmisc_1(k2_zfmisc_1(B_207,A_208)))
      | k2_relset_1(A_208,B_207,k2_funct_1(A_206)) != B_207
      | ~ v2_funct_1(k2_funct_1(A_206))
      | ~ m1_subset_1(k2_funct_1(A_206),k1_zfmisc_1(k2_zfmisc_1(A_208,B_207)))
      | ~ v1_funct_2(k2_funct_1(A_206),A_208,B_207)
      | ~ v1_funct_1(k2_funct_1(A_206))
      | ~ v2_funct_1(A_206)
      | ~ v1_funct_1(A_206)
      | ~ v1_relat_1(A_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_591])).

tff(c_1237,plain,(
    ! [A_1,B_207,A_208] :
      ( m1_subset_1(k2_funct_1(A_1),k1_zfmisc_1(k2_zfmisc_1(B_207,A_208)))
      | k2_relset_1(A_208,B_207,k2_funct_1(k2_funct_1(A_1))) != B_207
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(A_1)))
      | ~ m1_subset_1(A_1,k1_zfmisc_1(k2_zfmisc_1(A_208,B_207)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(A_1)),A_208,B_207)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(A_1)))
      | ~ v2_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(k2_funct_1(A_1))
      | ~ v1_relat_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1231])).

tff(c_3678,plain,(
    ! [B_207,A_208] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_207,A_208)))
      | k2_relset_1(A_208,B_207,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) != B_207
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))
      | ~ m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_208,B_207)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))),A_208,B_207)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3608,c_1237])).

tff(c_4653,plain,(
    ! [B_421,A_422] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_421,A_422)))
      | k2_relset_1(A_422,B_421,k2_funct_1(k2_funct_1('#skF_3'))) != B_421
      | ~ m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_422,B_421)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_422,B_421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_1641,c_3281,c_621,c_3608,c_566,c_3608,c_1348,c_3608,c_1641,c_3608,c_3608,c_3281,c_3608,c_3608,c_3678])).

tff(c_4667,plain,(
    ! [B_421,A_422] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_421,A_422)))
      | k2_relset_1(A_422,B_421,k2_funct_1(k2_funct_1('#skF_3'))) != B_421
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_422,B_421)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_422,B_421)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4653])).

tff(c_4677,plain,(
    ! [B_423,A_424] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(B_423,A_424)))
      | k2_relset_1(A_424,B_423,k2_funct_1(k2_funct_1('#skF_3'))) != B_423
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_424,B_423)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),A_424,B_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_44,c_217,c_4667])).

tff(c_1818,plain,(
    ! [C_256,A_257,B_258] :
      ( v3_tops_2(C_256,A_257,B_258)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_257),u1_struct_0(B_258),C_256),B_258,A_257)
      | ~ v5_pre_topc(C_256,A_257,B_258)
      | ~ v2_funct_1(C_256)
      | k2_relset_1(u1_struct_0(A_257),u1_struct_0(B_258),C_256) != k2_struct_0(B_258)
      | k1_relset_1(u1_struct_0(A_257),u1_struct_0(B_258),C_256) != k2_struct_0(A_257)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_257),u1_struct_0(B_258))))
      | ~ v1_funct_2(C_256,u1_struct_0(A_257),u1_struct_0(B_258))
      | ~ v1_funct_1(C_256)
      | ~ l1_pre_topc(B_258)
      | ~ l1_pre_topc(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1824,plain,(
    ! [C_256,B_258] :
      ( v3_tops_2(C_256,'#skF_2',B_258)
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0(B_258),C_256),B_258,'#skF_2')
      | ~ v5_pre_topc(C_256,'#skF_2',B_258)
      | ~ v2_funct_1(C_256)
      | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_258),C_256) != k2_struct_0(B_258)
      | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_258),C_256) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_258))))
      | ~ v1_funct_2(C_256,u1_struct_0('#skF_2'),u1_struct_0(B_258))
      | ~ v1_funct_1(C_256)
      | ~ l1_pre_topc(B_258)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1818])).

tff(c_3076,plain,(
    ! [C_354,B_355] :
      ( v3_tops_2(C_354,'#skF_2',B_355)
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),u1_struct_0(B_355),C_354),B_355,'#skF_2')
      | ~ v5_pre_topc(C_354,'#skF_2',B_355)
      | ~ v2_funct_1(C_354)
      | k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(B_355),C_354) != k2_struct_0(B_355)
      | k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(B_355),C_354) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0(B_355))))
      | ~ v1_funct_2(C_354,k2_struct_0('#skF_2'),u1_struct_0(B_355))
      | ~ v1_funct_1(C_354)
      | ~ l1_pre_topc(B_355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_64,c_64,c_64,c_1824])).

tff(c_3078,plain,(
    ! [C_354] :
      ( v3_tops_2(C_354,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_354),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_354,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_354)
      | k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),C_354) != k2_struct_0('#skF_1')
      | k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'),C_354) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_354,k2_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_354)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_3076])).

tff(c_3082,plain,(
    ! [C_354] :
      ( v3_tops_2(C_354,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_354),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_354,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_354)
      | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_354) != k2_struct_0('#skF_1')
      | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_354) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_354,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_354,k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_65,c_65,c_65,c_3078])).

tff(c_4739,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4677,c_3082])).

tff(c_5174,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3327,c_566,c_578,c_1761,c_1642,c_1348,c_1157,c_1894,c_4739])).

tff(c_5175,plain,
    ( ~ v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_5174])).

tff(c_5475,plain,(
    ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5175])).

tff(c_5511,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_608,c_5475])).

tff(c_5518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_78,c_217,c_567,c_566,c_578,c_1348,c_1642,c_5511])).

tff(c_5519,plain,(
    ~ v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_5175])).

tff(c_5523,plain,
    ( ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5519])).

tff(c_5526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_44,c_217,c_801,c_5523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:49:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.84/2.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/2.80  
% 7.84/2.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/2.80  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 7.84/2.80  
% 7.84/2.80  %Foreground sorts:
% 7.84/2.80  
% 7.84/2.80  
% 7.84/2.80  %Background operators:
% 7.84/2.80  
% 7.84/2.80  
% 7.84/2.80  %Foreground operators:
% 7.84/2.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.84/2.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.84/2.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.84/2.80  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.84/2.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.84/2.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.84/2.80  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 7.84/2.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.84/2.80  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 7.84/2.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.84/2.80  tff('#skF_2', type, '#skF_2': $i).
% 7.84/2.80  tff('#skF_3', type, '#skF_3': $i).
% 7.84/2.80  tff('#skF_1', type, '#skF_1': $i).
% 7.84/2.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.84/2.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.84/2.80  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.84/2.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.84/2.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.84/2.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.84/2.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.84/2.80  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.84/2.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.84/2.80  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.84/2.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.84/2.80  
% 8.04/2.84  tff(f_158, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_tops_2)).
% 8.04/2.84  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.04/2.84  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 8.04/2.84  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.04/2.84  tff(f_53, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.04/2.84  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_2)).
% 8.04/2.84  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 8.04/2.84  tff(f_73, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 8.04/2.84  tff(f_138, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_tops_2)).
% 8.04/2.84  tff(f_120, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 8.04/2.84  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.04/2.84  tff(c_14, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.04/2.84  tff(c_52, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.04/2.84  tff(c_57, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_14, c_52])).
% 8.04/2.84  tff(c_65, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_57])).
% 8.04/2.84  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.04/2.84  tff(c_64, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_57])).
% 8.04/2.84  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.04/2.84  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_40])).
% 8.04/2.84  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_66])).
% 8.04/2.84  tff(c_4, plain, (![C_4, A_2, B_3]: (v1_relat_1(C_4) | ~m1_subset_1(C_4, k1_zfmisc_1(k2_zfmisc_1(A_2, B_3))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.04/2.84  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_4])).
% 8.04/2.84  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.04/2.84  tff(c_42, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.04/2.84  tff(c_67, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_42])).
% 8.04/2.84  tff(c_76, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_67])).
% 8.04/2.84  tff(c_101, plain, (![C_45, A_46, B_47]: (v1_funct_1(k2_funct_1(C_45)) | k2_relset_1(A_46, B_47, C_45)!=B_47 | ~v2_funct_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_2(C_45, A_46, B_47) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.04/2.84  tff(c_104, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_101])).
% 8.04/2.84  tff(c_107, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_104])).
% 8.04/2.84  tff(c_108, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_107])).
% 8.04/2.84  tff(c_38, plain, (v3_tops_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.04/2.84  tff(c_154, plain, (![C_60, A_61, B_62]: (v2_funct_1(C_60) | ~v3_tops_2(C_60, A_61, B_62) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_61), u1_struct_0(B_62)))) | ~v1_funct_2(C_60, u1_struct_0(A_61), u1_struct_0(B_62)) | ~v1_funct_1(C_60) | ~l1_pre_topc(B_62) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.04/2.84  tff(c_161, plain, (![C_60, B_62]: (v2_funct_1(C_60) | ~v3_tops_2(C_60, '#skF_1', B_62) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_62)))) | ~v1_funct_2(C_60, u1_struct_0('#skF_1'), u1_struct_0(B_62)) | ~v1_funct_1(C_60) | ~l1_pre_topc(B_62) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_154])).
% 8.04/2.84  tff(c_180, plain, (![C_63, B_64]: (v2_funct_1(C_63) | ~v3_tops_2(C_63, '#skF_1', B_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_64)))) | ~v1_funct_2(C_63, k2_struct_0('#skF_1'), u1_struct_0(B_64)) | ~v1_funct_1(C_63) | ~l1_pre_topc(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_161])).
% 8.04/2.84  tff(c_190, plain, (![C_63]: (v2_funct_1(C_63) | ~v3_tops_2(C_63, '#skF_1', '#skF_2') | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_63, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_63) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_180])).
% 8.04/2.84  tff(c_202, plain, (![C_66]: (v2_funct_1(C_66) | ~v3_tops_2(C_66, '#skF_1', '#skF_2') | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_66, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_66))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_190])).
% 8.04/2.84  tff(c_209, plain, (v2_funct_1('#skF_3') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_202])).
% 8.04/2.84  tff(c_213, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_38, c_209])).
% 8.04/2.84  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_213])).
% 8.04/2.84  tff(c_217, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_107])).
% 8.04/2.84  tff(c_704, plain, (![C_138, A_139, B_140]: (v5_pre_topc(C_138, A_139, B_140) | ~v3_tops_2(C_138, A_139, B_140) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_139), u1_struct_0(B_140)))) | ~v1_funct_2(C_138, u1_struct_0(A_139), u1_struct_0(B_140)) | ~v1_funct_1(C_138) | ~l1_pre_topc(B_140) | ~l1_pre_topc(A_139))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.04/2.84  tff(c_711, plain, (![C_138, B_140]: (v5_pre_topc(C_138, '#skF_1', B_140) | ~v3_tops_2(C_138, '#skF_1', B_140) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_140)))) | ~v1_funct_2(C_138, u1_struct_0('#skF_1'), u1_struct_0(B_140)) | ~v1_funct_1(C_138) | ~l1_pre_topc(B_140) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_704])).
% 8.04/2.84  tff(c_768, plain, (![C_146, B_147]: (v5_pre_topc(C_146, '#skF_1', B_147) | ~v3_tops_2(C_146, '#skF_1', B_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_147)))) | ~v1_funct_2(C_146, k2_struct_0('#skF_1'), u1_struct_0(B_147)) | ~v1_funct_1(C_146) | ~l1_pre_topc(B_147))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_711])).
% 8.04/2.84  tff(c_778, plain, (![C_146]: (v5_pre_topc(C_146, '#skF_1', '#skF_2') | ~v3_tops_2(C_146, '#skF_1', '#skF_2') | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_146, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_146) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_768])).
% 8.04/2.84  tff(c_790, plain, (![C_149]: (v5_pre_topc(C_149, '#skF_1', '#skF_2') | ~v3_tops_2(C_149, '#skF_1', '#skF_2') | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_149, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_149))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_778])).
% 8.04/2.84  tff(c_797, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_790])).
% 8.04/2.84  tff(c_801, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_38, c_797])).
% 8.04/2.84  tff(c_2, plain, (![A_1]: (k2_funct_1(k2_funct_1(A_1))=A_1 | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.04/2.84  tff(c_216, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_107])).
% 8.04/2.84  tff(c_218, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_216])).
% 8.04/2.84  tff(c_504, plain, (![A_109, B_110, C_111]: (k2_relset_1(u1_struct_0(A_109), u1_struct_0(B_110), C_111)=k2_struct_0(B_110) | ~v3_tops_2(C_111, A_109, B_110) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_109), u1_struct_0(B_110)))) | ~v1_funct_2(C_111, u1_struct_0(A_109), u1_struct_0(B_110)) | ~v1_funct_1(C_111) | ~l1_pre_topc(B_110) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.04/2.84  tff(c_511, plain, (![B_110, C_111]: (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_110), C_111)=k2_struct_0(B_110) | ~v3_tops_2(C_111, '#skF_1', B_110) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_110)))) | ~v1_funct_2(C_111, u1_struct_0('#skF_1'), u1_struct_0(B_110)) | ~v1_funct_1(C_111) | ~l1_pre_topc(B_110) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_504])).
% 8.04/2.84  tff(c_530, plain, (![B_112, C_113]: (k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_112), C_113)=k2_struct_0(B_112) | ~v3_tops_2(C_113, '#skF_1', B_112) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_112)))) | ~v1_funct_2(C_113, k2_struct_0('#skF_1'), u1_struct_0(B_112)) | ~v1_funct_1(C_113) | ~l1_pre_topc(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_65, c_511])).
% 8.04/2.84  tff(c_540, plain, (![C_113]: (k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_113)=k2_struct_0('#skF_2') | ~v3_tops_2(C_113, '#skF_1', '#skF_2') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_113, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_113) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_530])).
% 8.04/2.84  tff(c_552, plain, (![C_115]: (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_115)=k2_struct_0('#skF_2') | ~v3_tops_2(C_115, '#skF_1', '#skF_2') | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_115, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_115))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_64, c_540])).
% 8.04/2.84  tff(c_559, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_552])).
% 8.04/2.84  tff(c_563, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_38, c_559])).
% 8.04/2.84  tff(c_565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_563])).
% 8.04/2.84  tff(c_567, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_216])).
% 8.04/2.84  tff(c_566, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_216])).
% 8.04/2.84  tff(c_572, plain, (![C_116, B_117, A_118]: (v1_funct_2(k2_funct_1(C_116), B_117, A_118) | k2_relset_1(A_118, B_117, C_116)!=B_117 | ~v2_funct_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))) | ~v1_funct_2(C_116, A_118, B_117) | ~v1_funct_1(C_116))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.04/2.84  tff(c_575, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_572])).
% 8.04/2.84  tff(c_578, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_217, c_567, c_575])).
% 8.04/2.84  tff(c_579, plain, (![A_119, B_120, C_121]: (k2_tops_2(A_119, B_120, C_121)=k2_funct_1(C_121) | ~v2_funct_1(C_121) | k2_relset_1(A_119, B_120, C_121)!=B_120 | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_2(C_121, A_119, B_120) | ~v1_funct_1(C_121))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.04/2.84  tff(c_582, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_579])).
% 8.04/2.84  tff(c_585, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_567, c_217, c_582])).
% 8.04/2.84  tff(c_1183, plain, (![A_199, B_200, C_201]: (v2_funct_1(k2_tops_2(u1_struct_0(A_199), u1_struct_0(B_200), C_201)) | ~v2_funct_1(C_201) | k2_relset_1(u1_struct_0(A_199), u1_struct_0(B_200), C_201)!=k2_struct_0(B_200) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_199), u1_struct_0(B_200)))) | ~v1_funct_2(C_201, u1_struct_0(A_199), u1_struct_0(B_200)) | ~v1_funct_1(C_201) | ~l1_struct_0(B_200) | ~l1_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.04/2.84  tff(c_1190, plain, (![B_200, C_201]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_200), C_201)) | ~v2_funct_1(C_201) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_200), C_201)!=k2_struct_0(B_200) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_200)))) | ~v1_funct_2(C_201, u1_struct_0('#skF_1'), u1_struct_0(B_200)) | ~v1_funct_1(C_201) | ~l1_struct_0(B_200) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1183])).
% 8.04/2.84  tff(c_1201, plain, (![B_200, C_201]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_200), C_201)) | ~v2_funct_1(C_201) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_200), C_201)!=k2_struct_0(B_200) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_200)))) | ~v1_funct_2(C_201, k2_struct_0('#skF_1'), u1_struct_0(B_200)) | ~v1_funct_1(C_201) | ~l1_struct_0(B_200) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_65, c_1190])).
% 8.04/2.84  tff(c_1239, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1201])).
% 8.04/2.84  tff(c_1242, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_1239])).
% 8.04/2.84  tff(c_1246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1242])).
% 8.04/2.84  tff(c_1254, plain, (![B_209, C_210]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_209), C_210)) | ~v2_funct_1(C_210) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_209), C_210)!=k2_struct_0(B_209) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_209)))) | ~v1_funct_2(C_210, k2_struct_0('#skF_1'), u1_struct_0(B_209)) | ~v1_funct_1(C_210) | ~l1_struct_0(B_209))), inference(splitRight, [status(thm)], [c_1201])).
% 8.04/2.84  tff(c_1264, plain, (![C_210]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_210)) | ~v2_funct_1(C_210) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_210)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_210, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_210) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1254])).
% 8.04/2.84  tff(c_1268, plain, (![C_210]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_210)) | ~v2_funct_1(C_210) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_210)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_210, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_210) | ~l1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_1264])).
% 8.04/2.84  tff(c_1275, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1268])).
% 8.04/2.84  tff(c_1325, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_1275])).
% 8.04/2.84  tff(c_1329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1325])).
% 8.04/2.84  tff(c_1337, plain, (![C_215]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_215)) | ~v2_funct_1(C_215) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_215)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_215, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_215))), inference(splitRight, [status(thm)], [c_1268])).
% 8.04/2.84  tff(c_1344, plain, (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1337])).
% 8.04/2.84  tff(c_1348, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_567, c_217, c_585, c_1344])).
% 8.04/2.84  tff(c_591, plain, (![C_122, B_123, A_124]: (m1_subset_1(k2_funct_1(C_122), k1_zfmisc_1(k2_zfmisc_1(B_123, A_124))) | k2_relset_1(A_124, B_123, C_122)!=B_123 | ~v2_funct_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))) | ~v1_funct_2(C_122, A_124, B_123) | ~v1_funct_1(C_122))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.04/2.84  tff(c_10, plain, (![C_7, A_5, B_6]: (v1_funct_1(k2_funct_1(C_7)) | k2_relset_1(A_5, B_6, C_7)!=B_6 | ~v2_funct_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(C_7, A_5, B_6) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.04/2.84  tff(c_1466, plain, (![C_227, B_228, A_229]: (v1_funct_1(k2_funct_1(k2_funct_1(C_227))) | k2_relset_1(B_228, A_229, k2_funct_1(C_227))!=A_229 | ~v2_funct_1(k2_funct_1(C_227)) | ~v1_funct_2(k2_funct_1(C_227), B_228, A_229) | ~v1_funct_1(k2_funct_1(C_227)) | k2_relset_1(A_229, B_228, C_227)!=B_228 | ~v2_funct_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_229, B_228))) | ~v1_funct_2(C_227, A_229, B_228) | ~v1_funct_1(C_227))), inference(resolution, [status(thm)], [c_591, c_10])).
% 8.04/2.84  tff(c_1472, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1466])).
% 8.04/2.84  tff(c_1476, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_217, c_567, c_566, c_578, c_1348, c_1472])).
% 8.04/2.84  tff(c_1477, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1476])).
% 8.04/2.84  tff(c_1248, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1201])).
% 8.04/2.84  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.04/2.84  tff(c_1331, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1268])).
% 8.04/2.84  tff(c_1534, plain, (![B_234, A_235, C_236]: (k2_relset_1(u1_struct_0(B_234), u1_struct_0(A_235), k2_tops_2(u1_struct_0(A_235), u1_struct_0(B_234), C_236))=k2_struct_0(A_235) | ~v2_funct_1(C_236) | k2_relset_1(u1_struct_0(A_235), u1_struct_0(B_234), C_236)!=k2_struct_0(B_234) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235), u1_struct_0(B_234)))) | ~v1_funct_2(C_236, u1_struct_0(A_235), u1_struct_0(B_234)) | ~v1_funct_1(C_236) | ~l1_struct_0(B_234) | v2_struct_0(B_234) | ~l1_struct_0(A_235))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.04/2.84  tff(c_1555, plain, (![A_235, C_236]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_235), k2_tops_2(u1_struct_0(A_235), u1_struct_0('#skF_2'), C_236))=k2_struct_0(A_235) | ~v2_funct_1(C_236) | k2_relset_1(u1_struct_0(A_235), u1_struct_0('#skF_2'), C_236)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_236, u1_struct_0(A_235), u1_struct_0('#skF_2')) | ~v1_funct_1(C_236) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_235))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1534])).
% 8.04/2.84  tff(c_1576, plain, (![A_235, C_236]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_235), k2_tops_2(u1_struct_0(A_235), k2_struct_0('#skF_2'), C_236))=k2_struct_0(A_235) | ~v2_funct_1(C_236) | k2_relset_1(u1_struct_0(A_235), k2_struct_0('#skF_2'), C_236)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_236, u1_struct_0(A_235), k2_struct_0('#skF_2')) | ~v1_funct_1(C_236) | v2_struct_0('#skF_2') | ~l1_struct_0(A_235))), inference(demodulation, [status(thm), theory('equality')], [c_1331, c_64, c_64, c_64, c_64, c_1555])).
% 8.04/2.84  tff(c_1596, plain, (![A_240, C_241]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_240), k2_tops_2(u1_struct_0(A_240), k2_struct_0('#skF_2'), C_241))=k2_struct_0(A_240) | ~v2_funct_1(C_241) | k2_relset_1(u1_struct_0(A_240), k2_struct_0('#skF_2'), C_241)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_241, u1_struct_0(A_240), k2_struct_0('#skF_2')) | ~v1_funct_1(C_241) | ~l1_struct_0(A_240))), inference(negUnitSimplification, [status(thm)], [c_48, c_1576])).
% 8.04/2.84  tff(c_1605, plain, (![C_241]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_241))=k2_struct_0('#skF_1') | ~v2_funct_1(C_241) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_241)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_241, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_241) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1596])).
% 8.04/2.84  tff(c_1625, plain, (![C_242]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_242))=k2_struct_0('#skF_1') | ~v2_funct_1(C_242) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_242)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_242, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_242))), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_65, c_65, c_65, c_65, c_1605])).
% 8.04/2.84  tff(c_1634, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_585, c_1625])).
% 8.04/2.84  tff(c_1638, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_78, c_567, c_217, c_1634])).
% 8.04/2.84  tff(c_1640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1477, c_1638])).
% 8.04/2.84  tff(c_1642, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1476])).
% 8.04/2.84  tff(c_8, plain, (![C_7, B_6, A_5]: (v1_funct_2(k2_funct_1(C_7), B_6, A_5) | k2_relset_1(A_5, B_6, C_7)!=B_6 | ~v2_funct_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(C_7, A_5, B_6) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.04/2.84  tff(c_608, plain, (![C_122, A_124, B_123]: (v1_funct_2(k2_funct_1(k2_funct_1(C_122)), A_124, B_123) | k2_relset_1(B_123, A_124, k2_funct_1(C_122))!=A_124 | ~v2_funct_1(k2_funct_1(C_122)) | ~v1_funct_2(k2_funct_1(C_122), B_123, A_124) | ~v1_funct_1(k2_funct_1(C_122)) | k2_relset_1(A_124, B_123, C_122)!=B_123 | ~v2_funct_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_124, B_123))) | ~v1_funct_2(C_122, A_124, B_123) | ~v1_funct_1(C_122))), inference(resolution, [status(thm)], [c_591, c_8])).
% 8.04/2.84  tff(c_36, plain, (~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.04/2.84  tff(c_83, plain, (~v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_36])).
% 8.04/2.84  tff(c_586, plain, (~v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_585, c_83])).
% 8.04/2.84  tff(c_1641, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1476])).
% 8.04/2.84  tff(c_6, plain, (![C_7, B_6, A_5]: (m1_subset_1(k2_funct_1(C_7), k1_zfmisc_1(k2_zfmisc_1(B_6, A_5))) | k2_relset_1(A_5, B_6, C_7)!=B_6 | ~v2_funct_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(C_7, A_5, B_6) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.04/2.84  tff(c_3040, plain, (![C_347, A_348, B_349]: (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(C_347)))) | k2_relset_1(A_348, B_349, k2_funct_1(k2_funct_1(C_347)))!=B_349 | ~v2_funct_1(k2_funct_1(k2_funct_1(C_347))) | ~v1_funct_2(k2_funct_1(k2_funct_1(C_347)), A_348, B_349) | ~v1_funct_1(k2_funct_1(k2_funct_1(C_347))) | k2_relset_1(B_349, A_348, k2_funct_1(C_347))!=A_348 | ~v2_funct_1(k2_funct_1(C_347)) | ~v1_funct_2(k2_funct_1(C_347), B_349, A_348) | ~v1_funct_1(k2_funct_1(C_347)) | k2_relset_1(A_348, B_349, C_347)!=B_349 | ~v2_funct_1(C_347) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_348, B_349))) | ~v1_funct_2(C_347, A_348, B_349) | ~v1_funct_1(C_347))), inference(resolution, [status(thm)], [c_6, c_1466])).
% 8.04/2.84  tff(c_3261, plain, (![C_378, A_379, B_380]: (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(C_378)))) | k2_relset_1(A_379, B_380, k2_funct_1(k2_funct_1(C_378)))!=B_380 | ~v2_funct_1(k2_funct_1(k2_funct_1(C_378))) | ~v1_funct_1(k2_funct_1(k2_funct_1(C_378))) | k2_relset_1(B_380, A_379, k2_funct_1(C_378))!=A_379 | ~v2_funct_1(k2_funct_1(C_378)) | ~v1_funct_2(k2_funct_1(C_378), B_380, A_379) | ~v1_funct_1(k2_funct_1(C_378)) | k2_relset_1(A_379, B_380, C_378)!=B_380 | ~v2_funct_1(C_378) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_379, B_380))) | ~v1_funct_2(C_378, A_379, B_380) | ~v1_funct_1(C_378))), inference(resolution, [status(thm)], [c_608, c_3040])).
% 8.04/2.84  tff(c_3267, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2') | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3261])).
% 8.04/2.84  tff(c_3272, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2') | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_217, c_567, c_566, c_578, c_1348, c_1642, c_1641, c_3267])).
% 8.04/2.84  tff(c_3273, plain, (~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_3272])).
% 8.04/2.84  tff(c_3276, plain, (~v2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_3273])).
% 8.04/2.84  tff(c_3279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_44, c_217, c_217, c_3276])).
% 8.04/2.84  tff(c_3280, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2') | v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_3272])).
% 8.04/2.84  tff(c_3319, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_3280])).
% 8.04/2.84  tff(c_3322, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_3319])).
% 8.04/2.84  tff(c_3325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_44, c_217, c_567, c_3322])).
% 8.04/2.84  tff(c_3327, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_3280])).
% 8.04/2.84  tff(c_1415, plain, (![B_224, A_225, C_226]: (k1_relset_1(u1_struct_0(B_224), u1_struct_0(A_225), k2_tops_2(u1_struct_0(A_225), u1_struct_0(B_224), C_226))=k2_struct_0(B_224) | ~v2_funct_1(C_226) | k2_relset_1(u1_struct_0(A_225), u1_struct_0(B_224), C_226)!=k2_struct_0(B_224) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225), u1_struct_0(B_224)))) | ~v1_funct_2(C_226, u1_struct_0(A_225), u1_struct_0(B_224)) | ~v1_funct_1(C_226) | ~l1_struct_0(B_224) | v2_struct_0(B_224) | ~l1_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.04/2.84  tff(c_1436, plain, (![A_225, C_226]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_225), k2_tops_2(u1_struct_0(A_225), u1_struct_0('#skF_2'), C_226))=k2_struct_0('#skF_2') | ~v2_funct_1(C_226) | k2_relset_1(u1_struct_0(A_225), u1_struct_0('#skF_2'), C_226)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_226, u1_struct_0(A_225), u1_struct_0('#skF_2')) | ~v1_funct_1(C_226) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_225))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1415])).
% 8.04/2.84  tff(c_1457, plain, (![A_225, C_226]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_225), k2_tops_2(u1_struct_0(A_225), k2_struct_0('#skF_2'), C_226))=k2_struct_0('#skF_2') | ~v2_funct_1(C_226) | k2_relset_1(u1_struct_0(A_225), k2_struct_0('#skF_2'), C_226)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_225), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_226, u1_struct_0(A_225), k2_struct_0('#skF_2')) | ~v1_funct_1(C_226) | v2_struct_0('#skF_2') | ~l1_struct_0(A_225))), inference(demodulation, [status(thm), theory('equality')], [c_1331, c_64, c_64, c_64, c_64, c_1436])).
% 8.04/2.84  tff(c_1719, plain, (![A_249, C_250]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_249), k2_tops_2(u1_struct_0(A_249), k2_struct_0('#skF_2'), C_250))=k2_struct_0('#skF_2') | ~v2_funct_1(C_250) | k2_relset_1(u1_struct_0(A_249), k2_struct_0('#skF_2'), C_250)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_250, u1_struct_0(A_249), k2_struct_0('#skF_2')) | ~v1_funct_1(C_250) | ~l1_struct_0(A_249))), inference(negUnitSimplification, [status(thm)], [c_48, c_1457])).
% 8.04/2.84  tff(c_1728, plain, (![C_250]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_250))=k2_struct_0('#skF_2') | ~v2_funct_1(C_250) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_250)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_250, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_250) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1719])).
% 8.04/2.84  tff(c_1748, plain, (![C_251]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_251))=k2_struct_0('#skF_2') | ~v2_funct_1(C_251) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_251)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_251, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_251))), inference(demodulation, [status(thm), theory('equality')], [c_1248, c_65, c_65, c_65, c_65, c_1728])).
% 8.04/2.84  tff(c_1757, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_585, c_1748])).
% 8.04/2.84  tff(c_1761, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_78, c_567, c_217, c_1757])).
% 8.04/2.84  tff(c_1074, plain, (![A_184, B_185, C_186]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_184), u1_struct_0(B_185), C_186), B_185, A_184) | ~v3_tops_2(C_186, A_184, B_185) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_184), u1_struct_0(B_185)))) | ~v1_funct_2(C_186, u1_struct_0(A_184), u1_struct_0(B_185)) | ~v1_funct_1(C_186) | ~l1_pre_topc(B_185) | ~l1_pre_topc(A_184))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.04/2.84  tff(c_1079, plain, (![B_185, C_186]: (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_185), C_186), B_185, '#skF_1') | ~v3_tops_2(C_186, '#skF_1', B_185) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_185)))) | ~v1_funct_2(C_186, u1_struct_0('#skF_1'), u1_struct_0(B_185)) | ~v1_funct_1(C_186) | ~l1_pre_topc(B_185) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1074])).
% 8.04/2.84  tff(c_1127, plain, (![B_191, C_192]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_191), C_192), B_191, '#skF_1') | ~v3_tops_2(C_192, '#skF_1', B_191) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_191)))) | ~v1_funct_2(C_192, k2_struct_0('#skF_1'), u1_struct_0(B_191)) | ~v1_funct_1(C_192) | ~l1_pre_topc(B_191))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_65, c_1079])).
% 8.04/2.84  tff(c_1134, plain, (![C_192]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_192), '#skF_2', '#skF_1') | ~v3_tops_2(C_192, '#skF_1', '#skF_2') | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_192, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_192) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1127])).
% 8.04/2.84  tff(c_1146, plain, (![C_194]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_194), '#skF_2', '#skF_1') | ~v3_tops_2(C_194, '#skF_1', '#skF_2') | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_194, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_194))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_64, c_1134])).
% 8.04/2.84  tff(c_1153, plain, (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1146])).
% 8.04/2.84  tff(c_1157, plain, (v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_38, c_585, c_1153])).
% 8.04/2.84  tff(c_16, plain, (![A_10, B_11, C_12]: (k2_tops_2(A_10, B_11, C_12)=k2_funct_1(C_12) | ~v2_funct_1(C_12) | k2_relset_1(A_10, B_11, C_12)!=B_11 | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_2(C_12, A_10, B_11) | ~v1_funct_1(C_12))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.04/2.84  tff(c_1884, plain, (![B_265, A_266, C_267]: (k2_tops_2(B_265, A_266, k2_funct_1(C_267))=k2_funct_1(k2_funct_1(C_267)) | ~v2_funct_1(k2_funct_1(C_267)) | k2_relset_1(B_265, A_266, k2_funct_1(C_267))!=A_266 | ~v1_funct_2(k2_funct_1(C_267), B_265, A_266) | ~v1_funct_1(k2_funct_1(C_267)) | k2_relset_1(A_266, B_265, C_267)!=B_265 | ~v2_funct_1(C_267) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_266, B_265))) | ~v1_funct_2(C_267, A_266, B_265) | ~v1_funct_1(C_267))), inference(resolution, [status(thm)], [c_591, c_16])).
% 8.04/2.84  tff(c_1890, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1884])).
% 8.04/2.84  tff(c_1894, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_217, c_567, c_566, c_578, c_1642, c_1348, c_1890])).
% 8.04/2.84  tff(c_611, plain, (![C_125, A_126, B_127]: (v1_relat_1(k2_funct_1(C_125)) | k2_relset_1(A_126, B_127, C_125)!=B_127 | ~v2_funct_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_2(C_125, A_126, B_127) | ~v1_funct_1(C_125))), inference(resolution, [status(thm)], [c_591, c_4])).
% 8.04/2.84  tff(c_1652, plain, (![C_243, B_244, A_245]: (v1_relat_1(k2_funct_1(k2_funct_1(C_243))) | k2_relset_1(B_244, A_245, k2_funct_1(C_243))!=A_245 | ~v2_funct_1(k2_funct_1(C_243)) | ~v1_funct_2(k2_funct_1(C_243), B_244, A_245) | ~v1_funct_1(k2_funct_1(C_243)) | k2_relset_1(A_245, B_244, C_243)!=B_244 | ~v2_funct_1(C_243) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_245, B_244))) | ~v1_funct_2(C_243, A_245, B_244) | ~v1_funct_1(C_243))), inference(resolution, [status(thm)], [c_6, c_611])).
% 8.04/2.84  tff(c_1658, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1652])).
% 8.04/2.84  tff(c_1662, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_217, c_567, c_566, c_578, c_1348, c_1642, c_1658])).
% 8.04/2.84  tff(c_3281, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_3272])).
% 8.04/2.84  tff(c_617, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_611])).
% 8.04/2.84  tff(c_621, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_217, c_567, c_617])).
% 8.04/2.84  tff(c_3085, plain, (![A_356, B_357, C_358]: (k2_tops_2(A_356, B_357, k2_funct_1(k2_funct_1(C_358)))=k2_funct_1(k2_funct_1(k2_funct_1(C_358))) | ~v2_funct_1(k2_funct_1(k2_funct_1(C_358))) | k2_relset_1(A_356, B_357, k2_funct_1(k2_funct_1(C_358)))!=B_357 | ~v1_funct_2(k2_funct_1(k2_funct_1(C_358)), A_356, B_357) | ~v1_funct_1(k2_funct_1(k2_funct_1(C_358))) | k2_relset_1(B_357, A_356, k2_funct_1(C_358))!=A_356 | ~v2_funct_1(k2_funct_1(C_358)) | ~v1_funct_2(k2_funct_1(C_358), B_357, A_356) | ~v1_funct_1(k2_funct_1(C_358)) | k2_relset_1(A_356, B_357, C_358)!=B_357 | ~v2_funct_1(C_358) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))) | ~v1_funct_2(C_358, A_356, B_357) | ~v1_funct_1(C_358))), inference(resolution, [status(thm)], [c_6, c_1884])).
% 8.04/2.84  tff(c_3551, plain, (![A_409, B_410, C_411]: (k2_tops_2(A_409, B_410, k2_funct_1(k2_funct_1(C_411)))=k2_funct_1(k2_funct_1(k2_funct_1(C_411))) | ~v2_funct_1(k2_funct_1(k2_funct_1(C_411))) | k2_relset_1(A_409, B_410, k2_funct_1(k2_funct_1(C_411)))!=B_410 | ~v1_funct_1(k2_funct_1(k2_funct_1(C_411))) | k2_relset_1(B_410, A_409, k2_funct_1(C_411))!=A_409 | ~v2_funct_1(k2_funct_1(C_411)) | ~v1_funct_2(k2_funct_1(C_411), B_410, A_409) | ~v1_funct_1(k2_funct_1(C_411)) | k2_relset_1(A_409, B_410, C_411)!=B_410 | ~v2_funct_1(C_411) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_409, B_410))) | ~v1_funct_2(C_411, A_409, B_410) | ~v1_funct_1(C_411))), inference(resolution, [status(thm)], [c_608, c_3085])).
% 8.04/2.84  tff(c_3560, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2') | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3551])).
% 8.04/2.84  tff(c_3565, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_217, c_567, c_566, c_578, c_1348, c_1642, c_1641, c_3327, c_3281, c_3560])).
% 8.04/2.84  tff(c_3598, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_3565])).
% 8.04/2.84  tff(c_3608, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_44, c_217, c_585, c_3598])).
% 8.04/2.84  tff(c_1231, plain, (![A_206, B_207, A_208]: (m1_subset_1(A_206, k1_zfmisc_1(k2_zfmisc_1(B_207, A_208))) | k2_relset_1(A_208, B_207, k2_funct_1(A_206))!=B_207 | ~v2_funct_1(k2_funct_1(A_206)) | ~m1_subset_1(k2_funct_1(A_206), k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))) | ~v1_funct_2(k2_funct_1(A_206), A_208, B_207) | ~v1_funct_1(k2_funct_1(A_206)) | ~v2_funct_1(A_206) | ~v1_funct_1(A_206) | ~v1_relat_1(A_206))), inference(superposition, [status(thm), theory('equality')], [c_2, c_591])).
% 8.04/2.84  tff(c_1237, plain, (![A_1, B_207, A_208]: (m1_subset_1(k2_funct_1(A_1), k1_zfmisc_1(k2_zfmisc_1(B_207, A_208))) | k2_relset_1(A_208, B_207, k2_funct_1(k2_funct_1(A_1)))!=B_207 | ~v2_funct_1(k2_funct_1(k2_funct_1(A_1))) | ~m1_subset_1(A_1, k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))) | ~v1_funct_2(k2_funct_1(k2_funct_1(A_1)), A_208, B_207) | ~v1_funct_1(k2_funct_1(k2_funct_1(A_1))) | ~v2_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(k2_funct_1(A_1)) | ~v1_relat_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1231])).
% 8.04/2.84  tff(c_3678, plain, (![B_207, A_208]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_207, A_208))) | k2_relset_1(A_208, B_207, k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))))!=B_207 | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_208, B_207))) | ~v1_funct_2(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), A_208, B_207) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))) | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_3608, c_1237])).
% 8.04/2.84  tff(c_4653, plain, (![B_421, A_422]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_421, A_422))) | k2_relset_1(A_422, B_421, k2_funct_1(k2_funct_1('#skF_3')))!=B_421 | ~m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_422, B_421))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_422, B_421))), inference(demodulation, [status(thm), theory('equality')], [c_1662, c_1641, c_3281, c_621, c_3608, c_566, c_3608, c_1348, c_3608, c_1641, c_3608, c_3608, c_3281, c_3608, c_3608, c_3678])).
% 8.04/2.84  tff(c_4667, plain, (![B_421, A_422]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_421, A_422))) | k2_relset_1(A_422, B_421, k2_funct_1(k2_funct_1('#skF_3')))!=B_421 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_422, B_421))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_422, B_421) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4653])).
% 8.04/2.84  tff(c_4677, plain, (![B_423, A_424]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(B_423, A_424))) | k2_relset_1(A_424, B_423, k2_funct_1(k2_funct_1('#skF_3')))!=B_423 | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_424, B_423))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), A_424, B_423))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_44, c_217, c_4667])).
% 8.04/2.84  tff(c_1818, plain, (![C_256, A_257, B_258]: (v3_tops_2(C_256, A_257, B_258) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_257), u1_struct_0(B_258), C_256), B_258, A_257) | ~v5_pre_topc(C_256, A_257, B_258) | ~v2_funct_1(C_256) | k2_relset_1(u1_struct_0(A_257), u1_struct_0(B_258), C_256)!=k2_struct_0(B_258) | k1_relset_1(u1_struct_0(A_257), u1_struct_0(B_258), C_256)!=k2_struct_0(A_257) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_257), u1_struct_0(B_258)))) | ~v1_funct_2(C_256, u1_struct_0(A_257), u1_struct_0(B_258)) | ~v1_funct_1(C_256) | ~l1_pre_topc(B_258) | ~l1_pre_topc(A_257))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.04/2.84  tff(c_1824, plain, (![C_256, B_258]: (v3_tops_2(C_256, '#skF_2', B_258) | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0(B_258), C_256), B_258, '#skF_2') | ~v5_pre_topc(C_256, '#skF_2', B_258) | ~v2_funct_1(C_256) | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_258), C_256)!=k2_struct_0(B_258) | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_258), C_256)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_258)))) | ~v1_funct_2(C_256, u1_struct_0('#skF_2'), u1_struct_0(B_258)) | ~v1_funct_1(C_256) | ~l1_pre_topc(B_258) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1818])).
% 8.04/2.84  tff(c_3076, plain, (![C_354, B_355]: (v3_tops_2(C_354, '#skF_2', B_355) | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), u1_struct_0(B_355), C_354), B_355, '#skF_2') | ~v5_pre_topc(C_354, '#skF_2', B_355) | ~v2_funct_1(C_354) | k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(B_355), C_354)!=k2_struct_0(B_355) | k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(B_355), C_354)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0(B_355)))) | ~v1_funct_2(C_354, k2_struct_0('#skF_2'), u1_struct_0(B_355)) | ~v1_funct_1(C_354) | ~l1_pre_topc(B_355))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_64, c_64, c_64, c_1824])).
% 8.04/2.84  tff(c_3078, plain, (![C_354]: (v3_tops_2(C_354, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_354), '#skF_1', '#skF_2') | ~v5_pre_topc(C_354, '#skF_2', '#skF_1') | ~v2_funct_1(C_354) | k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), C_354)!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1'), C_354)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2(C_354, k2_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1(C_354) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_3076])).
% 8.04/2.84  tff(c_3082, plain, (![C_354]: (v3_tops_2(C_354, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_354), '#skF_1', '#skF_2') | ~v5_pre_topc(C_354, '#skF_2', '#skF_1') | ~v2_funct_1(C_354) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_354)!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_354)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_354, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_354, k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_354))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_65, c_65, c_65, c_3078])).
% 8.04/2.84  tff(c_4739, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4677, c_3082])).
% 8.04/2.84  tff(c_5174, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3327, c_566, c_578, c_1761, c_1642, c_1348, c_1157, c_1894, c_4739])).
% 8.04/2.84  tff(c_5175, plain, (~v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_586, c_5174])).
% 8.04/2.84  tff(c_5475, plain, (~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_5175])).
% 8.04/2.84  tff(c_5511, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_608, c_5475])).
% 8.04/2.84  tff(c_5518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_78, c_217, c_567, c_566, c_578, c_1348, c_1642, c_5511])).
% 8.04/2.84  tff(c_5519, plain, (~v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_5175])).
% 8.04/2.84  tff(c_5523, plain, (~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_5519])).
% 8.04/2.84  tff(c_5526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_44, c_217, c_801, c_5523])).
% 8.04/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.04/2.84  
% 8.04/2.84  Inference rules
% 8.04/2.84  ----------------------
% 8.04/2.84  #Ref     : 0
% 8.04/2.84  #Sup     : 1009
% 8.04/2.84  #Fact    : 0
% 8.04/2.84  #Define  : 0
% 8.04/2.84  #Split   : 9
% 8.04/2.84  #Chain   : 0
% 8.04/2.84  #Close   : 0
% 8.04/2.84  
% 8.04/2.84  Ordering : KBO
% 8.04/2.84  
% 8.04/2.84  Simplification rules
% 8.04/2.84  ----------------------
% 8.04/2.84  #Subsume      : 156
% 8.04/2.84  #Demod        : 2781
% 8.04/2.84  #Tautology    : 221
% 8.04/2.84  #SimpNegUnit  : 20
% 8.04/2.84  #BackRed      : 5
% 8.04/2.84  
% 8.04/2.84  #Partial instantiations: 0
% 8.04/2.84  #Strategies tried      : 1
% 8.04/2.84  
% 8.04/2.84  Timing (in seconds)
% 8.04/2.84  ----------------------
% 8.04/2.84  Preprocessing        : 0.38
% 8.04/2.84  Parsing              : 0.20
% 8.04/2.84  CNF conversion       : 0.03
% 8.04/2.84  Main loop            : 1.61
% 8.04/2.84  Inferencing          : 0.49
% 8.04/2.84  Reduction            : 0.59
% 8.04/2.84  Demodulation         : 0.45
% 8.04/2.84  BG Simplification    : 0.07
% 8.04/2.84  Subsumption          : 0.37
% 8.04/2.84  Abstraction          : 0.09
% 8.04/2.84  MUC search           : 0.00
% 8.04/2.84  Cooper               : 0.00
% 8.04/2.84  Total                : 2.06
% 8.04/2.84  Index Insertion      : 0.00
% 8.04/2.84  Index Deletion       : 0.00
% 8.04/2.84  Index Matching       : 0.00
% 8.04/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
