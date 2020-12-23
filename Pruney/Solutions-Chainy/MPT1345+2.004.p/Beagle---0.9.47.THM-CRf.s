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
% DateTime   : Thu Dec  3 10:23:49 EST 2020

% Result     : Theorem 6.69s
% Output     : CNFRefutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :  214 (9269 expanded)
%              Number of leaves         :   34 (3147 expanded)
%              Depth                    :   23
%              Number of atoms          :  786 (26004 expanded)
%              Number of equality atoms :  126 (4362 expanded)
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

tff(f_154,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_81,axiom,(
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

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_134,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

tff(f_116,axiom,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_pre_topc(A_40) ) ),
    inference(resolution,[status(thm)],[c_8,c_52])).

tff(c_65,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_57])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_64,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_57])).

tff(c_42,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_67,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_42])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_67])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_66])).

tff(c_137,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_tops_2(A_57,B_58,C_59) = k2_funct_1(C_59)
      | ~ v2_funct_1(C_59)
      | k2_relset_1(A_57,B_58,C_59) != B_58
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_143,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_137])).

tff(c_147,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_143])).

tff(c_148,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_38,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_481,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(u1_struct_0(A_102),u1_struct_0(B_103),C_104) = k2_struct_0(B_103)
      | ~ v3_tops_2(C_104,A_102,B_103)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),u1_struct_0(B_103))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_102),u1_struct_0(B_103))
      | ~ v1_funct_1(C_104)
      | ~ l1_pre_topc(B_103)
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_497,plain,(
    ! [A_102,C_104] :
      ( k2_relset_1(u1_struct_0(A_102),u1_struct_0('#skF_2'),C_104) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_104,A_102,'#skF_2')
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_102),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_104)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_481])).

tff(c_567,plain,(
    ! [A_112,C_113] :
      ( k2_relset_1(u1_struct_0(A_112),k2_struct_0('#skF_2'),C_113) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_113,A_112,'#skF_2')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_113,u1_struct_0(A_112),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_64,c_497])).

tff(c_574,plain,(
    ! [C_113] :
      ( k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_113) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_113,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_113,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_567])).

tff(c_583,plain,(
    ! [C_114] :
      ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_114) = k2_struct_0('#skF_2')
      | ~ v3_tops_2(C_114,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_114,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_65,c_574])).

tff(c_590,plain,
    ( k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_583])).

tff(c_594,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_38,c_590])).

tff(c_596,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_594])).

tff(c_597,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_629,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_597])).

tff(c_603,plain,(
    ! [C_115,A_116,B_117] :
      ( v2_funct_1(C_115)
      | ~ v3_tops_2(C_115,A_116,B_117)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116),u1_struct_0(B_117))))
      | ~ v1_funct_2(C_115,u1_struct_0(A_116),u1_struct_0(B_117))
      | ~ v1_funct_1(C_115)
      | ~ l1_pre_topc(B_117)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_610,plain,(
    ! [C_115,B_117] :
      ( v2_funct_1(C_115)
      | ~ v3_tops_2(C_115,'#skF_1',B_117)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_117))))
      | ~ v1_funct_2(C_115,u1_struct_0('#skF_1'),u1_struct_0(B_117))
      | ~ v1_funct_1(C_115)
      | ~ l1_pre_topc(B_117)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_603])).

tff(c_658,plain,(
    ! [C_122,B_123] :
      ( v2_funct_1(C_122)
      | ~ v3_tops_2(C_122,'#skF_1',B_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_123))))
      | ~ v1_funct_2(C_122,k2_struct_0('#skF_1'),u1_struct_0(B_123))
      | ~ v1_funct_1(C_122)
      | ~ l1_pre_topc(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_610])).

tff(c_668,plain,(
    ! [C_122] :
      ( v2_funct_1(C_122)
      | ~ v3_tops_2(C_122,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_122,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_122)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_658])).

tff(c_674,plain,(
    ! [C_124] :
      ( v2_funct_1(C_124)
      | ~ v3_tops_2(C_124,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_124,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_668])).

tff(c_681,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_674])).

tff(c_685,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_38,c_681])).

tff(c_687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_629,c_685])).

tff(c_688,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_36,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_83,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_64,c_36])).

tff(c_693,plain,(
    ~ v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_83])).

tff(c_101,plain,(
    ! [A_45,B_46,C_47] :
      ( v1_funct_1(k2_tops_2(A_45,B_46,C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_104,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_101])).

tff(c_107,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_104])).

tff(c_692,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_107])).

tff(c_108,plain,(
    ! [A_48,B_49,C_50] :
      ( v1_funct_2(k2_tops_2(A_48,B_49,C_50),B_49,A_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_110,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_108])).

tff(c_113,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_110])).

tff(c_691,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_113])).

tff(c_598,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_689,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_597])).

tff(c_2778,plain,(
    ! [A_351,B_352,C_353] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_351),u1_struct_0(B_352),C_353))
      | ~ v2_funct_1(C_353)
      | k2_relset_1(u1_struct_0(A_351),u1_struct_0(B_352),C_353) != k2_struct_0(B_352)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_351),u1_struct_0(B_352))))
      | ~ v1_funct_2(C_353,u1_struct_0(A_351),u1_struct_0(B_352))
      | ~ v1_funct_1(C_353)
      | ~ l1_struct_0(B_352)
      | ~ l1_struct_0(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2788,plain,(
    ! [A_351,C_353] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_351),u1_struct_0('#skF_1'),C_353))
      | ~ v2_funct_1(C_353)
      | k2_relset_1(u1_struct_0(A_351),u1_struct_0('#skF_1'),C_353) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_351),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_353,u1_struct_0(A_351),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_353)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(A_351) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_2778])).

tff(c_2797,plain,(
    ! [A_351,C_353] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_351),k2_struct_0('#skF_1'),C_353))
      | ~ v2_funct_1(C_353)
      | k2_relset_1(u1_struct_0(A_351),k2_struct_0('#skF_1'),C_353) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_351),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_353,u1_struct_0(A_351),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_353)
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0(A_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_65,c_2788])).

tff(c_3508,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2797])).

tff(c_3511,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_3508])).

tff(c_3515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3511])).

tff(c_3517,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2797])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2897,plain,(
    ! [B_360,A_361,C_362] :
      ( k1_relset_1(u1_struct_0(B_360),u1_struct_0(A_361),k2_tops_2(u1_struct_0(A_361),u1_struct_0(B_360),C_362)) = k2_struct_0(B_360)
      | ~ v2_funct_1(C_362)
      | k2_relset_1(u1_struct_0(A_361),u1_struct_0(B_360),C_362) != k2_struct_0(B_360)
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361),u1_struct_0(B_360))))
      | ~ v1_funct_2(C_362,u1_struct_0(A_361),u1_struct_0(B_360))
      | ~ v1_funct_1(C_362)
      | ~ l1_struct_0(B_360)
      | v2_struct_0(B_360)
      | ~ l1_struct_0(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2918,plain,(
    ! [A_361,C_362] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_361),k2_tops_2(u1_struct_0(A_361),u1_struct_0('#skF_2'),C_362)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_362)
      | k2_relset_1(u1_struct_0(A_361),u1_struct_0('#skF_2'),C_362) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_362,u1_struct_0(A_361),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_362)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2897])).

tff(c_2934,plain,(
    ! [A_361,C_362] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_361),k2_tops_2(u1_struct_0(A_361),k2_struct_0('#skF_2'),C_362)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_362)
      | k2_relset_1(u1_struct_0(A_361),k2_struct_0('#skF_2'),C_362) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_362,u1_struct_0(A_361),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_362)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_64,c_2918])).

tff(c_2935,plain,(
    ! [A_361,C_362] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_361),k2_tops_2(u1_struct_0(A_361),k2_struct_0('#skF_2'),C_362)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_362)
      | k2_relset_1(u1_struct_0(A_361),k2_struct_0('#skF_2'),C_362) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_362,u1_struct_0(A_361),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_362)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_361) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2934])).

tff(c_2984,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2935])).

tff(c_2987,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_2984])).

tff(c_2991,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2987])).

tff(c_2993,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2935])).

tff(c_2927,plain,(
    ! [A_361,C_362] :
      ( k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_361),k2_tops_2(u1_struct_0(A_361),k2_struct_0('#skF_2'),C_362)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_362)
      | k2_relset_1(u1_struct_0(A_361),u1_struct_0('#skF_2'),C_362) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_362,u1_struct_0(A_361),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_362)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_361) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2897])).

tff(c_2938,plain,(
    ! [A_361,C_362] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_361),k2_tops_2(u1_struct_0(A_361),k2_struct_0('#skF_2'),C_362)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_362)
      | k2_relset_1(u1_struct_0(A_361),k2_struct_0('#skF_2'),C_362) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_362,u1_struct_0(A_361),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_362)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_361) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_64,c_2927])).

tff(c_2939,plain,(
    ! [A_361,C_362] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_361),k2_tops_2(u1_struct_0(A_361),k2_struct_0('#skF_2'),C_362)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_362)
      | k2_relset_1(u1_struct_0(A_361),k2_struct_0('#skF_2'),C_362) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_362,u1_struct_0(A_361),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_362)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_361) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2938])).

tff(c_3382,plain,(
    ! [A_401,C_402] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_401),k2_tops_2(u1_struct_0(A_401),k2_struct_0('#skF_2'),C_402)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_402)
      | k2_relset_1(u1_struct_0(A_401),k2_struct_0('#skF_2'),C_402) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_401),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_402,u1_struct_0(A_401),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_402)
      | ~ l1_struct_0(A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2993,c_2939])).

tff(c_3391,plain,(
    ! [C_402] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_402)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_402)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_402) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_402,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_402)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_3382])).

tff(c_3403,plain,(
    ! [C_402] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_402)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_402)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_402) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_402,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_402)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_65,c_65,c_3391])).

tff(c_3717,plain,(
    ! [C_438] :
      ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_438)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_438)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_438) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_438,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_438,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3517,c_3403])).

tff(c_3729,plain,
    ( k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_3717])).

tff(c_3735,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_78,c_598,c_689,c_3729])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] :
      ( m1_subset_1(k2_tops_2(A_17,B_18,C_19),k1_zfmisc_1(k2_zfmisc_1(B_18,A_17)))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_697,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_24])).

tff(c_701,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_78,c_697])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( k2_tops_2(A_7,B_8,C_9) = k2_funct_1(C_9)
      | ~ v2_funct_1(C_9)
      | k2_relset_1(A_7,B_8,C_9) != B_8
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(C_9,A_7,B_8)
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_747,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_701,c_10])).

tff(c_761,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_691,c_747])).

tff(c_817,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_761])).

tff(c_1271,plain,(
    ! [B_190,A_191,C_192] :
      ( k2_relset_1(u1_struct_0(B_190),u1_struct_0(A_191),k2_tops_2(u1_struct_0(A_191),u1_struct_0(B_190),C_192)) = k2_struct_0(A_191)
      | ~ v2_funct_1(C_192)
      | k2_relset_1(u1_struct_0(A_191),u1_struct_0(B_190),C_192) != k2_struct_0(B_190)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),u1_struct_0(B_190))))
      | ~ v1_funct_2(C_192,u1_struct_0(A_191),u1_struct_0(B_190))
      | ~ v1_funct_1(C_192)
      | ~ l1_struct_0(B_190)
      | v2_struct_0(B_190)
      | ~ l1_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1292,plain,(
    ! [A_191,C_192] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_191),k2_tops_2(u1_struct_0(A_191),u1_struct_0('#skF_2'),C_192)) = k2_struct_0(A_191)
      | ~ v2_funct_1(C_192)
      | k2_relset_1(u1_struct_0(A_191),u1_struct_0('#skF_2'),C_192) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_192,u1_struct_0(A_191),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_192)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1271])).

tff(c_1308,plain,(
    ! [A_191,C_192] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_191),k2_tops_2(u1_struct_0(A_191),k2_struct_0('#skF_2'),C_192)) = k2_struct_0(A_191)
      | ~ v2_funct_1(C_192)
      | k2_relset_1(u1_struct_0(A_191),k2_struct_0('#skF_2'),C_192) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_192,u1_struct_0(A_191),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_192)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_64,c_1292])).

tff(c_1309,plain,(
    ! [A_191,C_192] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_191),k2_tops_2(u1_struct_0(A_191),k2_struct_0('#skF_2'),C_192)) = k2_struct_0(A_191)
      | ~ v2_funct_1(C_192)
      | k2_relset_1(u1_struct_0(A_191),k2_struct_0('#skF_2'),C_192) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_192,u1_struct_0(A_191),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_192)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_191) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1308])).

tff(c_1345,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1309])).

tff(c_1348,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_1345])).

tff(c_1352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1348])).

tff(c_1354,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1309])).

tff(c_1144,plain,(
    ! [A_174,B_175,C_176] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_174),u1_struct_0(B_175),C_176))
      | ~ v2_funct_1(C_176)
      | k2_relset_1(u1_struct_0(A_174),u1_struct_0(B_175),C_176) != k2_struct_0(B_175)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_174),u1_struct_0(B_175))))
      | ~ v1_funct_2(C_176,u1_struct_0(A_174),u1_struct_0(B_175))
      | ~ v1_funct_1(C_176)
      | ~ l1_struct_0(B_175)
      | ~ l1_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1160,plain,(
    ! [A_174,C_176] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_174),u1_struct_0('#skF_2'),C_176))
      | ~ v2_funct_1(C_176)
      | k2_relset_1(u1_struct_0(A_174),u1_struct_0('#skF_2'),C_176) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_174),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_176,u1_struct_0(A_174),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_176)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1144])).

tff(c_1165,plain,(
    ! [A_174,C_176] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_174),k2_struct_0('#skF_2'),C_176))
      | ~ v2_funct_1(C_176)
      | k2_relset_1(u1_struct_0(A_174),k2_struct_0('#skF_2'),C_176) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_174),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_176,u1_struct_0(A_174),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_176)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_1160])).

tff(c_1514,plain,(
    ! [A_217,C_218] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_217),k2_struct_0('#skF_2'),C_218))
      | ~ v2_funct_1(C_218)
      | k2_relset_1(u1_struct_0(A_217),k2_struct_0('#skF_2'),C_218) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_217),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_218,u1_struct_0(A_217),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_218)
      | ~ l1_struct_0(A_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1354,c_1165])).

tff(c_1521,plain,(
    ! [C_218] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_218))
      | ~ v2_funct_1(C_218)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_218) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_218,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_218)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1514])).

tff(c_1526,plain,(
    ! [C_218] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_218))
      | ~ v2_funct_1(C_218)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_218) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_218,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_218)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_65,c_1521])).

tff(c_1552,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1526])).

tff(c_1555,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1552])).

tff(c_1559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1555])).

tff(c_1561,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1526])).

tff(c_1301,plain,(
    ! [A_191,C_192] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_191),k2_tops_2(u1_struct_0(A_191),k2_struct_0('#skF_2'),C_192)) = k2_struct_0(A_191)
      | ~ v2_funct_1(C_192)
      | k2_relset_1(u1_struct_0(A_191),u1_struct_0('#skF_2'),C_192) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_192,u1_struct_0(A_191),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_192)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1271])).

tff(c_1312,plain,(
    ! [A_191,C_192] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_191),k2_tops_2(u1_struct_0(A_191),k2_struct_0('#skF_2'),C_192)) = k2_struct_0(A_191)
      | ~ v2_funct_1(C_192)
      | k2_relset_1(u1_struct_0(A_191),k2_struct_0('#skF_2'),C_192) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_192,u1_struct_0(A_191),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_192)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_64,c_1301])).

tff(c_1313,plain,(
    ! [A_191,C_192] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_191),k2_tops_2(u1_struct_0(A_191),k2_struct_0('#skF_2'),C_192)) = k2_struct_0(A_191)
      | ~ v2_funct_1(C_192)
      | k2_relset_1(u1_struct_0(A_191),k2_struct_0('#skF_2'),C_192) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_192,u1_struct_0(A_191),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_192)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_191) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1312])).

tff(c_1666,plain,(
    ! [A_235,C_236] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_235),k2_tops_2(u1_struct_0(A_235),k2_struct_0('#skF_2'),C_236)) = k2_struct_0(A_235)
      | ~ v2_funct_1(C_236)
      | k2_relset_1(u1_struct_0(A_235),k2_struct_0('#skF_2'),C_236) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_236,u1_struct_0(A_235),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_236)
      | ~ l1_struct_0(A_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1354,c_1313])).

tff(c_1675,plain,(
    ! [C_236] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_236)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_236)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_236) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_236,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_236)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1666])).

tff(c_1704,plain,(
    ! [C_238] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_238)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_238)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_238) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_238,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_65,c_65,c_65,c_65,c_1675])).

tff(c_1713,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_688,c_1704])).

tff(c_1717,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_78,c_598,c_689,c_1713])).

tff(c_1719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_817,c_1717])).

tff(c_1721,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_761])).

tff(c_1720,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_761])).

tff(c_1726,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1720])).

tff(c_2101,plain,(
    ! [B_284,A_285,C_286] :
      ( k1_relset_1(u1_struct_0(B_284),u1_struct_0(A_285),k2_tops_2(u1_struct_0(A_285),u1_struct_0(B_284),C_286)) = k2_struct_0(B_284)
      | ~ v2_funct_1(C_286)
      | k2_relset_1(u1_struct_0(A_285),u1_struct_0(B_284),C_286) != k2_struct_0(B_284)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285),u1_struct_0(B_284))))
      | ~ v1_funct_2(C_286,u1_struct_0(A_285),u1_struct_0(B_284))
      | ~ v1_funct_1(C_286)
      | ~ l1_struct_0(B_284)
      | v2_struct_0(B_284)
      | ~ l1_struct_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2122,plain,(
    ! [A_285,C_286] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_285),k2_tops_2(u1_struct_0(A_285),u1_struct_0('#skF_2'),C_286)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_286)
      | k2_relset_1(u1_struct_0(A_285),u1_struct_0('#skF_2'),C_286) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_286,u1_struct_0(A_285),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_286)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2101])).

tff(c_2138,plain,(
    ! [A_285,C_286] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_285),k2_tops_2(u1_struct_0(A_285),k2_struct_0('#skF_2'),C_286)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_286)
      | k2_relset_1(u1_struct_0(A_285),k2_struct_0('#skF_2'),C_286) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_286,u1_struct_0(A_285),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_286)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_64,c_2122])).

tff(c_2139,plain,(
    ! [A_285,C_286] :
      ( k1_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_285),k2_tops_2(u1_struct_0(A_285),k2_struct_0('#skF_2'),C_286)) = k2_struct_0('#skF_2')
      | ~ v2_funct_1(C_286)
      | k2_relset_1(u1_struct_0(A_285),k2_struct_0('#skF_2'),C_286) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_286,u1_struct_0(A_285),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_286)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_285) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2138])).

tff(c_2178,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2139])).

tff(c_2181,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_2178])).

tff(c_2185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2181])).

tff(c_2187,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2139])).

tff(c_1975,plain,(
    ! [A_269,B_270,C_271] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_269),u1_struct_0(B_270),C_271))
      | ~ v2_funct_1(C_271)
      | k2_relset_1(u1_struct_0(A_269),u1_struct_0(B_270),C_271) != k2_struct_0(B_270)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_269),u1_struct_0(B_270))))
      | ~ v1_funct_2(C_271,u1_struct_0(A_269),u1_struct_0(B_270))
      | ~ v1_funct_1(C_271)
      | ~ l1_struct_0(B_270)
      | ~ l1_struct_0(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1982,plain,(
    ! [B_270,C_271] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_270),C_271))
      | ~ v2_funct_1(C_271)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_270),C_271) != k2_struct_0(B_270)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_270))))
      | ~ v1_funct_2(C_271,u1_struct_0('#skF_1'),u1_struct_0(B_270))
      | ~ v1_funct_1(C_271)
      | ~ l1_struct_0(B_270)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1975])).

tff(c_1993,plain,(
    ! [B_270,C_271] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_270),C_271))
      | ~ v2_funct_1(C_271)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_270),C_271) != k2_struct_0(B_270)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_270))))
      | ~ v1_funct_2(C_271,k2_struct_0('#skF_1'),u1_struct_0(B_270))
      | ~ v1_funct_1(C_271)
      | ~ l1_struct_0(B_270)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_65,c_1982])).

tff(c_2438,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1993])).

tff(c_2441,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_2438])).

tff(c_2445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2441])).

tff(c_2466,plain,(
    ! [B_327,C_328] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_327),C_328))
      | ~ v2_funct_1(C_328)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_327),C_328) != k2_struct_0(B_327)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_327))))
      | ~ v1_funct_2(C_328,k2_struct_0('#skF_1'),u1_struct_0(B_327))
      | ~ v1_funct_1(C_328)
      | ~ l1_struct_0(B_327) ) ),
    inference(splitRight,[status(thm)],[c_1993])).

tff(c_2476,plain,(
    ! [C_328] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_328))
      | ~ v2_funct_1(C_328)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_328) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_328,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_328)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2466])).

tff(c_2488,plain,(
    ! [C_330] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_330))
      | ~ v2_funct_1(C_330)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_330) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_330,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2187,c_64,c_64,c_64,c_2476])).

tff(c_2495,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2488])).

tff(c_2499,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_598,c_689,c_688,c_2495])).

tff(c_2501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1726,c_2499])).

tff(c_2503,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1720])).

tff(c_2652,plain,(
    ! [A_337,B_338,C_339] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_337),u1_struct_0(B_338),C_339),B_338,A_337)
      | ~ v3_tops_2(C_339,A_337,B_338)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_337),u1_struct_0(B_338))))
      | ~ v1_funct_2(C_339,u1_struct_0(A_337),u1_struct_0(B_338))
      | ~ v1_funct_1(C_339)
      | ~ l1_pre_topc(B_338)
      | ~ l1_pre_topc(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2663,plain,(
    ! [A_337,C_339] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_337),u1_struct_0('#skF_2'),C_339),'#skF_2',A_337)
      | ~ v3_tops_2(C_339,A_337,'#skF_2')
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_337),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_339,u1_struct_0(A_337),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_339)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_337) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2652])).

tff(c_3349,plain,(
    ! [A_398,C_399] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_398),k2_struct_0('#skF_2'),C_399),'#skF_2',A_398)
      | ~ v3_tops_2(C_399,A_398,'#skF_2')
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_398),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_399,u1_struct_0(A_398),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_399)
      | ~ l1_pre_topc(A_398) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_64,c_2663])).

tff(c_3354,plain,(
    ! [C_399] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_399),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_399,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_399,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_399)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_3349])).

tff(c_3362,plain,(
    ! [C_400] :
      ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_400),'#skF_2','#skF_1')
      | ~ v3_tops_2(C_400,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_400,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_65,c_3354])).

tff(c_3372,plain,
    ( v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3362])).

tff(c_3379,plain,(
    v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_38,c_688,c_3372])).

tff(c_2502,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1720])).

tff(c_28,plain,(
    ! [A_17,B_18,C_19] :
      ( v1_funct_1(k2_tops_2(A_17,B_18,C_19))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_755,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_701,c_28])).

tff(c_770,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_691,c_755])).

tff(c_2521,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2502,c_770])).

tff(c_26,plain,(
    ! [A_17,B_18,C_19] :
      ( v1_funct_2(k2_tops_2(A_17,B_18,C_19),B_18,A_17)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(C_19,A_17,B_18)
      | ~ v1_funct_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_752,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_701,c_26])).

tff(c_767,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_691,c_752])).

tff(c_2520,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2502,c_767])).

tff(c_4,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_funct_1(k2_funct_1(A_1)) = A_1
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2526,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2502,c_24])).

tff(c_2530,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_691,c_701,c_2526])).

tff(c_619,plain,(
    ! [C_115,A_116] :
      ( v2_funct_1(C_115)
      | ~ v3_tops_2(C_115,A_116,'#skF_2')
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_115,u1_struct_0(A_116),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_115)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_603])).

tff(c_729,plain,(
    ! [C_128,A_129] :
      ( v2_funct_1(C_128)
      | ~ v3_tops_2(C_128,A_129,'#skF_2')
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_128,u1_struct_0(A_129),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_128)
      | ~ l1_pre_topc(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_619])).

tff(c_736,plain,(
    ! [C_128] :
      ( v2_funct_1(C_128)
      | ~ v3_tops_2(C_128,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_128,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_128)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_729])).

tff(c_742,plain,(
    ! [C_128] :
      ( v2_funct_1(C_128)
      | ~ v3_tops_2(C_128,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_128,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_736])).

tff(c_2575,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2530,c_742])).

tff(c_2595,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_2520,c_2575])).

tff(c_2628,plain,(
    ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2595])).

tff(c_2631,plain,
    ( ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2628])).

tff(c_2634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_44,c_689,c_38,c_2631])).

tff(c_2636,plain,(
    v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2595])).

tff(c_703,plain,(
    ! [C_125,A_126,B_127] :
      ( v5_pre_topc(C_125,A_126,B_127)
      | ~ v3_tops_2(C_125,A_126,B_127)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_126),u1_struct_0(B_127))))
      | ~ v1_funct_2(C_125,u1_struct_0(A_126),u1_struct_0(B_127))
      | ~ v1_funct_1(C_125)
      | ~ l1_pre_topc(B_127)
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_710,plain,(
    ! [C_125,B_127] :
      ( v5_pre_topc(C_125,'#skF_1',B_127)
      | ~ v3_tops_2(C_125,'#skF_1',B_127)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_127))))
      | ~ v1_funct_2(C_125,u1_struct_0('#skF_1'),u1_struct_0(B_127))
      | ~ v1_funct_1(C_125)
      | ~ l1_pre_topc(B_127)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_703])).

tff(c_2717,plain,(
    ! [C_345,B_346] :
      ( v5_pre_topc(C_345,'#skF_1',B_346)
      | ~ v3_tops_2(C_345,'#skF_1',B_346)
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_346))))
      | ~ v1_funct_2(C_345,k2_struct_0('#skF_1'),u1_struct_0(B_346))
      | ~ v1_funct_1(C_345)
      | ~ l1_pre_topc(B_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_710])).

tff(c_2727,plain,(
    ! [C_345] :
      ( v5_pre_topc(C_345,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_345,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_345,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_345)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2717])).

tff(c_2739,plain,(
    ! [C_348] :
      ( v5_pre_topc(C_348,'#skF_1','#skF_2')
      | ~ v3_tops_2(C_348,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_348,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_348) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_2727])).

tff(c_2742,plain,
    ( v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2530,c_2739])).

tff(c_2752,plain,(
    v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')),'#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2521,c_2520,c_2636,c_2742])).

tff(c_3206,plain,(
    ! [C_381,A_382,B_383] :
      ( v3_tops_2(C_381,A_382,B_383)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_382),u1_struct_0(B_383),C_381),B_383,A_382)
      | ~ v5_pre_topc(C_381,A_382,B_383)
      | ~ v2_funct_1(C_381)
      | k2_relset_1(u1_struct_0(A_382),u1_struct_0(B_383),C_381) != k2_struct_0(B_383)
      | k1_relset_1(u1_struct_0(A_382),u1_struct_0(B_383),C_381) != k2_struct_0(A_382)
      | ~ m1_subset_1(C_381,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_382),u1_struct_0(B_383))))
      | ~ v1_funct_2(C_381,u1_struct_0(A_382),u1_struct_0(B_383))
      | ~ v1_funct_1(C_381)
      | ~ l1_pre_topc(B_383)
      | ~ l1_pre_topc(A_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3210,plain,(
    ! [C_381,A_382] :
      ( v3_tops_2(C_381,A_382,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_382),k2_struct_0('#skF_1'),C_381),'#skF_1',A_382)
      | ~ v5_pre_topc(C_381,A_382,'#skF_1')
      | ~ v2_funct_1(C_381)
      | k2_relset_1(u1_struct_0(A_382),u1_struct_0('#skF_1'),C_381) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_382),u1_struct_0('#skF_1'),C_381) != k2_struct_0(A_382)
      | ~ m1_subset_1(C_381,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_382),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_381,u1_struct_0(A_382),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(C_381)
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_382) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_3206])).

tff(c_4382,plain,(
    ! [C_489,A_490] :
      ( v3_tops_2(C_489,A_490,'#skF_1')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_490),k2_struct_0('#skF_1'),C_489),'#skF_1',A_490)
      | ~ v5_pre_topc(C_489,A_490,'#skF_1')
      | ~ v2_funct_1(C_489)
      | k2_relset_1(u1_struct_0(A_490),k2_struct_0('#skF_1'),C_489) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0(A_490),k2_struct_0('#skF_1'),C_489) != k2_struct_0(A_490)
      | ~ m1_subset_1(C_489,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_490),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_489,u1_struct_0(A_490),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_489)
      | ~ l1_pre_topc(A_490) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65,c_65,c_65,c_65,c_3210])).

tff(c_4386,plain,(
    ! [C_489] :
      ( v3_tops_2(C_489,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_489),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_489,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_489)
      | k2_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_489) != k2_struct_0('#skF_1')
      | k1_relset_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_489) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_489,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_489,u1_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_489)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_4382])).

tff(c_4391,plain,(
    ! [C_491] :
      ( v3_tops_2(C_491,'#skF_2','#skF_1')
      | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_491),'#skF_1','#skF_2')
      | ~ v5_pre_topc(C_491,'#skF_2','#skF_1')
      | ~ v2_funct_1(C_491)
      | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_491) != k2_struct_0('#skF_1')
      | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),C_491) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
      | ~ v1_funct_2(C_491,k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
      | ~ v1_funct_1(C_491) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64,c_64,c_64,c_64,c_4386])).

tff(c_4394,plain,
    ( v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_1','#skF_2')
    | ~ v5_pre_topc(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_701,c_4391])).

tff(c_4401,plain,(
    v3_tops_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_691,c_3735,c_1721,c_2503,c_3379,c_2752,c_2502,c_4394])).

tff(c_4403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_693,c_4401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.69/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.69/2.33  
% 6.69/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.69/2.34  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.69/2.34  
% 6.69/2.34  %Foreground sorts:
% 6.69/2.34  
% 6.69/2.34  
% 6.69/2.34  %Background operators:
% 6.69/2.34  
% 6.69/2.34  
% 6.69/2.34  %Foreground operators:
% 6.69/2.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.69/2.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.69/2.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.69/2.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.69/2.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.69/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.69/2.34  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 6.69/2.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.69/2.34  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 6.69/2.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.69/2.34  tff('#skF_2', type, '#skF_2': $i).
% 6.69/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.69/2.34  tff('#skF_1', type, '#skF_1': $i).
% 6.69/2.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.69/2.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.69/2.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.69/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.69/2.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.69/2.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.69/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.69/2.34  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 6.69/2.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.69/2.34  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.69/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.69/2.34  
% 6.92/2.38  tff(f_154, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 6.92/2.38  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.92/2.38  tff(f_41, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 6.92/2.38  tff(f_57, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 6.92/2.38  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 6.92/2.38  tff(f_93, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 6.92/2.38  tff(f_134, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 6.92/2.38  tff(f_116, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 6.92/2.38  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.92/2.38  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 6.92/2.38  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.92/2.38  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.92/2.38  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.92/2.38  tff(c_52, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.92/2.38  tff(c_57, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_pre_topc(A_40))), inference(resolution, [status(thm)], [c_8, c_52])).
% 6.92/2.38  tff(c_65, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_57])).
% 6.92/2.38  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.92/2.38  tff(c_64, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_57])).
% 6.92/2.38  tff(c_42, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.92/2.38  tff(c_67, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_42])).
% 6.92/2.38  tff(c_76, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_67])).
% 6.92/2.38  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.92/2.38  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_40])).
% 6.92/2.38  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_66])).
% 6.92/2.38  tff(c_137, plain, (![A_57, B_58, C_59]: (k2_tops_2(A_57, B_58, C_59)=k2_funct_1(C_59) | ~v2_funct_1(C_59) | k2_relset_1(A_57, B_58, C_59)!=B_58 | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_2(C_59, A_57, B_58) | ~v1_funct_1(C_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.92/2.38  tff(c_143, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_137])).
% 6.92/2.38  tff(c_147, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_143])).
% 6.92/2.38  tff(c_148, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_147])).
% 6.92/2.38  tff(c_38, plain, (v3_tops_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.92/2.38  tff(c_481, plain, (![A_102, B_103, C_104]: (k2_relset_1(u1_struct_0(A_102), u1_struct_0(B_103), C_104)=k2_struct_0(B_103) | ~v3_tops_2(C_104, A_102, B_103) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102), u1_struct_0(B_103)))) | ~v1_funct_2(C_104, u1_struct_0(A_102), u1_struct_0(B_103)) | ~v1_funct_1(C_104) | ~l1_pre_topc(B_103) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.92/2.38  tff(c_497, plain, (![A_102, C_104]: (k2_relset_1(u1_struct_0(A_102), u1_struct_0('#skF_2'), C_104)=k2_struct_0('#skF_2') | ~v3_tops_2(C_104, A_102, '#skF_2') | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_104, u1_struct_0(A_102), u1_struct_0('#skF_2')) | ~v1_funct_1(C_104) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_102))), inference(superposition, [status(thm), theory('equality')], [c_64, c_481])).
% 6.92/2.38  tff(c_567, plain, (![A_112, C_113]: (k2_relset_1(u1_struct_0(A_112), k2_struct_0('#skF_2'), C_113)=k2_struct_0('#skF_2') | ~v3_tops_2(C_113, A_112, '#skF_2') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_112), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_113, u1_struct_0(A_112), k2_struct_0('#skF_2')) | ~v1_funct_1(C_113) | ~l1_pre_topc(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_64, c_497])).
% 6.92/2.38  tff(c_574, plain, (![C_113]: (k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_113)=k2_struct_0('#skF_2') | ~v3_tops_2(C_113, '#skF_1', '#skF_2') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_113, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_113) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_567])).
% 6.92/2.38  tff(c_583, plain, (![C_114]: (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_114)=k2_struct_0('#skF_2') | ~v3_tops_2(C_114, '#skF_1', '#skF_2') | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_114, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_114))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_65, c_574])).
% 6.92/2.38  tff(c_590, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_583])).
% 6.92/2.38  tff(c_594, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_38, c_590])).
% 6.92/2.38  tff(c_596, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_594])).
% 6.92/2.38  tff(c_597, plain, (~v2_funct_1('#skF_3') | k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_147])).
% 6.92/2.38  tff(c_629, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_597])).
% 6.92/2.38  tff(c_603, plain, (![C_115, A_116, B_117]: (v2_funct_1(C_115) | ~v3_tops_2(C_115, A_116, B_117) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116), u1_struct_0(B_117)))) | ~v1_funct_2(C_115, u1_struct_0(A_116), u1_struct_0(B_117)) | ~v1_funct_1(C_115) | ~l1_pre_topc(B_117) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.92/2.38  tff(c_610, plain, (![C_115, B_117]: (v2_funct_1(C_115) | ~v3_tops_2(C_115, '#skF_1', B_117) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_117)))) | ~v1_funct_2(C_115, u1_struct_0('#skF_1'), u1_struct_0(B_117)) | ~v1_funct_1(C_115) | ~l1_pre_topc(B_117) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_603])).
% 6.92/2.38  tff(c_658, plain, (![C_122, B_123]: (v2_funct_1(C_122) | ~v3_tops_2(C_122, '#skF_1', B_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_123)))) | ~v1_funct_2(C_122, k2_struct_0('#skF_1'), u1_struct_0(B_123)) | ~v1_funct_1(C_122) | ~l1_pre_topc(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_610])).
% 6.92/2.38  tff(c_668, plain, (![C_122]: (v2_funct_1(C_122) | ~v3_tops_2(C_122, '#skF_1', '#skF_2') | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_122, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_122) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_658])).
% 6.92/2.38  tff(c_674, plain, (![C_124]: (v2_funct_1(C_124) | ~v3_tops_2(C_124, '#skF_1', '#skF_2') | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_124, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_124))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_668])).
% 6.92/2.38  tff(c_681, plain, (v2_funct_1('#skF_3') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_674])).
% 6.92/2.38  tff(c_685, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_38, c_681])).
% 6.92/2.38  tff(c_687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_629, c_685])).
% 6.92/2.38  tff(c_688, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_597])).
% 6.92/2.38  tff(c_36, plain, (~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.92/2.38  tff(c_83, plain, (~v3_tops_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_64, c_36])).
% 6.92/2.38  tff(c_693, plain, (~v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_83])).
% 6.92/2.38  tff(c_101, plain, (![A_45, B_46, C_47]: (v1_funct_1(k2_tops_2(A_45, B_46, C_47)) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(C_47, A_45, B_46) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.92/2.38  tff(c_104, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_101])).
% 6.92/2.38  tff(c_107, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_104])).
% 6.92/2.38  tff(c_692, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_107])).
% 6.92/2.38  tff(c_108, plain, (![A_48, B_49, C_50]: (v1_funct_2(k2_tops_2(A_48, B_49, C_50), B_49, A_48) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_2(C_50, A_48, B_49) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.92/2.38  tff(c_110, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_108])).
% 6.92/2.38  tff(c_113, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_110])).
% 6.92/2.38  tff(c_691, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_113])).
% 6.92/2.38  tff(c_598, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_147])).
% 6.92/2.38  tff(c_689, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_597])).
% 6.92/2.38  tff(c_2778, plain, (![A_351, B_352, C_353]: (v2_funct_1(k2_tops_2(u1_struct_0(A_351), u1_struct_0(B_352), C_353)) | ~v2_funct_1(C_353) | k2_relset_1(u1_struct_0(A_351), u1_struct_0(B_352), C_353)!=k2_struct_0(B_352) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_351), u1_struct_0(B_352)))) | ~v1_funct_2(C_353, u1_struct_0(A_351), u1_struct_0(B_352)) | ~v1_funct_1(C_353) | ~l1_struct_0(B_352) | ~l1_struct_0(A_351))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.92/2.38  tff(c_2788, plain, (![A_351, C_353]: (v2_funct_1(k2_tops_2(u1_struct_0(A_351), u1_struct_0('#skF_1'), C_353)) | ~v2_funct_1(C_353) | k2_relset_1(u1_struct_0(A_351), u1_struct_0('#skF_1'), C_353)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_351), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_353, u1_struct_0(A_351), u1_struct_0('#skF_1')) | ~v1_funct_1(C_353) | ~l1_struct_0('#skF_1') | ~l1_struct_0(A_351))), inference(superposition, [status(thm), theory('equality')], [c_65, c_2778])).
% 6.92/2.38  tff(c_2797, plain, (![A_351, C_353]: (v2_funct_1(k2_tops_2(u1_struct_0(A_351), k2_struct_0('#skF_1'), C_353)) | ~v2_funct_1(C_353) | k2_relset_1(u1_struct_0(A_351), k2_struct_0('#skF_1'), C_353)!=k2_struct_0('#skF_1') | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_351), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_353, u1_struct_0(A_351), k2_struct_0('#skF_1')) | ~v1_funct_1(C_353) | ~l1_struct_0('#skF_1') | ~l1_struct_0(A_351))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_65, c_2788])).
% 6.92/2.38  tff(c_3508, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2797])).
% 6.92/2.38  tff(c_3511, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_3508])).
% 6.92/2.38  tff(c_3515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_3511])).
% 6.92/2.38  tff(c_3517, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_2797])).
% 6.92/2.38  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.92/2.38  tff(c_2897, plain, (![B_360, A_361, C_362]: (k1_relset_1(u1_struct_0(B_360), u1_struct_0(A_361), k2_tops_2(u1_struct_0(A_361), u1_struct_0(B_360), C_362))=k2_struct_0(B_360) | ~v2_funct_1(C_362) | k2_relset_1(u1_struct_0(A_361), u1_struct_0(B_360), C_362)!=k2_struct_0(B_360) | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361), u1_struct_0(B_360)))) | ~v1_funct_2(C_362, u1_struct_0(A_361), u1_struct_0(B_360)) | ~v1_funct_1(C_362) | ~l1_struct_0(B_360) | v2_struct_0(B_360) | ~l1_struct_0(A_361))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.92/2.38  tff(c_2918, plain, (![A_361, C_362]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_361), k2_tops_2(u1_struct_0(A_361), u1_struct_0('#skF_2'), C_362))=k2_struct_0('#skF_2') | ~v2_funct_1(C_362) | k2_relset_1(u1_struct_0(A_361), u1_struct_0('#skF_2'), C_362)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_362, u1_struct_0(A_361), u1_struct_0('#skF_2')) | ~v1_funct_1(C_362) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_361))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2897])).
% 6.92/2.38  tff(c_2934, plain, (![A_361, C_362]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_361), k2_tops_2(u1_struct_0(A_361), k2_struct_0('#skF_2'), C_362))=k2_struct_0('#skF_2') | ~v2_funct_1(C_362) | k2_relset_1(u1_struct_0(A_361), k2_struct_0('#skF_2'), C_362)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_362, u1_struct_0(A_361), k2_struct_0('#skF_2')) | ~v1_funct_1(C_362) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_361))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_64, c_2918])).
% 6.92/2.38  tff(c_2935, plain, (![A_361, C_362]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_361), k2_tops_2(u1_struct_0(A_361), k2_struct_0('#skF_2'), C_362))=k2_struct_0('#skF_2') | ~v2_funct_1(C_362) | k2_relset_1(u1_struct_0(A_361), k2_struct_0('#skF_2'), C_362)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_362, u1_struct_0(A_361), k2_struct_0('#skF_2')) | ~v1_funct_1(C_362) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_361))), inference(negUnitSimplification, [status(thm)], [c_48, c_2934])).
% 6.92/2.38  tff(c_2984, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2935])).
% 6.92/2.38  tff(c_2987, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_2984])).
% 6.92/2.38  tff(c_2991, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2987])).
% 6.92/2.38  tff(c_2993, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2935])).
% 6.92/2.38  tff(c_2927, plain, (![A_361, C_362]: (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_361), k2_tops_2(u1_struct_0(A_361), k2_struct_0('#skF_2'), C_362))=k2_struct_0('#skF_2') | ~v2_funct_1(C_362) | k2_relset_1(u1_struct_0(A_361), u1_struct_0('#skF_2'), C_362)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_362, u1_struct_0(A_361), u1_struct_0('#skF_2')) | ~v1_funct_1(C_362) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_361))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2897])).
% 6.92/2.38  tff(c_2938, plain, (![A_361, C_362]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_361), k2_tops_2(u1_struct_0(A_361), k2_struct_0('#skF_2'), C_362))=k2_struct_0('#skF_2') | ~v2_funct_1(C_362) | k2_relset_1(u1_struct_0(A_361), k2_struct_0('#skF_2'), C_362)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_362, u1_struct_0(A_361), k2_struct_0('#skF_2')) | ~v1_funct_1(C_362) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_361))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_64, c_2927])).
% 6.92/2.38  tff(c_2939, plain, (![A_361, C_362]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_361), k2_tops_2(u1_struct_0(A_361), k2_struct_0('#skF_2'), C_362))=k2_struct_0('#skF_2') | ~v2_funct_1(C_362) | k2_relset_1(u1_struct_0(A_361), k2_struct_0('#skF_2'), C_362)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_361), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_362, u1_struct_0(A_361), k2_struct_0('#skF_2')) | ~v1_funct_1(C_362) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_361))), inference(negUnitSimplification, [status(thm)], [c_48, c_2938])).
% 6.92/2.38  tff(c_3382, plain, (![A_401, C_402]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_401), k2_tops_2(u1_struct_0(A_401), k2_struct_0('#skF_2'), C_402))=k2_struct_0('#skF_2') | ~v2_funct_1(C_402) | k2_relset_1(u1_struct_0(A_401), k2_struct_0('#skF_2'), C_402)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_401), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_402, u1_struct_0(A_401), k2_struct_0('#skF_2')) | ~v1_funct_1(C_402) | ~l1_struct_0(A_401))), inference(demodulation, [status(thm), theory('equality')], [c_2993, c_2939])).
% 6.92/2.38  tff(c_3391, plain, (![C_402]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_402))=k2_struct_0('#skF_2') | ~v2_funct_1(C_402) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_402)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_402, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_402) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_3382])).
% 6.92/2.38  tff(c_3403, plain, (![C_402]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_402))=k2_struct_0('#skF_2') | ~v2_funct_1(C_402) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_402)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_402, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_402) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_65, c_65, c_3391])).
% 6.92/2.38  tff(c_3717, plain, (![C_438]: (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_438))=k2_struct_0('#skF_2') | ~v2_funct_1(C_438) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_438)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_438, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_438, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_438))), inference(demodulation, [status(thm), theory('equality')], [c_3517, c_3403])).
% 6.92/2.38  tff(c_3729, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_688, c_3717])).
% 6.92/2.38  tff(c_3735, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_78, c_598, c_689, c_3729])).
% 6.92/2.38  tff(c_24, plain, (![A_17, B_18, C_19]: (m1_subset_1(k2_tops_2(A_17, B_18, C_19), k1_zfmisc_1(k2_zfmisc_1(B_18, A_17))) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.92/2.38  tff(c_697, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_688, c_24])).
% 6.92/2.38  tff(c_701, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_78, c_697])).
% 6.92/2.38  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_tops_2(A_7, B_8, C_9)=k2_funct_1(C_9) | ~v2_funct_1(C_9) | k2_relset_1(A_7, B_8, C_9)!=B_8 | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(C_9, A_7, B_8) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.92/2.38  tff(c_747, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_701, c_10])).
% 6.92/2.38  tff(c_761, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_692, c_691, c_747])).
% 6.92/2.38  tff(c_817, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_761])).
% 6.92/2.38  tff(c_1271, plain, (![B_190, A_191, C_192]: (k2_relset_1(u1_struct_0(B_190), u1_struct_0(A_191), k2_tops_2(u1_struct_0(A_191), u1_struct_0(B_190), C_192))=k2_struct_0(A_191) | ~v2_funct_1(C_192) | k2_relset_1(u1_struct_0(A_191), u1_struct_0(B_190), C_192)!=k2_struct_0(B_190) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191), u1_struct_0(B_190)))) | ~v1_funct_2(C_192, u1_struct_0(A_191), u1_struct_0(B_190)) | ~v1_funct_1(C_192) | ~l1_struct_0(B_190) | v2_struct_0(B_190) | ~l1_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.92/2.38  tff(c_1292, plain, (![A_191, C_192]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_191), k2_tops_2(u1_struct_0(A_191), u1_struct_0('#skF_2'), C_192))=k2_struct_0(A_191) | ~v2_funct_1(C_192) | k2_relset_1(u1_struct_0(A_191), u1_struct_0('#skF_2'), C_192)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_192, u1_struct_0(A_191), u1_struct_0('#skF_2')) | ~v1_funct_1(C_192) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_191))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1271])).
% 6.92/2.38  tff(c_1308, plain, (![A_191, C_192]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_191), k2_tops_2(u1_struct_0(A_191), k2_struct_0('#skF_2'), C_192))=k2_struct_0(A_191) | ~v2_funct_1(C_192) | k2_relset_1(u1_struct_0(A_191), k2_struct_0('#skF_2'), C_192)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_192, u1_struct_0(A_191), k2_struct_0('#skF_2')) | ~v1_funct_1(C_192) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_64, c_1292])).
% 6.92/2.38  tff(c_1309, plain, (![A_191, C_192]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_191), k2_tops_2(u1_struct_0(A_191), k2_struct_0('#skF_2'), C_192))=k2_struct_0(A_191) | ~v2_funct_1(C_192) | k2_relset_1(u1_struct_0(A_191), k2_struct_0('#skF_2'), C_192)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_192, u1_struct_0(A_191), k2_struct_0('#skF_2')) | ~v1_funct_1(C_192) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_191))), inference(negUnitSimplification, [status(thm)], [c_48, c_1308])).
% 6.92/2.38  tff(c_1345, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1309])).
% 6.92/2.38  tff(c_1348, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_1345])).
% 6.92/2.38  tff(c_1352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1348])).
% 6.92/2.38  tff(c_1354, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_1309])).
% 6.92/2.38  tff(c_1144, plain, (![A_174, B_175, C_176]: (v2_funct_1(k2_tops_2(u1_struct_0(A_174), u1_struct_0(B_175), C_176)) | ~v2_funct_1(C_176) | k2_relset_1(u1_struct_0(A_174), u1_struct_0(B_175), C_176)!=k2_struct_0(B_175) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_174), u1_struct_0(B_175)))) | ~v1_funct_2(C_176, u1_struct_0(A_174), u1_struct_0(B_175)) | ~v1_funct_1(C_176) | ~l1_struct_0(B_175) | ~l1_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.92/2.38  tff(c_1160, plain, (![A_174, C_176]: (v2_funct_1(k2_tops_2(u1_struct_0(A_174), u1_struct_0('#skF_2'), C_176)) | ~v2_funct_1(C_176) | k2_relset_1(u1_struct_0(A_174), u1_struct_0('#skF_2'), C_176)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_174), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_176, u1_struct_0(A_174), u1_struct_0('#skF_2')) | ~v1_funct_1(C_176) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_174))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1144])).
% 6.92/2.38  tff(c_1165, plain, (![A_174, C_176]: (v2_funct_1(k2_tops_2(u1_struct_0(A_174), k2_struct_0('#skF_2'), C_176)) | ~v2_funct_1(C_176) | k2_relset_1(u1_struct_0(A_174), k2_struct_0('#skF_2'), C_176)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_174), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_176, u1_struct_0(A_174), k2_struct_0('#skF_2')) | ~v1_funct_1(C_176) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_1160])).
% 6.92/2.38  tff(c_1514, plain, (![A_217, C_218]: (v2_funct_1(k2_tops_2(u1_struct_0(A_217), k2_struct_0('#skF_2'), C_218)) | ~v2_funct_1(C_218) | k2_relset_1(u1_struct_0(A_217), k2_struct_0('#skF_2'), C_218)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_217), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_218, u1_struct_0(A_217), k2_struct_0('#skF_2')) | ~v1_funct_1(C_218) | ~l1_struct_0(A_217))), inference(demodulation, [status(thm), theory('equality')], [c_1354, c_1165])).
% 6.92/2.38  tff(c_1521, plain, (![C_218]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_218)) | ~v2_funct_1(C_218) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_218)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_218, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_218) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1514])).
% 6.92/2.38  tff(c_1526, plain, (![C_218]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_218)) | ~v2_funct_1(C_218) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_218)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_218, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_218) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_65, c_1521])).
% 6.92/2.38  tff(c_1552, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1526])).
% 6.92/2.38  tff(c_1555, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_1552])).
% 6.92/2.38  tff(c_1559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1555])).
% 6.92/2.38  tff(c_1561, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_1526])).
% 6.92/2.38  tff(c_1301, plain, (![A_191, C_192]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_191), k2_tops_2(u1_struct_0(A_191), k2_struct_0('#skF_2'), C_192))=k2_struct_0(A_191) | ~v2_funct_1(C_192) | k2_relset_1(u1_struct_0(A_191), u1_struct_0('#skF_2'), C_192)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_192, u1_struct_0(A_191), u1_struct_0('#skF_2')) | ~v1_funct_1(C_192) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_191))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1271])).
% 6.92/2.38  tff(c_1312, plain, (![A_191, C_192]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_191), k2_tops_2(u1_struct_0(A_191), k2_struct_0('#skF_2'), C_192))=k2_struct_0(A_191) | ~v2_funct_1(C_192) | k2_relset_1(u1_struct_0(A_191), k2_struct_0('#skF_2'), C_192)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_192, u1_struct_0(A_191), k2_struct_0('#skF_2')) | ~v1_funct_1(C_192) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_191))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_64, c_1301])).
% 6.92/2.38  tff(c_1313, plain, (![A_191, C_192]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_191), k2_tops_2(u1_struct_0(A_191), k2_struct_0('#skF_2'), C_192))=k2_struct_0(A_191) | ~v2_funct_1(C_192) | k2_relset_1(u1_struct_0(A_191), k2_struct_0('#skF_2'), C_192)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_191), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_192, u1_struct_0(A_191), k2_struct_0('#skF_2')) | ~v1_funct_1(C_192) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_191))), inference(negUnitSimplification, [status(thm)], [c_48, c_1312])).
% 6.92/2.38  tff(c_1666, plain, (![A_235, C_236]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_235), k2_tops_2(u1_struct_0(A_235), k2_struct_0('#skF_2'), C_236))=k2_struct_0(A_235) | ~v2_funct_1(C_236) | k2_relset_1(u1_struct_0(A_235), k2_struct_0('#skF_2'), C_236)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_236, u1_struct_0(A_235), k2_struct_0('#skF_2')) | ~v1_funct_1(C_236) | ~l1_struct_0(A_235))), inference(demodulation, [status(thm), theory('equality')], [c_1354, c_1313])).
% 6.92/2.38  tff(c_1675, plain, (![C_236]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_236))=k2_struct_0('#skF_1') | ~v2_funct_1(C_236) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_236)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_236, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_236) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1666])).
% 6.92/2.38  tff(c_1704, plain, (![C_238]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_238))=k2_struct_0('#skF_1') | ~v2_funct_1(C_238) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_238)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_238, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_238))), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_65, c_65, c_65, c_65, c_1675])).
% 6.92/2.38  tff(c_1713, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_688, c_1704])).
% 6.92/2.38  tff(c_1717, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_78, c_598, c_689, c_1713])).
% 6.92/2.38  tff(c_1719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_817, c_1717])).
% 6.92/2.38  tff(c_1721, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_761])).
% 6.92/2.38  tff(c_1720, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_761])).
% 6.92/2.38  tff(c_1726, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1720])).
% 6.92/2.38  tff(c_2101, plain, (![B_284, A_285, C_286]: (k1_relset_1(u1_struct_0(B_284), u1_struct_0(A_285), k2_tops_2(u1_struct_0(A_285), u1_struct_0(B_284), C_286))=k2_struct_0(B_284) | ~v2_funct_1(C_286) | k2_relset_1(u1_struct_0(A_285), u1_struct_0(B_284), C_286)!=k2_struct_0(B_284) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285), u1_struct_0(B_284)))) | ~v1_funct_2(C_286, u1_struct_0(A_285), u1_struct_0(B_284)) | ~v1_funct_1(C_286) | ~l1_struct_0(B_284) | v2_struct_0(B_284) | ~l1_struct_0(A_285))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.92/2.38  tff(c_2122, plain, (![A_285, C_286]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_285), k2_tops_2(u1_struct_0(A_285), u1_struct_0('#skF_2'), C_286))=k2_struct_0('#skF_2') | ~v2_funct_1(C_286) | k2_relset_1(u1_struct_0(A_285), u1_struct_0('#skF_2'), C_286)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_286, u1_struct_0(A_285), u1_struct_0('#skF_2')) | ~v1_funct_1(C_286) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_285))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2101])).
% 6.92/2.38  tff(c_2138, plain, (![A_285, C_286]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_285), k2_tops_2(u1_struct_0(A_285), k2_struct_0('#skF_2'), C_286))=k2_struct_0('#skF_2') | ~v2_funct_1(C_286) | k2_relset_1(u1_struct_0(A_285), k2_struct_0('#skF_2'), C_286)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_286, u1_struct_0(A_285), k2_struct_0('#skF_2')) | ~v1_funct_1(C_286) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_285))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_64, c_2122])).
% 6.92/2.38  tff(c_2139, plain, (![A_285, C_286]: (k1_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_285), k2_tops_2(u1_struct_0(A_285), k2_struct_0('#skF_2'), C_286))=k2_struct_0('#skF_2') | ~v2_funct_1(C_286) | k2_relset_1(u1_struct_0(A_285), k2_struct_0('#skF_2'), C_286)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_286, u1_struct_0(A_285), k2_struct_0('#skF_2')) | ~v1_funct_1(C_286) | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_285))), inference(negUnitSimplification, [status(thm)], [c_48, c_2138])).
% 6.92/2.38  tff(c_2178, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2139])).
% 6.92/2.38  tff(c_2181, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_2178])).
% 6.92/2.38  tff(c_2185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2181])).
% 6.92/2.38  tff(c_2187, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2139])).
% 6.92/2.38  tff(c_1975, plain, (![A_269, B_270, C_271]: (v2_funct_1(k2_tops_2(u1_struct_0(A_269), u1_struct_0(B_270), C_271)) | ~v2_funct_1(C_271) | k2_relset_1(u1_struct_0(A_269), u1_struct_0(B_270), C_271)!=k2_struct_0(B_270) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_269), u1_struct_0(B_270)))) | ~v1_funct_2(C_271, u1_struct_0(A_269), u1_struct_0(B_270)) | ~v1_funct_1(C_271) | ~l1_struct_0(B_270) | ~l1_struct_0(A_269))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.92/2.38  tff(c_1982, plain, (![B_270, C_271]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_270), C_271)) | ~v2_funct_1(C_271) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_270), C_271)!=k2_struct_0(B_270) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_270)))) | ~v1_funct_2(C_271, u1_struct_0('#skF_1'), u1_struct_0(B_270)) | ~v1_funct_1(C_271) | ~l1_struct_0(B_270) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1975])).
% 6.92/2.38  tff(c_1993, plain, (![B_270, C_271]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_270), C_271)) | ~v2_funct_1(C_271) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_270), C_271)!=k2_struct_0(B_270) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_270)))) | ~v1_funct_2(C_271, k2_struct_0('#skF_1'), u1_struct_0(B_270)) | ~v1_funct_1(C_271) | ~l1_struct_0(B_270) | ~l1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_65, c_1982])).
% 6.92/2.38  tff(c_2438, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1993])).
% 6.92/2.38  tff(c_2441, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_2438])).
% 6.92/2.38  tff(c_2445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_2441])).
% 6.92/2.38  tff(c_2466, plain, (![B_327, C_328]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_327), C_328)) | ~v2_funct_1(C_328) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_327), C_328)!=k2_struct_0(B_327) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_327)))) | ~v1_funct_2(C_328, k2_struct_0('#skF_1'), u1_struct_0(B_327)) | ~v1_funct_1(C_328) | ~l1_struct_0(B_327))), inference(splitRight, [status(thm)], [c_1993])).
% 6.92/2.38  tff(c_2476, plain, (![C_328]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_328)) | ~v2_funct_1(C_328) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_328)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_328, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_328) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2466])).
% 6.92/2.38  tff(c_2488, plain, (![C_330]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_330)) | ~v2_funct_1(C_330) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_330)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_330, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_330))), inference(demodulation, [status(thm), theory('equality')], [c_2187, c_64, c_64, c_64, c_2476])).
% 6.92/2.38  tff(c_2495, plain, (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2488])).
% 6.92/2.38  tff(c_2499, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_598, c_689, c_688, c_2495])).
% 6.92/2.38  tff(c_2501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1726, c_2499])).
% 6.92/2.38  tff(c_2503, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1720])).
% 6.92/2.38  tff(c_2652, plain, (![A_337, B_338, C_339]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_337), u1_struct_0(B_338), C_339), B_338, A_337) | ~v3_tops_2(C_339, A_337, B_338) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_337), u1_struct_0(B_338)))) | ~v1_funct_2(C_339, u1_struct_0(A_337), u1_struct_0(B_338)) | ~v1_funct_1(C_339) | ~l1_pre_topc(B_338) | ~l1_pre_topc(A_337))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.92/2.38  tff(c_2663, plain, (![A_337, C_339]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_337), u1_struct_0('#skF_2'), C_339), '#skF_2', A_337) | ~v3_tops_2(C_339, A_337, '#skF_2') | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_337), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_339, u1_struct_0(A_337), u1_struct_0('#skF_2')) | ~v1_funct_1(C_339) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_337))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2652])).
% 6.92/2.38  tff(c_3349, plain, (![A_398, C_399]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_398), k2_struct_0('#skF_2'), C_399), '#skF_2', A_398) | ~v3_tops_2(C_399, A_398, '#skF_2') | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_398), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_399, u1_struct_0(A_398), k2_struct_0('#skF_2')) | ~v1_funct_1(C_399) | ~l1_pre_topc(A_398))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_64, c_2663])).
% 6.92/2.38  tff(c_3354, plain, (![C_399]: (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_399), '#skF_2', '#skF_1') | ~v3_tops_2(C_399, '#skF_1', '#skF_2') | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_399, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_399) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_3349])).
% 6.92/2.38  tff(c_3362, plain, (![C_400]: (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_400), '#skF_2', '#skF_1') | ~v3_tops_2(C_400, '#skF_1', '#skF_2') | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_400, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_400))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_65, c_3354])).
% 6.92/2.38  tff(c_3372, plain, (v5_pre_topc(k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3362])).
% 6.92/2.38  tff(c_3379, plain, (v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_38, c_688, c_3372])).
% 6.92/2.38  tff(c_2502, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1720])).
% 6.92/2.38  tff(c_28, plain, (![A_17, B_18, C_19]: (v1_funct_1(k2_tops_2(A_17, B_18, C_19)) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.92/2.38  tff(c_755, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_701, c_28])).
% 6.92/2.38  tff(c_770, plain, (v1_funct_1(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_692, c_691, c_755])).
% 6.92/2.38  tff(c_2521, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2502, c_770])).
% 6.92/2.38  tff(c_26, plain, (![A_17, B_18, C_19]: (v1_funct_2(k2_tops_2(A_17, B_18, C_19), B_18, A_17) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(C_19, A_17, B_18) | ~v1_funct_1(C_19))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.92/2.38  tff(c_752, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_701, c_26])).
% 6.92/2.38  tff(c_767, plain, (v1_funct_2(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_692, c_691, c_752])).
% 6.92/2.38  tff(c_2520, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2502, c_767])).
% 6.92/2.38  tff(c_4, plain, (![C_4, A_2, B_3]: (v1_relat_1(C_4) | ~m1_subset_1(C_4, k1_zfmisc_1(k2_zfmisc_1(A_2, B_3))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.92/2.38  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_4])).
% 6.92/2.38  tff(c_2, plain, (![A_1]: (k2_funct_1(k2_funct_1(A_1))=A_1 | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.92/2.38  tff(c_2526, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2502, c_24])).
% 6.92/2.38  tff(c_2530, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_692, c_691, c_701, c_2526])).
% 6.92/2.38  tff(c_619, plain, (![C_115, A_116]: (v2_funct_1(C_115) | ~v3_tops_2(C_115, A_116, '#skF_2') | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_115, u1_struct_0(A_116), u1_struct_0('#skF_2')) | ~v1_funct_1(C_115) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_116))), inference(superposition, [status(thm), theory('equality')], [c_64, c_603])).
% 6.92/2.38  tff(c_729, plain, (![C_128, A_129]: (v2_funct_1(C_128) | ~v3_tops_2(C_128, A_129, '#skF_2') | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_129), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_128, u1_struct_0(A_129), k2_struct_0('#skF_2')) | ~v1_funct_1(C_128) | ~l1_pre_topc(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_619])).
% 6.92/2.38  tff(c_736, plain, (![C_128]: (v2_funct_1(C_128) | ~v3_tops_2(C_128, '#skF_1', '#skF_2') | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_128, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_128) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_729])).
% 6.92/2.38  tff(c_742, plain, (![C_128]: (v2_funct_1(C_128) | ~v3_tops_2(C_128, '#skF_1', '#skF_2') | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_128, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_128))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_736])).
% 6.92/2.38  tff(c_2575, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2530, c_742])).
% 6.92/2.38  tff(c_2595, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2521, c_2520, c_2575])).
% 6.92/2.38  tff(c_2628, plain, (~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_2595])).
% 6.92/2.38  tff(c_2631, plain, (~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_2628])).
% 6.92/2.38  tff(c_2634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_44, c_689, c_38, c_2631])).
% 6.92/2.38  tff(c_2636, plain, (v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_2595])).
% 6.92/2.38  tff(c_703, plain, (![C_125, A_126, B_127]: (v5_pre_topc(C_125, A_126, B_127) | ~v3_tops_2(C_125, A_126, B_127) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_126), u1_struct_0(B_127)))) | ~v1_funct_2(C_125, u1_struct_0(A_126), u1_struct_0(B_127)) | ~v1_funct_1(C_125) | ~l1_pre_topc(B_127) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.92/2.38  tff(c_710, plain, (![C_125, B_127]: (v5_pre_topc(C_125, '#skF_1', B_127) | ~v3_tops_2(C_125, '#skF_1', B_127) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_127)))) | ~v1_funct_2(C_125, u1_struct_0('#skF_1'), u1_struct_0(B_127)) | ~v1_funct_1(C_125) | ~l1_pre_topc(B_127) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_703])).
% 6.92/2.38  tff(c_2717, plain, (![C_345, B_346]: (v5_pre_topc(C_345, '#skF_1', B_346) | ~v3_tops_2(C_345, '#skF_1', B_346) | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_346)))) | ~v1_funct_2(C_345, k2_struct_0('#skF_1'), u1_struct_0(B_346)) | ~v1_funct_1(C_345) | ~l1_pre_topc(B_346))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_710])).
% 6.92/2.38  tff(c_2727, plain, (![C_345]: (v5_pre_topc(C_345, '#skF_1', '#skF_2') | ~v3_tops_2(C_345, '#skF_1', '#skF_2') | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_345, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_345) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2717])).
% 6.92/2.38  tff(c_2739, plain, (![C_348]: (v5_pre_topc(C_348, '#skF_1', '#skF_2') | ~v3_tops_2(C_348, '#skF_1', '#skF_2') | ~m1_subset_1(C_348, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_348, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_348))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_2727])).
% 6.92/2.38  tff(c_2742, plain, (v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v3_tops_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2530, c_2739])).
% 6.92/2.38  tff(c_2752, plain, (v5_pre_topc(k2_funct_1(k2_funct_1('#skF_3')), '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2521, c_2520, c_2636, c_2742])).
% 6.92/2.38  tff(c_3206, plain, (![C_381, A_382, B_383]: (v3_tops_2(C_381, A_382, B_383) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_382), u1_struct_0(B_383), C_381), B_383, A_382) | ~v5_pre_topc(C_381, A_382, B_383) | ~v2_funct_1(C_381) | k2_relset_1(u1_struct_0(A_382), u1_struct_0(B_383), C_381)!=k2_struct_0(B_383) | k1_relset_1(u1_struct_0(A_382), u1_struct_0(B_383), C_381)!=k2_struct_0(A_382) | ~m1_subset_1(C_381, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_382), u1_struct_0(B_383)))) | ~v1_funct_2(C_381, u1_struct_0(A_382), u1_struct_0(B_383)) | ~v1_funct_1(C_381) | ~l1_pre_topc(B_383) | ~l1_pre_topc(A_382))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.92/2.38  tff(c_3210, plain, (![C_381, A_382]: (v3_tops_2(C_381, A_382, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_382), k2_struct_0('#skF_1'), C_381), '#skF_1', A_382) | ~v5_pre_topc(C_381, A_382, '#skF_1') | ~v2_funct_1(C_381) | k2_relset_1(u1_struct_0(A_382), u1_struct_0('#skF_1'), C_381)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_382), u1_struct_0('#skF_1'), C_381)!=k2_struct_0(A_382) | ~m1_subset_1(C_381, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_382), u1_struct_0('#skF_1')))) | ~v1_funct_2(C_381, u1_struct_0(A_382), u1_struct_0('#skF_1')) | ~v1_funct_1(C_381) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_382))), inference(superposition, [status(thm), theory('equality')], [c_65, c_3206])).
% 6.92/2.38  tff(c_4382, plain, (![C_489, A_490]: (v3_tops_2(C_489, A_490, '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_490), k2_struct_0('#skF_1'), C_489), '#skF_1', A_490) | ~v5_pre_topc(C_489, A_490, '#skF_1') | ~v2_funct_1(C_489) | k2_relset_1(u1_struct_0(A_490), k2_struct_0('#skF_1'), C_489)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0(A_490), k2_struct_0('#skF_1'), C_489)!=k2_struct_0(A_490) | ~m1_subset_1(C_489, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_490), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_489, u1_struct_0(A_490), k2_struct_0('#skF_1')) | ~v1_funct_1(C_489) | ~l1_pre_topc(A_490))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_65, c_65, c_65, c_65, c_3210])).
% 6.92/2.38  tff(c_4386, plain, (![C_489]: (v3_tops_2(C_489, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_489), '#skF_1', '#skF_2') | ~v5_pre_topc(C_489, '#skF_2', '#skF_1') | ~v2_funct_1(C_489) | k2_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_489)!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_489)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_489, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_489, u1_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_489) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_4382])).
% 6.92/2.38  tff(c_4391, plain, (![C_491]: (v3_tops_2(C_491, '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_491), '#skF_1', '#skF_2') | ~v5_pre_topc(C_491, '#skF_2', '#skF_1') | ~v2_funct_1(C_491) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_491)!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), C_491)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_491, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1')))) | ~v1_funct_2(C_491, k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(C_491))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64, c_64, c_64, c_64, c_4386])).
% 6.92/2.38  tff(c_4394, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_1', '#skF_2') | ~v5_pre_topc(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_701, c_4391])).
% 6.92/2.38  tff(c_4401, plain, (v3_tops_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_692, c_691, c_3735, c_1721, c_2503, c_3379, c_2752, c_2502, c_4394])).
% 6.92/2.38  tff(c_4403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_693, c_4401])).
% 6.92/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.92/2.38  
% 6.92/2.38  Inference rules
% 6.92/2.38  ----------------------
% 6.92/2.38  #Ref     : 0
% 6.92/2.38  #Sup     : 837
% 6.92/2.38  #Fact    : 0
% 6.92/2.38  #Define  : 0
% 6.92/2.38  #Split   : 13
% 6.92/2.38  #Chain   : 0
% 6.92/2.38  #Close   : 0
% 6.92/2.38  
% 6.92/2.38  Ordering : KBO
% 6.92/2.38  
% 6.92/2.38  Simplification rules
% 6.92/2.38  ----------------------
% 6.92/2.38  #Subsume      : 149
% 6.92/2.38  #Demod        : 2350
% 6.92/2.38  #Tautology    : 164
% 6.92/2.38  #SimpNegUnit  : 27
% 6.92/2.38  #BackRed      : 15
% 6.92/2.38  
% 6.92/2.38  #Partial instantiations: 0
% 6.92/2.38  #Strategies tried      : 1
% 6.92/2.38  
% 6.92/2.38  Timing (in seconds)
% 6.92/2.38  ----------------------
% 6.92/2.38  Preprocessing        : 0.34
% 6.92/2.38  Parsing              : 0.18
% 6.92/2.38  CNF conversion       : 0.03
% 6.92/2.38  Main loop            : 1.24
% 6.92/2.38  Inferencing          : 0.41
% 6.92/2.38  Reduction            : 0.49
% 6.92/2.38  Demodulation         : 0.37
% 6.92/2.38  BG Simplification    : 0.05
% 6.92/2.38  Subsumption          : 0.21
% 6.92/2.38  Abstraction          : 0.06
% 6.92/2.38  MUC search           : 0.00
% 6.92/2.38  Cooper               : 0.00
% 6.92/2.38  Total                : 1.65
% 6.92/2.38  Index Insertion      : 0.00
% 6.92/2.38  Index Deletion       : 0.00
% 6.92/2.38  Index Matching       : 0.00
% 6.92/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
