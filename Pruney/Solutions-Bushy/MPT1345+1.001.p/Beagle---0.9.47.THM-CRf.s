%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1345+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:50 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  106 (1322 expanded)
%              Number of leaves         :   31 ( 552 expanded)
%              Depth                    :   16
%              Number of atoms          :  365 (6329 expanded)
%              Number of equality atoms :   45 ( 293 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v3_tops_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
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

tff(f_121,axiom,(
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

tff(f_103,axiom,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_142,axiom,(
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
               => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_20,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_36,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_111,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(u1_struct_0(A_64),u1_struct_0(B_65),C_66) = k2_struct_0(B_65)
      | ~ v3_tops_2(C_66,A_64,B_65)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64),u1_struct_0(B_65))))
      | ~ v1_funct_2(C_66,u1_struct_0(A_64),u1_struct_0(B_65))
      | ~ v1_funct_1(C_66)
      | ~ l1_pre_topc(B_65)
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_118,plain,
    ( k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_122,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_40,c_36,c_118])).

tff(c_80,plain,(
    ! [C_54,A_55,B_56] :
      ( v2_funct_1(C_54)
      | ~ v3_tops_2(C_54,A_55,B_56)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_55),u1_struct_0(B_56))))
      | ~ v1_funct_2(C_54,u1_struct_0(A_55),u1_struct_0(B_56))
      | ~ v1_funct_1(C_54)
      | ~ l1_pre_topc(B_56)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_87,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_80])).

tff(c_91,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_40,c_36,c_87])).

tff(c_162,plain,(
    ! [A_76,B_77,C_78] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_76),u1_struct_0(B_77),C_78))
      | ~ v2_funct_1(C_78)
      | k2_relset_1(u1_struct_0(A_76),u1_struct_0(B_77),C_78) != k2_struct_0(B_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_76),u1_struct_0(B_77))))
      | ~ v1_funct_2(C_78,u1_struct_0(A_76),u1_struct_0(B_77))
      | ~ v1_funct_1(C_78)
      | ~ l1_struct_0(B_77)
      | ~ l1_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_169,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_162])).

tff(c_173,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_122,c_91,c_169])).

tff(c_174,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_177,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_174])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_177])).

tff(c_183,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_182,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_184,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_187,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_187])).

tff(c_193,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_28,plain,(
    ! [B_20,A_16,C_22] :
      ( k1_relset_1(u1_struct_0(B_20),u1_struct_0(A_16),k2_tops_2(u1_struct_0(A_16),u1_struct_0(B_20),C_22)) = k2_struct_0(B_20)
      | ~ v2_funct_1(C_22)
      | k2_relset_1(u1_struct_0(A_16),u1_struct_0(B_20),C_22) != k2_struct_0(B_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16),u1_struct_0(B_20))))
      | ~ v1_funct_2(C_22,u1_struct_0(A_16),u1_struct_0(B_20))
      | ~ v1_funct_1(C_22)
      | ~ l1_struct_0(B_20)
      | v2_struct_0(B_20)
      | ~ l1_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26,plain,(
    ! [B_20,A_16,C_22] :
      ( k2_relset_1(u1_struct_0(B_20),u1_struct_0(A_16),k2_tops_2(u1_struct_0(A_16),u1_struct_0(B_20),C_22)) = k2_struct_0(A_16)
      | ~ v2_funct_1(C_22)
      | k2_relset_1(u1_struct_0(A_16),u1_struct_0(B_20),C_22) != k2_struct_0(B_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16),u1_struct_0(B_20))))
      | ~ v1_funct_2(C_22,u1_struct_0(A_16),u1_struct_0(B_20))
      | ~ v1_funct_1(C_22)
      | ~ l1_struct_0(B_20)
      | v2_struct_0(B_20)
      | ~ l1_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k2_tops_2(A_8,B_9,C_10),k1_zfmisc_1(k2_zfmisc_1(B_9,A_8)))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    ! [A_45,B_46,C_47] :
      ( v1_funct_1(k2_tops_2(A_45,B_46,C_47))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_59,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_62,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_59])).

tff(c_63,plain,(
    ! [A_48,B_49,C_50] :
      ( v1_funct_2(k2_tops_2(A_48,B_49,C_50),B_49,A_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_65,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_63])).

tff(c_68,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_65])).

tff(c_192,plain,(
    v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_143,plain,(
    ! [A_70,B_71,C_72] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_70),u1_struct_0(B_71),C_72),B_71,A_70)
      | ~ v3_tops_2(C_72,A_70,B_71)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70),u1_struct_0(B_71))))
      | ~ v1_funct_2(C_72,u1_struct_0(A_70),u1_struct_0(B_71))
      | ~ v1_funct_1(C_72)
      | ~ l1_pre_topc(B_71)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_143])).

tff(c_152,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_40,c_36,c_148])).

tff(c_92,plain,(
    ! [C_57,A_58,B_59] :
      ( v5_pre_topc(C_57,A_58,B_59)
      | ~ v3_tops_2(C_57,A_58,B_59)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58),u1_struct_0(B_59))))
      | ~ v1_funct_2(C_57,u1_struct_0(A_58),u1_struct_0(B_59))
      | ~ v1_funct_1(C_57)
      | ~ l1_pre_topc(B_59)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_99,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_92])).

tff(c_103,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_40,c_36,c_99])).

tff(c_69,plain,(
    ! [A_51,B_52,C_53] :
      ( m1_subset_1(k2_tops_2(A_51,B_52,C_53),k1_zfmisc_1(k2_zfmisc_1(B_52,A_51)))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ v1_funct_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_8,B_9,C_10] :
      ( v1_funct_1(k2_tops_2(A_8,B_9,C_10))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_153,plain,(
    ! [B_73,A_74,C_75] :
      ( v1_funct_1(k2_tops_2(B_73,A_74,k2_tops_2(A_74,B_73,C_75)))
      | ~ v1_funct_2(k2_tops_2(A_74,B_73,C_75),B_73,A_74)
      | ~ v1_funct_1(k2_tops_2(A_74,B_73,C_75))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73)))
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ v1_funct_1(C_75) ) ),
    inference(resolution,[status(thm)],[c_69,c_18])).

tff(c_157,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_153])).

tff(c_161,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_62,c_68,c_157])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( v1_funct_2(k2_tops_2(A_8,B_9,C_10),B_9,A_8)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_77,plain,(
    ! [B_52,A_51,C_53] :
      ( v1_funct_2(k2_tops_2(B_52,A_51,k2_tops_2(A_51,B_52,C_53)),A_51,B_52)
      | ~ v1_funct_2(k2_tops_2(A_51,B_52,C_53),B_52,A_51)
      | ~ v1_funct_1(k2_tops_2(A_51,B_52,C_53))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_2(C_53,A_51,B_52)
      | ~ v1_funct_1(C_53) ) ),
    inference(resolution,[status(thm)],[c_69,c_16])).

tff(c_218,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_funct_2(u1_struct_0(A_91),u1_struct_0(B_92),k2_tops_2(u1_struct_0(B_92),u1_struct_0(A_91),k2_tops_2(u1_struct_0(A_91),u1_struct_0(B_92),C_93)),C_93)
      | ~ v2_funct_1(C_93)
      | k2_relset_1(u1_struct_0(A_91),u1_struct_0(B_92),C_93) != k2_struct_0(B_92)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_91),u1_struct_0(B_92))))
      | ~ v1_funct_2(C_93,u1_struct_0(A_91),u1_struct_0(B_92))
      | ~ v1_funct_1(C_93)
      | ~ l1_struct_0(B_92)
      | v2_struct_0(B_92)
      | ~ l1_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_24,plain,(
    ! [D_15,C_14,A_12,B_13] :
      ( D_15 = C_14
      | ~ r2_funct_2(A_12,B_13,C_14,D_15)
      | ~ m1_subset_1(D_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(D_15,A_12,B_13)
      | ~ v1_funct_1(D_15)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(C_14,A_12,B_13)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_283,plain,(
    ! [B_121,A_122,C_123] :
      ( k2_tops_2(u1_struct_0(B_121),u1_struct_0(A_122),k2_tops_2(u1_struct_0(A_122),u1_struct_0(B_121),C_123)) = C_123
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(B_121),u1_struct_0(A_122),k2_tops_2(u1_struct_0(A_122),u1_struct_0(B_121),C_123)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_122),u1_struct_0(B_121))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_121),u1_struct_0(A_122),k2_tops_2(u1_struct_0(A_122),u1_struct_0(B_121),C_123)),u1_struct_0(A_122),u1_struct_0(B_121))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_121),u1_struct_0(A_122),k2_tops_2(u1_struct_0(A_122),u1_struct_0(B_121),C_123)))
      | ~ v2_funct_1(C_123)
      | k2_relset_1(u1_struct_0(A_122),u1_struct_0(B_121),C_123) != k2_struct_0(B_121)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_122),u1_struct_0(B_121))))
      | ~ v1_funct_2(C_123,u1_struct_0(A_122),u1_struct_0(B_121))
      | ~ v1_funct_1(C_123)
      | ~ l1_struct_0(B_121)
      | v2_struct_0(B_121)
      | ~ l1_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_218,c_24])).

tff(c_333,plain,(
    ! [B_136,A_137,C_138] :
      ( k2_tops_2(u1_struct_0(B_136),u1_struct_0(A_137),k2_tops_2(u1_struct_0(A_137),u1_struct_0(B_136),C_138)) = C_138
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_136),u1_struct_0(A_137),k2_tops_2(u1_struct_0(A_137),u1_struct_0(B_136),C_138)),u1_struct_0(A_137),u1_struct_0(B_136))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_136),u1_struct_0(A_137),k2_tops_2(u1_struct_0(A_137),u1_struct_0(B_136),C_138)))
      | ~ v2_funct_1(C_138)
      | k2_relset_1(u1_struct_0(A_137),u1_struct_0(B_136),C_138) != k2_struct_0(B_136)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_137),u1_struct_0(B_136))))
      | ~ v1_funct_2(C_138,u1_struct_0(A_137),u1_struct_0(B_136))
      | ~ v1_funct_1(C_138)
      | ~ l1_struct_0(B_136)
      | v2_struct_0(B_136)
      | ~ l1_struct_0(A_137)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_137),u1_struct_0(B_136),C_138),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_136),u1_struct_0(A_137))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_137),u1_struct_0(B_136),C_138),u1_struct_0(B_136),u1_struct_0(A_137))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_137),u1_struct_0(B_136),C_138)) ) ),
    inference(resolution,[status(thm)],[c_14,c_283])).

tff(c_339,plain,(
    ! [B_139,A_140,C_141] :
      ( k2_tops_2(u1_struct_0(B_139),u1_struct_0(A_140),k2_tops_2(u1_struct_0(A_140),u1_struct_0(B_139),C_141)) = C_141
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_139),u1_struct_0(A_140),k2_tops_2(u1_struct_0(A_140),u1_struct_0(B_139),C_141)))
      | ~ v2_funct_1(C_141)
      | k2_relset_1(u1_struct_0(A_140),u1_struct_0(B_139),C_141) != k2_struct_0(B_139)
      | ~ l1_struct_0(B_139)
      | v2_struct_0(B_139)
      | ~ l1_struct_0(A_140)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_140),u1_struct_0(B_139),C_141),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_139),u1_struct_0(A_140))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_140),u1_struct_0(B_139),C_141),u1_struct_0(B_139),u1_struct_0(A_140))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_140),u1_struct_0(B_139),C_141))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140),u1_struct_0(B_139))))
      | ~ v1_funct_2(C_141,u1_struct_0(A_140),u1_struct_0(B_139))
      | ~ v1_funct_1(C_141) ) ),
    inference(resolution,[status(thm)],[c_77,c_333])).

tff(c_345,plain,(
    ! [B_142,A_143,C_144] :
      ( k2_tops_2(u1_struct_0(B_142),u1_struct_0(A_143),k2_tops_2(u1_struct_0(A_143),u1_struct_0(B_142),C_144)) = C_144
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_142),u1_struct_0(A_143),k2_tops_2(u1_struct_0(A_143),u1_struct_0(B_142),C_144)))
      | ~ v2_funct_1(C_144)
      | k2_relset_1(u1_struct_0(A_143),u1_struct_0(B_142),C_144) != k2_struct_0(B_142)
      | ~ l1_struct_0(B_142)
      | v2_struct_0(B_142)
      | ~ l1_struct_0(A_143)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_143),u1_struct_0(B_142),C_144),u1_struct_0(B_142),u1_struct_0(A_143))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_143),u1_struct_0(B_142),C_144))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_143),u1_struct_0(B_142))))
      | ~ v1_funct_2(C_144,u1_struct_0(A_143),u1_struct_0(B_142))
      | ~ v1_funct_1(C_144) ) ),
    inference(resolution,[status(thm)],[c_14,c_339])).

tff(c_352,plain,
    ( k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_345])).

tff(c_356,plain,
    ( k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_62,c_68,c_183,c_193,c_122,c_91,c_352])).

tff(c_357,plain,(
    k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_356])).

tff(c_2,plain,(
    ! [C_7,A_1,B_5] :
      ( v3_tops_2(C_7,A_1,B_5)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_1),u1_struct_0(B_5),C_7),B_5,A_1)
      | ~ v5_pre_topc(C_7,A_1,B_5)
      | ~ v2_funct_1(C_7)
      | k2_relset_1(u1_struct_0(A_1),u1_struct_0(B_5),C_7) != k2_struct_0(B_5)
      | k1_relset_1(u1_struct_0(A_1),u1_struct_0(B_5),C_7) != k2_struct_0(A_1)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(B_5))))
      | ~ v1_funct_2(C_7,u1_struct_0(A_1),u1_struct_0(B_5))
      | ~ v1_funct_1(C_7)
      | ~ l1_pre_topc(B_5)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_417,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_2])).

tff(c_497,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_48,c_62,c_68,c_192,c_152,c_103,c_417])).

tff(c_498,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_497])).

tff(c_525,plain,(
    ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_528,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_525])).

tff(c_532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_528])).

tff(c_533,plain,
    ( k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2')
    | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_597,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_533])).

tff(c_615,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_597])).

tff(c_618,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_193,c_42,c_40,c_38,c_122,c_91,c_615])).

tff(c_620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_618])).

tff(c_621,plain,(
    k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_533])).

tff(c_625,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_621])).

tff(c_628,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_193,c_42,c_40,c_38,c_122,c_91,c_625])).

tff(c_630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_628])).

%------------------------------------------------------------------------------
