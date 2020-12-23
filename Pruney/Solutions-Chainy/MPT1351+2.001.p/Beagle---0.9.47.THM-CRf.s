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
% DateTime   : Thu Dec  3 10:23:51 EST 2020

% Result     : Theorem 4.84s
% Output     : CNFRefutation 5.18s
% Verified   : 
% Statistics : Number of formulae       :  153 (2885 expanded)
%              Number of leaves         :   38 (1183 expanded)
%              Depth                    :   18
%              Number of atoms          :  663 (18411 expanded)
%              Number of equality atoms :   77 ( 602 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v3_tops_2 > v1_funct_2 > v2_connsp_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v3_tops_2,type,(
    v3_tops_2: ( $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v2_connsp_1,type,(
    v2_connsp_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_227,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( v3_tops_2(C,A,B)
                        & v2_connsp_1(D,B) )
                     => v2_connsp_1(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_69,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_122,axiom,(
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

tff(f_104,axiom,(
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

tff(f_143,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_41,axiom,(
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

tff(f_164,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                      & v2_funct_1(C) )
                   => k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k8_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).

tff(f_195,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v5_pre_topc(C,A,B)
                      & v2_connsp_1(D,A) )
                   => v2_connsp_1(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_2)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_40,plain,(
    v2_connsp_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_48,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_64,plain,(
    ! [A_79,B_80,C_81] :
      ( v1_funct_1(k2_tops_2(A_79,B_80,C_81))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ v1_funct_2(C_81,A_79,B_80)
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_67,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_64])).

tff(c_70,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_67])).

tff(c_77,plain,(
    ! [A_85,B_86,C_87] :
      ( v1_funct_2(k2_tops_2(A_85,B_86,C_87),B_86,A_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_87,A_85,B_86)
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_79,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_77])).

tff(c_82,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_79])).

tff(c_42,plain,(
    v3_tops_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_166,plain,(
    ! [A_110,B_111,C_112] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_110),u1_struct_0(B_111),C_112),B_111,A_110)
      | ~ v3_tops_2(C_112,A_110,B_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_111))))
      | ~ v1_funct_2(C_112,u1_struct_0(A_110),u1_struct_0(B_111))
      | ~ v1_funct_1(C_112)
      | ~ l1_pre_topc(B_111)
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_171,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_166])).

tff(c_175,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_48,c_42,c_171])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k2_tops_2(A_13,B_14,C_15),k1_zfmisc_1(k2_zfmisc_1(B_14,A_13)))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_141,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(u1_struct_0(A_104),u1_struct_0(B_105),C_106) = k2_struct_0(B_105)
      | ~ v3_tops_2(C_106,A_104,B_105)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_104),u1_struct_0(B_105))))
      | ~ v1_funct_2(C_106,u1_struct_0(A_104),u1_struct_0(B_105))
      | ~ v1_funct_1(C_106)
      | ~ l1_pre_topc(B_105)
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_148,plain,
    ( k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_141])).

tff(c_152,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_48,c_42,c_148])).

tff(c_94,plain,(
    ! [C_91,A_92,B_93] :
      ( v2_funct_1(C_91)
      | ~ v3_tops_2(C_91,A_92,B_93)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),u1_struct_0(B_93))))
      | ~ v1_funct_2(C_91,u1_struct_0(A_92),u1_struct_0(B_93))
      | ~ v1_funct_1(C_91)
      | ~ l1_pre_topc(B_93)
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_94])).

tff(c_105,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_48,c_42,c_101])).

tff(c_177,plain,(
    ! [A_116,B_117,C_118] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_116),u1_struct_0(B_117),C_118))
      | ~ v2_funct_1(C_118)
      | k2_relset_1(u1_struct_0(A_116),u1_struct_0(B_117),C_118) != k2_struct_0(B_117)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116),u1_struct_0(B_117))))
      | ~ v1_funct_2(C_118,u1_struct_0(A_116),u1_struct_0(B_117))
      | ~ v1_funct_1(C_118)
      | ~ l1_struct_0(B_117)
      | ~ l1_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_184,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_177])).

tff(c_188,plain,
    ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_152,c_105,c_184])).

tff(c_189,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_192,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_189])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_192])).

tff(c_197,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_199,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_202,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_202])).

tff(c_208,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_198,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_188])).

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
    inference(cnfTransformation,[status(thm)],[f_104])).

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
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_125,plain,(
    ! [A_101,B_102,C_103] :
      ( k1_relset_1(u1_struct_0(A_101),u1_struct_0(B_102),C_103) = k2_struct_0(A_101)
      | ~ v3_tops_2(C_103,A_101,B_102)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101),u1_struct_0(B_102))))
      | ~ v1_funct_2(C_103,u1_struct_0(A_101),u1_struct_0(B_102))
      | ~ v1_funct_1(C_103)
      | ~ l1_pre_topc(B_102)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_288,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_relset_1(u1_struct_0(A_152),u1_struct_0(B_153),k2_tops_2(u1_struct_0(B_153),u1_struct_0(A_152),C_154)) = k2_struct_0(A_152)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_153),u1_struct_0(A_152),C_154),A_152,B_153)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_153),u1_struct_0(A_152),C_154),u1_struct_0(A_152),u1_struct_0(B_153))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_153),u1_struct_0(A_152),C_154))
      | ~ l1_pre_topc(B_153)
      | ~ l1_pre_topc(A_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_153),u1_struct_0(A_152))))
      | ~ v1_funct_2(C_154,u1_struct_0(B_153),u1_struct_0(A_152))
      | ~ v1_funct_1(C_154) ) ),
    inference(resolution,[status(thm)],[c_20,c_125])).

tff(c_295,plain,
    ( k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_288])).

tff(c_299,plain,
    ( k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_2')
    | ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_52,c_58,c_70,c_295])).

tff(c_312,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_83,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1(k2_tops_2(A_88,B_89,C_90),k1_zfmisc_1(k2_zfmisc_1(B_89,A_88)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2(C_90,A_88,B_89)
      | ~ v1_funct_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] :
      ( v1_funct_1(k2_tops_2(A_13,B_14,C_15))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_157,plain,(
    ! [B_107,A_108,C_109] :
      ( v1_funct_1(k2_tops_2(B_107,A_108,k2_tops_2(A_108,B_107,C_109)))
      | ~ v1_funct_2(k2_tops_2(A_108,B_107,C_109),B_107,A_108)
      | ~ v1_funct_1(k2_tops_2(A_108,B_107,C_109))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107)))
      | ~ v1_funct_2(C_109,A_108,B_107)
      | ~ v1_funct_1(C_109) ) ),
    inference(resolution,[status(thm)],[c_83,c_24])).

tff(c_161,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_157])).

tff(c_165,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_70,c_82,c_161])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( v1_funct_2(k2_tops_2(A_13,B_14,C_15),B_14,A_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_91,plain,(
    ! [B_89,A_88,C_90] :
      ( v1_funct_2(k2_tops_2(B_89,A_88,k2_tops_2(A_88,B_89,C_90)),A_88,B_89)
      | ~ v1_funct_2(k2_tops_2(A_88,B_89,C_90),B_89,A_88)
      | ~ v1_funct_1(k2_tops_2(A_88,B_89,C_90))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2(C_90,A_88,B_89)
      | ~ v1_funct_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_83,c_22])).

tff(c_232,plain,(
    ! [A_128,B_129,C_130] :
      ( r2_funct_2(u1_struct_0(A_128),u1_struct_0(B_129),k2_tops_2(u1_struct_0(B_129),u1_struct_0(A_128),k2_tops_2(u1_struct_0(A_128),u1_struct_0(B_129),C_130)),C_130)
      | ~ v2_funct_1(C_130)
      | k2_relset_1(u1_struct_0(A_128),u1_struct_0(B_129),C_130) != k2_struct_0(B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_128),u1_struct_0(B_129))))
      | ~ v1_funct_2(C_130,u1_struct_0(A_128),u1_struct_0(B_129))
      | ~ v1_funct_1(C_130)
      | ~ l1_struct_0(B_129)
      | v2_struct_0(B_129)
      | ~ l1_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_320,plain,(
    ! [B_171,A_172,C_173] :
      ( k2_tops_2(u1_struct_0(B_171),u1_struct_0(A_172),k2_tops_2(u1_struct_0(A_172),u1_struct_0(B_171),C_173)) = C_173
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(B_171),u1_struct_0(A_172),k2_tops_2(u1_struct_0(A_172),u1_struct_0(B_171),C_173)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172),u1_struct_0(B_171))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_171),u1_struct_0(A_172),k2_tops_2(u1_struct_0(A_172),u1_struct_0(B_171),C_173)),u1_struct_0(A_172),u1_struct_0(B_171))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_171),u1_struct_0(A_172),k2_tops_2(u1_struct_0(A_172),u1_struct_0(B_171),C_173)))
      | ~ v2_funct_1(C_173)
      | k2_relset_1(u1_struct_0(A_172),u1_struct_0(B_171),C_173) != k2_struct_0(B_171)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172),u1_struct_0(B_171))))
      | ~ v1_funct_2(C_173,u1_struct_0(A_172),u1_struct_0(B_171))
      | ~ v1_funct_1(C_173)
      | ~ l1_struct_0(B_171)
      | v2_struct_0(B_171)
      | ~ l1_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_232,c_4])).

tff(c_370,plain,(
    ! [B_186,A_187,C_188] :
      ( k2_tops_2(u1_struct_0(B_186),u1_struct_0(A_187),k2_tops_2(u1_struct_0(A_187),u1_struct_0(B_186),C_188)) = C_188
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_186),u1_struct_0(A_187),k2_tops_2(u1_struct_0(A_187),u1_struct_0(B_186),C_188)),u1_struct_0(A_187),u1_struct_0(B_186))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_186),u1_struct_0(A_187),k2_tops_2(u1_struct_0(A_187),u1_struct_0(B_186),C_188)))
      | ~ v2_funct_1(C_188)
      | k2_relset_1(u1_struct_0(A_187),u1_struct_0(B_186),C_188) != k2_struct_0(B_186)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_187),u1_struct_0(B_186))))
      | ~ v1_funct_2(C_188,u1_struct_0(A_187),u1_struct_0(B_186))
      | ~ v1_funct_1(C_188)
      | ~ l1_struct_0(B_186)
      | v2_struct_0(B_186)
      | ~ l1_struct_0(A_187)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_187),u1_struct_0(B_186),C_188),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_186),u1_struct_0(A_187))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_187),u1_struct_0(B_186),C_188),u1_struct_0(B_186),u1_struct_0(A_187))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_187),u1_struct_0(B_186),C_188)) ) ),
    inference(resolution,[status(thm)],[c_20,c_320])).

tff(c_381,plain,(
    ! [B_192,A_193,C_194] :
      ( k2_tops_2(u1_struct_0(B_192),u1_struct_0(A_193),k2_tops_2(u1_struct_0(A_193),u1_struct_0(B_192),C_194)) = C_194
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_192),u1_struct_0(A_193),k2_tops_2(u1_struct_0(A_193),u1_struct_0(B_192),C_194)))
      | ~ v2_funct_1(C_194)
      | k2_relset_1(u1_struct_0(A_193),u1_struct_0(B_192),C_194) != k2_struct_0(B_192)
      | ~ l1_struct_0(B_192)
      | v2_struct_0(B_192)
      | ~ l1_struct_0(A_193)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_193),u1_struct_0(B_192),C_194),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_192),u1_struct_0(A_193))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_193),u1_struct_0(B_192),C_194),u1_struct_0(B_192),u1_struct_0(A_193))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_193),u1_struct_0(B_192),C_194))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193),u1_struct_0(B_192))))
      | ~ v1_funct_2(C_194,u1_struct_0(A_193),u1_struct_0(B_192))
      | ~ v1_funct_1(C_194) ) ),
    inference(resolution,[status(thm)],[c_91,c_370])).

tff(c_387,plain,(
    ! [B_195,A_196,C_197] :
      ( k2_tops_2(u1_struct_0(B_195),u1_struct_0(A_196),k2_tops_2(u1_struct_0(A_196),u1_struct_0(B_195),C_197)) = C_197
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_195),u1_struct_0(A_196),k2_tops_2(u1_struct_0(A_196),u1_struct_0(B_195),C_197)))
      | ~ v2_funct_1(C_197)
      | k2_relset_1(u1_struct_0(A_196),u1_struct_0(B_195),C_197) != k2_struct_0(B_195)
      | ~ l1_struct_0(B_195)
      | v2_struct_0(B_195)
      | ~ l1_struct_0(A_196)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_196),u1_struct_0(B_195),C_197),u1_struct_0(B_195),u1_struct_0(A_196))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_196),u1_struct_0(B_195),C_197))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_196),u1_struct_0(B_195))))
      | ~ v1_funct_2(C_197,u1_struct_0(A_196),u1_struct_0(B_195))
      | ~ v1_funct_1(C_197) ) ),
    inference(resolution,[status(thm)],[c_20,c_381])).

tff(c_394,plain,
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
    inference(resolution,[status(thm)],[c_165,c_387])).

tff(c_398,plain,
    ( k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_70,c_82,c_198,c_208,c_152,c_105,c_394])).

tff(c_399,plain,(
    k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_398])).

tff(c_207,plain,(
    v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_106,plain,(
    ! [C_94,A_95,B_96] :
      ( v5_pre_topc(C_94,A_95,B_96)
      | ~ v3_tops_2(C_94,A_95,B_96)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95),u1_struct_0(B_96))))
      | ~ v1_funct_2(C_94,u1_struct_0(A_95),u1_struct_0(B_96))
      | ~ v1_funct_1(C_94)
      | ~ l1_pre_topc(B_96)
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_276,plain,(
    ! [B_149,A_150,C_151] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(B_149),u1_struct_0(A_150),C_151),A_150,B_149)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_149),u1_struct_0(A_150),C_151),A_150,B_149)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_149),u1_struct_0(A_150),C_151),u1_struct_0(A_150),u1_struct_0(B_149))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_149),u1_struct_0(A_150),C_151))
      | ~ l1_pre_topc(B_149)
      | ~ l1_pre_topc(A_150)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_149),u1_struct_0(A_150))))
      | ~ v1_funct_2(C_151,u1_struct_0(B_149),u1_struct_0(A_150))
      | ~ v1_funct_1(C_151) ) ),
    inference(resolution,[status(thm)],[c_20,c_106])).

tff(c_325,plain,(
    ! [B_174,A_175,C_176] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(B_174),u1_struct_0(A_175),k2_tops_2(u1_struct_0(A_175),u1_struct_0(B_174),C_176)),A_175,B_174)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_174),u1_struct_0(A_175),k2_tops_2(u1_struct_0(A_175),u1_struct_0(B_174),C_176)),A_175,B_174)
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_174),u1_struct_0(A_175),k2_tops_2(u1_struct_0(A_175),u1_struct_0(B_174),C_176)))
      | ~ l1_pre_topc(B_174)
      | ~ l1_pre_topc(A_175)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_175),u1_struct_0(B_174),C_176),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_174),u1_struct_0(A_175))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_175),u1_struct_0(B_174),C_176),u1_struct_0(B_174),u1_struct_0(A_175))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_175),u1_struct_0(B_174),C_176))
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175),u1_struct_0(B_174))))
      | ~ v1_funct_2(C_176,u1_struct_0(A_175),u1_struct_0(B_174))
      | ~ v1_funct_1(C_176) ) ),
    inference(resolution,[status(thm)],[c_91,c_276])).

tff(c_348,plain,(
    ! [B_180,A_181,C_182] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(B_180),u1_struct_0(A_181),k2_tops_2(u1_struct_0(A_181),u1_struct_0(B_180),C_182)),A_181,B_180)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_180),u1_struct_0(A_181),k2_tops_2(u1_struct_0(A_181),u1_struct_0(B_180),C_182)),A_181,B_180)
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_180),u1_struct_0(A_181),k2_tops_2(u1_struct_0(A_181),u1_struct_0(B_180),C_182)))
      | ~ l1_pre_topc(B_180)
      | ~ l1_pre_topc(A_181)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_181),u1_struct_0(B_180),C_182),u1_struct_0(B_180),u1_struct_0(A_181))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_181),u1_struct_0(B_180),C_182))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),u1_struct_0(B_180))))
      | ~ v1_funct_2(C_182,u1_struct_0(A_181),u1_struct_0(B_180))
      | ~ v1_funct_1(C_182) ) ),
    inference(resolution,[status(thm)],[c_20,c_325])).

tff(c_8,plain,(
    ! [C_12,A_6,B_10] :
      ( v3_tops_2(C_12,A_6,B_10)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_6),u1_struct_0(B_10),C_12),B_10,A_6)
      | ~ v5_pre_topc(C_12,A_6,B_10)
      | ~ v2_funct_1(C_12)
      | k2_relset_1(u1_struct_0(A_6),u1_struct_0(B_10),C_12) != k2_struct_0(B_10)
      | k1_relset_1(u1_struct_0(A_6),u1_struct_0(B_10),C_12) != k2_struct_0(A_6)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6),u1_struct_0(B_10))))
      | ~ v1_funct_2(C_12,u1_struct_0(A_6),u1_struct_0(B_10))
      | ~ v1_funct_1(C_12)
      | ~ l1_pre_topc(B_10)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_376,plain,(
    ! [A_189,B_190,C_191] :
      ( v3_tops_2(k2_tops_2(u1_struct_0(A_189),u1_struct_0(B_190),C_191),B_190,A_189)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_189),u1_struct_0(B_190),C_191),B_190,A_189)
      | ~ v2_funct_1(k2_tops_2(u1_struct_0(A_189),u1_struct_0(B_190),C_191))
      | k2_relset_1(u1_struct_0(B_190),u1_struct_0(A_189),k2_tops_2(u1_struct_0(A_189),u1_struct_0(B_190),C_191)) != k2_struct_0(A_189)
      | k1_relset_1(u1_struct_0(B_190),u1_struct_0(A_189),k2_tops_2(u1_struct_0(A_189),u1_struct_0(B_190),C_191)) != k2_struct_0(B_190)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_189),u1_struct_0(B_190),C_191),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_190),u1_struct_0(A_189))))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_190),u1_struct_0(A_189),k2_tops_2(u1_struct_0(A_189),u1_struct_0(B_190),C_191)),A_189,B_190)
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_190),u1_struct_0(A_189),k2_tops_2(u1_struct_0(A_189),u1_struct_0(B_190),C_191)))
      | ~ l1_pre_topc(B_190)
      | ~ l1_pre_topc(A_189)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_189),u1_struct_0(B_190),C_191),u1_struct_0(B_190),u1_struct_0(A_189))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_189),u1_struct_0(B_190),C_191))
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_189),u1_struct_0(B_190))))
      | ~ v1_funct_2(C_191,u1_struct_0(A_189),u1_struct_0(B_190))
      | ~ v1_funct_1(C_191) ) ),
    inference(resolution,[status(thm)],[c_348,c_8])).

tff(c_597,plain,(
    ! [A_198,B_199,C_200] :
      ( v3_tops_2(k2_tops_2(u1_struct_0(A_198),u1_struct_0(B_199),C_200),B_199,A_198)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_198),u1_struct_0(B_199),C_200),B_199,A_198)
      | ~ v2_funct_1(k2_tops_2(u1_struct_0(A_198),u1_struct_0(B_199),C_200))
      | k2_relset_1(u1_struct_0(B_199),u1_struct_0(A_198),k2_tops_2(u1_struct_0(A_198),u1_struct_0(B_199),C_200)) != k2_struct_0(A_198)
      | k1_relset_1(u1_struct_0(B_199),u1_struct_0(A_198),k2_tops_2(u1_struct_0(A_198),u1_struct_0(B_199),C_200)) != k2_struct_0(B_199)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_199),u1_struct_0(A_198),k2_tops_2(u1_struct_0(A_198),u1_struct_0(B_199),C_200)),A_198,B_199)
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_199),u1_struct_0(A_198),k2_tops_2(u1_struct_0(A_198),u1_struct_0(B_199),C_200)))
      | ~ l1_pre_topc(B_199)
      | ~ l1_pre_topc(A_198)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_198),u1_struct_0(B_199),C_200),u1_struct_0(B_199),u1_struct_0(A_198))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_198),u1_struct_0(B_199),C_200))
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_198),u1_struct_0(B_199))))
      | ~ v1_funct_2(C_200,u1_struct_0(A_198),u1_struct_0(B_199))
      | ~ v1_funct_1(C_200) ) ),
    inference(resolution,[status(thm)],[c_20,c_376])).

tff(c_603,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2')
    | ~ v3_tops_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_597])).

tff(c_607,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_70,c_82,c_58,c_52,c_50,c_399,c_42,c_207,c_175,c_603])).

tff(c_608,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_607])).

tff(c_680,plain,(
    k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_608])).

tff(c_683,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_680])).

tff(c_686,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_208,c_50,c_48,c_46,c_152,c_105,c_683])).

tff(c_688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_686])).

tff(c_689,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_711,plain,
    ( ~ v2_funct_1('#skF_3')
    | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_689])).

tff(c_714,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_208,c_50,c_48,c_46,c_152,c_105,c_711])).

tff(c_716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_714])).

tff(c_718,plain,(
    v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_300,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_relset_1(u1_struct_0(A_155),u1_struct_0(B_156),k2_tops_2(u1_struct_0(B_156),u1_struct_0(A_155),C_157)) = k2_struct_0(B_156)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_156),u1_struct_0(A_155),C_157),A_155,B_156)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_156),u1_struct_0(A_155),C_157),u1_struct_0(A_155),u1_struct_0(B_156))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_156),u1_struct_0(A_155),C_157))
      | ~ l1_pre_topc(B_156)
      | ~ l1_pre_topc(A_155)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_156),u1_struct_0(A_155))))
      | ~ v1_funct_2(C_157,u1_struct_0(B_156),u1_struct_0(A_155))
      | ~ v1_funct_1(C_157) ) ),
    inference(resolution,[status(thm)],[c_20,c_141])).

tff(c_307,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_1')
    | ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_300])).

tff(c_311,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_1')
    | ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_52,c_58,c_70,c_307])).

tff(c_742,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_311])).

tff(c_764,plain,(
    ! [B_215,A_216,C_217] :
      ( k2_tops_2(u1_struct_0(B_215),u1_struct_0(A_216),k2_tops_2(u1_struct_0(A_216),u1_struct_0(B_215),C_217)) = C_217
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(B_215),u1_struct_0(A_216),k2_tops_2(u1_struct_0(A_216),u1_struct_0(B_215),C_217)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216),u1_struct_0(B_215))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_215),u1_struct_0(A_216),k2_tops_2(u1_struct_0(A_216),u1_struct_0(B_215),C_217)),u1_struct_0(A_216),u1_struct_0(B_215))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_215),u1_struct_0(A_216),k2_tops_2(u1_struct_0(A_216),u1_struct_0(B_215),C_217)))
      | ~ v2_funct_1(C_217)
      | k2_relset_1(u1_struct_0(A_216),u1_struct_0(B_215),C_217) != k2_struct_0(B_215)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216),u1_struct_0(B_215))))
      | ~ v1_funct_2(C_217,u1_struct_0(A_216),u1_struct_0(B_215))
      | ~ v1_funct_1(C_217)
      | ~ l1_struct_0(B_215)
      | v2_struct_0(B_215)
      | ~ l1_struct_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_232,c_4])).

tff(c_814,plain,(
    ! [B_230,A_231,C_232] :
      ( k2_tops_2(u1_struct_0(B_230),u1_struct_0(A_231),k2_tops_2(u1_struct_0(A_231),u1_struct_0(B_230),C_232)) = C_232
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_230),u1_struct_0(A_231),k2_tops_2(u1_struct_0(A_231),u1_struct_0(B_230),C_232)),u1_struct_0(A_231),u1_struct_0(B_230))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_230),u1_struct_0(A_231),k2_tops_2(u1_struct_0(A_231),u1_struct_0(B_230),C_232)))
      | ~ v2_funct_1(C_232)
      | k2_relset_1(u1_struct_0(A_231),u1_struct_0(B_230),C_232) != k2_struct_0(B_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_231),u1_struct_0(B_230))))
      | ~ v1_funct_2(C_232,u1_struct_0(A_231),u1_struct_0(B_230))
      | ~ v1_funct_1(C_232)
      | ~ l1_struct_0(B_230)
      | v2_struct_0(B_230)
      | ~ l1_struct_0(A_231)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_231),u1_struct_0(B_230),C_232),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_230),u1_struct_0(A_231))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_231),u1_struct_0(B_230),C_232),u1_struct_0(B_230),u1_struct_0(A_231))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_231),u1_struct_0(B_230),C_232)) ) ),
    inference(resolution,[status(thm)],[c_20,c_764])).

tff(c_820,plain,(
    ! [B_233,A_234,C_235] :
      ( k2_tops_2(u1_struct_0(B_233),u1_struct_0(A_234),k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_233),C_235)) = C_235
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_233),u1_struct_0(A_234),k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_233),C_235)))
      | ~ v2_funct_1(C_235)
      | k2_relset_1(u1_struct_0(A_234),u1_struct_0(B_233),C_235) != k2_struct_0(B_233)
      | ~ l1_struct_0(B_233)
      | v2_struct_0(B_233)
      | ~ l1_struct_0(A_234)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_233),C_235),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_233),u1_struct_0(A_234))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_233),C_235),u1_struct_0(B_233),u1_struct_0(A_234))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_234),u1_struct_0(B_233),C_235))
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_234),u1_struct_0(B_233))))
      | ~ v1_funct_2(C_235,u1_struct_0(A_234),u1_struct_0(B_233))
      | ~ v1_funct_1(C_235) ) ),
    inference(resolution,[status(thm)],[c_91,c_814])).

tff(c_826,plain,(
    ! [B_236,A_237,C_238] :
      ( k2_tops_2(u1_struct_0(B_236),u1_struct_0(A_237),k2_tops_2(u1_struct_0(A_237),u1_struct_0(B_236),C_238)) = C_238
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_236),u1_struct_0(A_237),k2_tops_2(u1_struct_0(A_237),u1_struct_0(B_236),C_238)))
      | ~ v2_funct_1(C_238)
      | k2_relset_1(u1_struct_0(A_237),u1_struct_0(B_236),C_238) != k2_struct_0(B_236)
      | ~ l1_struct_0(B_236)
      | v2_struct_0(B_236)
      | ~ l1_struct_0(A_237)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_237),u1_struct_0(B_236),C_238),u1_struct_0(B_236),u1_struct_0(A_237))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_237),u1_struct_0(B_236),C_238))
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_237),u1_struct_0(B_236))))
      | ~ v1_funct_2(C_238,u1_struct_0(A_237),u1_struct_0(B_236))
      | ~ v1_funct_1(C_238) ) ),
    inference(resolution,[status(thm)],[c_20,c_820])).

tff(c_833,plain,
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
    inference(resolution,[status(thm)],[c_165,c_826])).

tff(c_837,plain,
    ( k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_70,c_82,c_198,c_208,c_152,c_105,c_833])).

tff(c_838,plain,(
    k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_837])).

tff(c_32,plain,(
    ! [A_30,B_34,C_36] :
      ( r2_funct_2(u1_struct_0(A_30),u1_struct_0(B_34),k2_tops_2(u1_struct_0(B_34),u1_struct_0(A_30),k2_tops_2(u1_struct_0(A_30),u1_struct_0(B_34),C_36)),C_36)
      | ~ v2_funct_1(C_36)
      | k2_relset_1(u1_struct_0(A_30),u1_struct_0(B_34),C_36) != k2_struct_0(B_34)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30),u1_struct_0(B_34))))
      | ~ v1_funct_2(C_36,u1_struct_0(A_30),u1_struct_0(B_34))
      | ~ v1_funct_1(C_36)
      | ~ l1_struct_0(B_34)
      | v2_struct_0(B_34)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_916,plain,
    ( r2_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_32])).

tff(c_999,plain,
    ( r2_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_198,c_70,c_82,c_742,c_207,c_916])).

tff(c_1000,plain,
    ( r2_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_999])).

tff(c_1021,plain,(
    ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_1000])).

tff(c_1024,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1021])).

tff(c_1028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1024])).

tff(c_1030,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_1000])).

tff(c_34,plain,(
    ! [B_45,A_37,C_49,D_51] :
      ( k8_relset_1(u1_struct_0(B_45),u1_struct_0(A_37),k2_tops_2(u1_struct_0(A_37),u1_struct_0(B_45),C_49),D_51) = k7_relset_1(u1_struct_0(A_37),u1_struct_0(B_45),C_49,D_51)
      | ~ v2_funct_1(C_49)
      | k2_relset_1(u1_struct_0(A_37),u1_struct_0(B_45),C_49) != k2_struct_0(B_45)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37),u1_struct_0(B_45))))
      | ~ v1_funct_2(C_49,u1_struct_0(A_37),u1_struct_0(B_45))
      | ~ v1_funct_1(C_49)
      | ~ l1_struct_0(B_45)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_913,plain,(
    ! [D_51] :
      ( k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),D_51) = k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_51)
      | ~ v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
      | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_struct_0('#skF_1')
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_34])).

tff(c_997,plain,(
    ! [D_51] :
      ( k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),D_51) = k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_51)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_198,c_70,c_82,c_742,c_207,c_913])).

tff(c_1117,plain,(
    ! [D_243] :
      ( k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),D_243) = k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_243)
      | ~ m1_subset_1(D_243,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_997])).

tff(c_236,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( v2_connsp_1(k7_relset_1(u1_struct_0(A_131),u1_struct_0(B_132),C_133,D_134),B_132)
      | ~ v2_connsp_1(D_134,A_131)
      | ~ v5_pre_topc(C_133,A_131,B_132)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131),u1_struct_0(B_132))))
      | ~ v1_funct_2(C_133,u1_struct_0(A_131),u1_struct_0(B_132))
      | ~ v1_funct_1(C_133)
      | ~ l1_pre_topc(B_132)
      | ~ v2_pre_topc(B_132)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_242,plain,(
    ! [A_131,B_132,C_15,D_134] :
      ( v2_connsp_1(k7_relset_1(u1_struct_0(A_131),u1_struct_0(B_132),k2_tops_2(u1_struct_0(B_132),u1_struct_0(A_131),C_15),D_134),B_132)
      | ~ v2_connsp_1(D_134,A_131)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(B_132),u1_struct_0(A_131),C_15),A_131,B_132)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_132),u1_struct_0(A_131),C_15),u1_struct_0(A_131),u1_struct_0(B_132))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_132),u1_struct_0(A_131),C_15))
      | ~ l1_pre_topc(B_132)
      | ~ v2_pre_topc(B_132)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_132),u1_struct_0(A_131))))
      | ~ v1_funct_2(C_15,u1_struct_0(B_132),u1_struct_0(A_131))
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_20,c_236])).

tff(c_1126,plain,(
    ! [D_243] :
      ( v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_243),'#skF_1')
      | ~ v2_connsp_1(D_243,'#skF_2')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),'#skF_2','#skF_1')
      | ~ m1_subset_1(D_243,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3'))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(D_243,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1117,c_242])).

tff(c_1132,plain,(
    ! [D_243] :
      ( v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_243),'#skF_1')
      | ~ v2_connsp_1(D_243,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(D_243,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_54,c_52,c_60,c_58,c_70,c_82,c_175,c_1126])).

tff(c_1135,plain,(
    ! [D_244] :
      ( v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',D_244),'#skF_1')
      | ~ v2_connsp_1(D_244,'#skF_2')
      | ~ m1_subset_1(D_244,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_1132])).

tff(c_38,plain,(
    ~ v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_1138,plain,
    ( ~ v2_connsp_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1135,c_38])).

tff(c_1142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_1138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:19:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.84/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/2.00  
% 4.84/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/2.01  %$ r2_funct_2 > v5_pre_topc > v3_tops_2 > v1_funct_2 > v2_connsp_1 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.84/2.01  
% 4.84/2.01  %Foreground sorts:
% 4.84/2.01  
% 4.84/2.01  
% 4.84/2.01  %Background operators:
% 4.84/2.01  
% 4.84/2.01  
% 4.84/2.01  %Foreground operators:
% 4.84/2.01  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.84/2.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.84/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.84/2.01  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.84/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/2.01  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.84/2.01  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 4.84/2.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.84/2.01  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.84/2.01  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.84/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.84/2.01  tff('#skF_2', type, '#skF_2': $i).
% 4.84/2.01  tff('#skF_3', type, '#skF_3': $i).
% 4.84/2.01  tff('#skF_1', type, '#skF_1': $i).
% 4.84/2.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.84/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.84/2.01  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.84/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.84/2.01  tff('#skF_4', type, '#skF_4': $i).
% 4.84/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/2.01  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.84/2.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.84/2.01  tff(v2_connsp_1, type, v2_connsp_1: ($i * $i) > $o).
% 4.84/2.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.84/2.01  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.84/2.01  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.84/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.84/2.01  
% 5.18/2.04  tff(f_227, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_tops_2(C, A, B) & v2_connsp_1(D, B)) => v2_connsp_1(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_2)).
% 5.18/2.04  tff(f_81, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 5.18/2.04  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 5.18/2.04  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.18/2.04  tff(f_122, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_tops_2)).
% 5.18/2.04  tff(f_104, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 5.18/2.04  tff(f_143, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 5.18/2.04  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 5.18/2.04  tff(f_164, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k8_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tops_2)).
% 5.18/2.04  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v5_pre_topc(C, A, B) & v2_connsp_1(D, A)) => v2_connsp_1(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_tops_2)).
% 5.18/2.04  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_40, plain, (v2_connsp_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_48, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_64, plain, (![A_79, B_80, C_81]: (v1_funct_1(k2_tops_2(A_79, B_80, C_81)) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~v1_funct_2(C_81, A_79, B_80) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.18/2.04  tff(c_67, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_64])).
% 5.18/2.04  tff(c_70, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_67])).
% 5.18/2.04  tff(c_77, plain, (![A_85, B_86, C_87]: (v1_funct_2(k2_tops_2(A_85, B_86, C_87), B_86, A_85) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_87, A_85, B_86) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.18/2.04  tff(c_79, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_77])).
% 5.18/2.04  tff(c_82, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_79])).
% 5.18/2.04  tff(c_42, plain, (v3_tops_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_166, plain, (![A_110, B_111, C_112]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_110), u1_struct_0(B_111), C_112), B_111, A_110) | ~v3_tops_2(C_112, A_110, B_111) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_111)))) | ~v1_funct_2(C_112, u1_struct_0(A_110), u1_struct_0(B_111)) | ~v1_funct_1(C_112) | ~l1_pre_topc(B_111) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.18/2.04  tff(c_171, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_166])).
% 5.18/2.04  tff(c_175, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_50, c_48, c_42, c_171])).
% 5.18/2.04  tff(c_20, plain, (![A_13, B_14, C_15]: (m1_subset_1(k2_tops_2(A_13, B_14, C_15), k1_zfmisc_1(k2_zfmisc_1(B_14, A_13))) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.18/2.04  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.18/2.04  tff(c_141, plain, (![A_104, B_105, C_106]: (k2_relset_1(u1_struct_0(A_104), u1_struct_0(B_105), C_106)=k2_struct_0(B_105) | ~v3_tops_2(C_106, A_104, B_105) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_104), u1_struct_0(B_105)))) | ~v1_funct_2(C_106, u1_struct_0(A_104), u1_struct_0(B_105)) | ~v1_funct_1(C_106) | ~l1_pre_topc(B_105) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.18/2.04  tff(c_148, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_141])).
% 5.18/2.04  tff(c_152, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_50, c_48, c_42, c_148])).
% 5.18/2.04  tff(c_94, plain, (![C_91, A_92, B_93]: (v2_funct_1(C_91) | ~v3_tops_2(C_91, A_92, B_93) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), u1_struct_0(B_93)))) | ~v1_funct_2(C_91, u1_struct_0(A_92), u1_struct_0(B_93)) | ~v1_funct_1(C_91) | ~l1_pre_topc(B_93) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.18/2.04  tff(c_101, plain, (v2_funct_1('#skF_3') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_94])).
% 5.18/2.04  tff(c_105, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_50, c_48, c_42, c_101])).
% 5.18/2.04  tff(c_177, plain, (![A_116, B_117, C_118]: (v2_funct_1(k2_tops_2(u1_struct_0(A_116), u1_struct_0(B_117), C_118)) | ~v2_funct_1(C_118) | k2_relset_1(u1_struct_0(A_116), u1_struct_0(B_117), C_118)!=k2_struct_0(B_117) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_116), u1_struct_0(B_117)))) | ~v1_funct_2(C_118, u1_struct_0(A_116), u1_struct_0(B_117)) | ~v1_funct_1(C_118) | ~l1_struct_0(B_117) | ~l1_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.18/2.04  tff(c_184, plain, (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_177])).
% 5.18/2.04  tff(c_188, plain, (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_152, c_105, c_184])).
% 5.18/2.04  tff(c_189, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_188])).
% 5.18/2.04  tff(c_192, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_189])).
% 5.18/2.04  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_192])).
% 5.18/2.04  tff(c_197, plain, (~l1_struct_0('#skF_2') | v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_188])).
% 5.18/2.04  tff(c_199, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_197])).
% 5.18/2.04  tff(c_202, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_199])).
% 5.18/2.04  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_202])).
% 5.18/2.04  tff(c_208, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_197])).
% 5.18/2.04  tff(c_198, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_188])).
% 5.18/2.04  tff(c_26, plain, (![B_20, A_16, C_22]: (k2_relset_1(u1_struct_0(B_20), u1_struct_0(A_16), k2_tops_2(u1_struct_0(A_16), u1_struct_0(B_20), C_22))=k2_struct_0(A_16) | ~v2_funct_1(C_22) | k2_relset_1(u1_struct_0(A_16), u1_struct_0(B_20), C_22)!=k2_struct_0(B_20) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16), u1_struct_0(B_20)))) | ~v1_funct_2(C_22, u1_struct_0(A_16), u1_struct_0(B_20)) | ~v1_funct_1(C_22) | ~l1_struct_0(B_20) | v2_struct_0(B_20) | ~l1_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.18/2.04  tff(c_28, plain, (![B_20, A_16, C_22]: (k1_relset_1(u1_struct_0(B_20), u1_struct_0(A_16), k2_tops_2(u1_struct_0(A_16), u1_struct_0(B_20), C_22))=k2_struct_0(B_20) | ~v2_funct_1(C_22) | k2_relset_1(u1_struct_0(A_16), u1_struct_0(B_20), C_22)!=k2_struct_0(B_20) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16), u1_struct_0(B_20)))) | ~v1_funct_2(C_22, u1_struct_0(A_16), u1_struct_0(B_20)) | ~v1_funct_1(C_22) | ~l1_struct_0(B_20) | v2_struct_0(B_20) | ~l1_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.18/2.04  tff(c_125, plain, (![A_101, B_102, C_103]: (k1_relset_1(u1_struct_0(A_101), u1_struct_0(B_102), C_103)=k2_struct_0(A_101) | ~v3_tops_2(C_103, A_101, B_102) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_101), u1_struct_0(B_102)))) | ~v1_funct_2(C_103, u1_struct_0(A_101), u1_struct_0(B_102)) | ~v1_funct_1(C_103) | ~l1_pre_topc(B_102) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.18/2.04  tff(c_288, plain, (![A_152, B_153, C_154]: (k1_relset_1(u1_struct_0(A_152), u1_struct_0(B_153), k2_tops_2(u1_struct_0(B_153), u1_struct_0(A_152), C_154))=k2_struct_0(A_152) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_153), u1_struct_0(A_152), C_154), A_152, B_153) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_153), u1_struct_0(A_152), C_154), u1_struct_0(A_152), u1_struct_0(B_153)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_153), u1_struct_0(A_152), C_154)) | ~l1_pre_topc(B_153) | ~l1_pre_topc(A_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_153), u1_struct_0(A_152)))) | ~v1_funct_2(C_154, u1_struct_0(B_153), u1_struct_0(A_152)) | ~v1_funct_1(C_154))), inference(resolution, [status(thm)], [c_20, c_125])).
% 5.18/2.04  tff(c_295, plain, (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_288])).
% 5.18/2.04  tff(c_299, plain, (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_2') | ~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_52, c_58, c_70, c_295])).
% 5.18/2.04  tff(c_312, plain, (~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_299])).
% 5.18/2.04  tff(c_83, plain, (![A_88, B_89, C_90]: (m1_subset_1(k2_tops_2(A_88, B_89, C_90), k1_zfmisc_1(k2_zfmisc_1(B_89, A_88))) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2(C_90, A_88, B_89) | ~v1_funct_1(C_90))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.18/2.04  tff(c_24, plain, (![A_13, B_14, C_15]: (v1_funct_1(k2_tops_2(A_13, B_14, C_15)) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.18/2.04  tff(c_157, plain, (![B_107, A_108, C_109]: (v1_funct_1(k2_tops_2(B_107, A_108, k2_tops_2(A_108, B_107, C_109))) | ~v1_funct_2(k2_tops_2(A_108, B_107, C_109), B_107, A_108) | ~v1_funct_1(k2_tops_2(A_108, B_107, C_109)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))) | ~v1_funct_2(C_109, A_108, B_107) | ~v1_funct_1(C_109))), inference(resolution, [status(thm)], [c_83, c_24])).
% 5.18/2.04  tff(c_161, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))) | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_157])).
% 5.18/2.04  tff(c_165, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_70, c_82, c_161])).
% 5.18/2.04  tff(c_22, plain, (![A_13, B_14, C_15]: (v1_funct_2(k2_tops_2(A_13, B_14, C_15), B_14, A_13) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.18/2.04  tff(c_91, plain, (![B_89, A_88, C_90]: (v1_funct_2(k2_tops_2(B_89, A_88, k2_tops_2(A_88, B_89, C_90)), A_88, B_89) | ~v1_funct_2(k2_tops_2(A_88, B_89, C_90), B_89, A_88) | ~v1_funct_1(k2_tops_2(A_88, B_89, C_90)) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2(C_90, A_88, B_89) | ~v1_funct_1(C_90))), inference(resolution, [status(thm)], [c_83, c_22])).
% 5.18/2.04  tff(c_232, plain, (![A_128, B_129, C_130]: (r2_funct_2(u1_struct_0(A_128), u1_struct_0(B_129), k2_tops_2(u1_struct_0(B_129), u1_struct_0(A_128), k2_tops_2(u1_struct_0(A_128), u1_struct_0(B_129), C_130)), C_130) | ~v2_funct_1(C_130) | k2_relset_1(u1_struct_0(A_128), u1_struct_0(B_129), C_130)!=k2_struct_0(B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_128), u1_struct_0(B_129)))) | ~v1_funct_2(C_130, u1_struct_0(A_128), u1_struct_0(B_129)) | ~v1_funct_1(C_130) | ~l1_struct_0(B_129) | v2_struct_0(B_129) | ~l1_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.18/2.04  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.18/2.04  tff(c_320, plain, (![B_171, A_172, C_173]: (k2_tops_2(u1_struct_0(B_171), u1_struct_0(A_172), k2_tops_2(u1_struct_0(A_172), u1_struct_0(B_171), C_173))=C_173 | ~m1_subset_1(k2_tops_2(u1_struct_0(B_171), u1_struct_0(A_172), k2_tops_2(u1_struct_0(A_172), u1_struct_0(B_171), C_173)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172), u1_struct_0(B_171)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_171), u1_struct_0(A_172), k2_tops_2(u1_struct_0(A_172), u1_struct_0(B_171), C_173)), u1_struct_0(A_172), u1_struct_0(B_171)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_171), u1_struct_0(A_172), k2_tops_2(u1_struct_0(A_172), u1_struct_0(B_171), C_173))) | ~v2_funct_1(C_173) | k2_relset_1(u1_struct_0(A_172), u1_struct_0(B_171), C_173)!=k2_struct_0(B_171) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172), u1_struct_0(B_171)))) | ~v1_funct_2(C_173, u1_struct_0(A_172), u1_struct_0(B_171)) | ~v1_funct_1(C_173) | ~l1_struct_0(B_171) | v2_struct_0(B_171) | ~l1_struct_0(A_172))), inference(resolution, [status(thm)], [c_232, c_4])).
% 5.18/2.04  tff(c_370, plain, (![B_186, A_187, C_188]: (k2_tops_2(u1_struct_0(B_186), u1_struct_0(A_187), k2_tops_2(u1_struct_0(A_187), u1_struct_0(B_186), C_188))=C_188 | ~v1_funct_2(k2_tops_2(u1_struct_0(B_186), u1_struct_0(A_187), k2_tops_2(u1_struct_0(A_187), u1_struct_0(B_186), C_188)), u1_struct_0(A_187), u1_struct_0(B_186)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_186), u1_struct_0(A_187), k2_tops_2(u1_struct_0(A_187), u1_struct_0(B_186), C_188))) | ~v2_funct_1(C_188) | k2_relset_1(u1_struct_0(A_187), u1_struct_0(B_186), C_188)!=k2_struct_0(B_186) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_187), u1_struct_0(B_186)))) | ~v1_funct_2(C_188, u1_struct_0(A_187), u1_struct_0(B_186)) | ~v1_funct_1(C_188) | ~l1_struct_0(B_186) | v2_struct_0(B_186) | ~l1_struct_0(A_187) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_187), u1_struct_0(B_186), C_188), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_186), u1_struct_0(A_187)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_187), u1_struct_0(B_186), C_188), u1_struct_0(B_186), u1_struct_0(A_187)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_187), u1_struct_0(B_186), C_188)))), inference(resolution, [status(thm)], [c_20, c_320])).
% 5.18/2.04  tff(c_381, plain, (![B_192, A_193, C_194]: (k2_tops_2(u1_struct_0(B_192), u1_struct_0(A_193), k2_tops_2(u1_struct_0(A_193), u1_struct_0(B_192), C_194))=C_194 | ~v1_funct_1(k2_tops_2(u1_struct_0(B_192), u1_struct_0(A_193), k2_tops_2(u1_struct_0(A_193), u1_struct_0(B_192), C_194))) | ~v2_funct_1(C_194) | k2_relset_1(u1_struct_0(A_193), u1_struct_0(B_192), C_194)!=k2_struct_0(B_192) | ~l1_struct_0(B_192) | v2_struct_0(B_192) | ~l1_struct_0(A_193) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_193), u1_struct_0(B_192), C_194), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_192), u1_struct_0(A_193)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_193), u1_struct_0(B_192), C_194), u1_struct_0(B_192), u1_struct_0(A_193)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_193), u1_struct_0(B_192), C_194)) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193), u1_struct_0(B_192)))) | ~v1_funct_2(C_194, u1_struct_0(A_193), u1_struct_0(B_192)) | ~v1_funct_1(C_194))), inference(resolution, [status(thm)], [c_91, c_370])).
% 5.18/2.04  tff(c_387, plain, (![B_195, A_196, C_197]: (k2_tops_2(u1_struct_0(B_195), u1_struct_0(A_196), k2_tops_2(u1_struct_0(A_196), u1_struct_0(B_195), C_197))=C_197 | ~v1_funct_1(k2_tops_2(u1_struct_0(B_195), u1_struct_0(A_196), k2_tops_2(u1_struct_0(A_196), u1_struct_0(B_195), C_197))) | ~v2_funct_1(C_197) | k2_relset_1(u1_struct_0(A_196), u1_struct_0(B_195), C_197)!=k2_struct_0(B_195) | ~l1_struct_0(B_195) | v2_struct_0(B_195) | ~l1_struct_0(A_196) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_196), u1_struct_0(B_195), C_197), u1_struct_0(B_195), u1_struct_0(A_196)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_196), u1_struct_0(B_195), C_197)) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_196), u1_struct_0(B_195)))) | ~v1_funct_2(C_197, u1_struct_0(A_196), u1_struct_0(B_195)) | ~v1_funct_1(C_197))), inference(resolution, [status(thm)], [c_20, c_381])).
% 5.18/2.04  tff(c_394, plain, (k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v2_funct_1('#skF_3') | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_165, c_387])).
% 5.18/2.04  tff(c_398, plain, (k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_70, c_82, c_198, c_208, c_152, c_105, c_394])).
% 5.18/2.04  tff(c_399, plain, (k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_56, c_398])).
% 5.18/2.04  tff(c_207, plain, (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))), inference(splitRight, [status(thm)], [c_197])).
% 5.18/2.04  tff(c_106, plain, (![C_94, A_95, B_96]: (v5_pre_topc(C_94, A_95, B_96) | ~v3_tops_2(C_94, A_95, B_96) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_95), u1_struct_0(B_96)))) | ~v1_funct_2(C_94, u1_struct_0(A_95), u1_struct_0(B_96)) | ~v1_funct_1(C_94) | ~l1_pre_topc(B_96) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.18/2.04  tff(c_276, plain, (![B_149, A_150, C_151]: (v5_pre_topc(k2_tops_2(u1_struct_0(B_149), u1_struct_0(A_150), C_151), A_150, B_149) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_149), u1_struct_0(A_150), C_151), A_150, B_149) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_149), u1_struct_0(A_150), C_151), u1_struct_0(A_150), u1_struct_0(B_149)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_149), u1_struct_0(A_150), C_151)) | ~l1_pre_topc(B_149) | ~l1_pre_topc(A_150) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_149), u1_struct_0(A_150)))) | ~v1_funct_2(C_151, u1_struct_0(B_149), u1_struct_0(A_150)) | ~v1_funct_1(C_151))), inference(resolution, [status(thm)], [c_20, c_106])).
% 5.18/2.04  tff(c_325, plain, (![B_174, A_175, C_176]: (v5_pre_topc(k2_tops_2(u1_struct_0(B_174), u1_struct_0(A_175), k2_tops_2(u1_struct_0(A_175), u1_struct_0(B_174), C_176)), A_175, B_174) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_174), u1_struct_0(A_175), k2_tops_2(u1_struct_0(A_175), u1_struct_0(B_174), C_176)), A_175, B_174) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_174), u1_struct_0(A_175), k2_tops_2(u1_struct_0(A_175), u1_struct_0(B_174), C_176))) | ~l1_pre_topc(B_174) | ~l1_pre_topc(A_175) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_175), u1_struct_0(B_174), C_176), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_174), u1_struct_0(A_175)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_175), u1_struct_0(B_174), C_176), u1_struct_0(B_174), u1_struct_0(A_175)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_175), u1_struct_0(B_174), C_176)) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175), u1_struct_0(B_174)))) | ~v1_funct_2(C_176, u1_struct_0(A_175), u1_struct_0(B_174)) | ~v1_funct_1(C_176))), inference(resolution, [status(thm)], [c_91, c_276])).
% 5.18/2.04  tff(c_348, plain, (![B_180, A_181, C_182]: (v5_pre_topc(k2_tops_2(u1_struct_0(B_180), u1_struct_0(A_181), k2_tops_2(u1_struct_0(A_181), u1_struct_0(B_180), C_182)), A_181, B_180) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_180), u1_struct_0(A_181), k2_tops_2(u1_struct_0(A_181), u1_struct_0(B_180), C_182)), A_181, B_180) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_180), u1_struct_0(A_181), k2_tops_2(u1_struct_0(A_181), u1_struct_0(B_180), C_182))) | ~l1_pre_topc(B_180) | ~l1_pre_topc(A_181) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_181), u1_struct_0(B_180), C_182), u1_struct_0(B_180), u1_struct_0(A_181)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_181), u1_struct_0(B_180), C_182)) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181), u1_struct_0(B_180)))) | ~v1_funct_2(C_182, u1_struct_0(A_181), u1_struct_0(B_180)) | ~v1_funct_1(C_182))), inference(resolution, [status(thm)], [c_20, c_325])).
% 5.18/2.04  tff(c_8, plain, (![C_12, A_6, B_10]: (v3_tops_2(C_12, A_6, B_10) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_6), u1_struct_0(B_10), C_12), B_10, A_6) | ~v5_pre_topc(C_12, A_6, B_10) | ~v2_funct_1(C_12) | k2_relset_1(u1_struct_0(A_6), u1_struct_0(B_10), C_12)!=k2_struct_0(B_10) | k1_relset_1(u1_struct_0(A_6), u1_struct_0(B_10), C_12)!=k2_struct_0(A_6) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6), u1_struct_0(B_10)))) | ~v1_funct_2(C_12, u1_struct_0(A_6), u1_struct_0(B_10)) | ~v1_funct_1(C_12) | ~l1_pre_topc(B_10) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.18/2.04  tff(c_376, plain, (![A_189, B_190, C_191]: (v3_tops_2(k2_tops_2(u1_struct_0(A_189), u1_struct_0(B_190), C_191), B_190, A_189) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_189), u1_struct_0(B_190), C_191), B_190, A_189) | ~v2_funct_1(k2_tops_2(u1_struct_0(A_189), u1_struct_0(B_190), C_191)) | k2_relset_1(u1_struct_0(B_190), u1_struct_0(A_189), k2_tops_2(u1_struct_0(A_189), u1_struct_0(B_190), C_191))!=k2_struct_0(A_189) | k1_relset_1(u1_struct_0(B_190), u1_struct_0(A_189), k2_tops_2(u1_struct_0(A_189), u1_struct_0(B_190), C_191))!=k2_struct_0(B_190) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_189), u1_struct_0(B_190), C_191), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_190), u1_struct_0(A_189)))) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_190), u1_struct_0(A_189), k2_tops_2(u1_struct_0(A_189), u1_struct_0(B_190), C_191)), A_189, B_190) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_190), u1_struct_0(A_189), k2_tops_2(u1_struct_0(A_189), u1_struct_0(B_190), C_191))) | ~l1_pre_topc(B_190) | ~l1_pre_topc(A_189) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_189), u1_struct_0(B_190), C_191), u1_struct_0(B_190), u1_struct_0(A_189)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_189), u1_struct_0(B_190), C_191)) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_189), u1_struct_0(B_190)))) | ~v1_funct_2(C_191, u1_struct_0(A_189), u1_struct_0(B_190)) | ~v1_funct_1(C_191))), inference(resolution, [status(thm)], [c_348, c_8])).
% 5.18/2.04  tff(c_597, plain, (![A_198, B_199, C_200]: (v3_tops_2(k2_tops_2(u1_struct_0(A_198), u1_struct_0(B_199), C_200), B_199, A_198) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_198), u1_struct_0(B_199), C_200), B_199, A_198) | ~v2_funct_1(k2_tops_2(u1_struct_0(A_198), u1_struct_0(B_199), C_200)) | k2_relset_1(u1_struct_0(B_199), u1_struct_0(A_198), k2_tops_2(u1_struct_0(A_198), u1_struct_0(B_199), C_200))!=k2_struct_0(A_198) | k1_relset_1(u1_struct_0(B_199), u1_struct_0(A_198), k2_tops_2(u1_struct_0(A_198), u1_struct_0(B_199), C_200))!=k2_struct_0(B_199) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_199), u1_struct_0(A_198), k2_tops_2(u1_struct_0(A_198), u1_struct_0(B_199), C_200)), A_198, B_199) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_199), u1_struct_0(A_198), k2_tops_2(u1_struct_0(A_198), u1_struct_0(B_199), C_200))) | ~l1_pre_topc(B_199) | ~l1_pre_topc(A_198) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_198), u1_struct_0(B_199), C_200), u1_struct_0(B_199), u1_struct_0(A_198)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_198), u1_struct_0(B_199), C_200)) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_198), u1_struct_0(B_199)))) | ~v1_funct_2(C_200, u1_struct_0(A_198), u1_struct_0(B_199)) | ~v1_funct_1(C_200))), inference(resolution, [status(thm)], [c_20, c_376])).
% 5.18/2.04  tff(c_603, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2') | ~v3_tops_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_399, c_597])).
% 5.18/2.04  tff(c_607, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_70, c_82, c_58, c_52, c_50, c_399, c_42, c_207, c_175, c_603])).
% 5.18/2.04  tff(c_608, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_312, c_607])).
% 5.18/2.04  tff(c_680, plain, (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_608])).
% 5.18/2.04  tff(c_683, plain, (~v2_funct_1('#skF_3') | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_680])).
% 5.18/2.04  tff(c_686, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_208, c_50, c_48, c_46, c_152, c_105, c_683])).
% 5.18/2.04  tff(c_688, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_686])).
% 5.18/2.04  tff(c_689, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_608])).
% 5.18/2.04  tff(c_711, plain, (~v2_funct_1('#skF_3') | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_689])).
% 5.18/2.04  tff(c_714, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_208, c_50, c_48, c_46, c_152, c_105, c_711])).
% 5.18/2.04  tff(c_716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_714])).
% 5.18/2.04  tff(c_718, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_299])).
% 5.18/2.04  tff(c_300, plain, (![A_155, B_156, C_157]: (k2_relset_1(u1_struct_0(A_155), u1_struct_0(B_156), k2_tops_2(u1_struct_0(B_156), u1_struct_0(A_155), C_157))=k2_struct_0(B_156) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_156), u1_struct_0(A_155), C_157), A_155, B_156) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_156), u1_struct_0(A_155), C_157), u1_struct_0(A_155), u1_struct_0(B_156)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_156), u1_struct_0(A_155), C_157)) | ~l1_pre_topc(B_156) | ~l1_pre_topc(A_155) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_156), u1_struct_0(A_155)))) | ~v1_funct_2(C_157, u1_struct_0(B_156), u1_struct_0(A_155)) | ~v1_funct_1(C_157))), inference(resolution, [status(thm)], [c_20, c_141])).
% 5.18/2.04  tff(c_307, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_1') | ~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_300])).
% 5.18/2.04  tff(c_311, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_1') | ~v3_tops_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_52, c_58, c_70, c_307])).
% 5.18/2.04  tff(c_742, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_311])).
% 5.18/2.04  tff(c_764, plain, (![B_215, A_216, C_217]: (k2_tops_2(u1_struct_0(B_215), u1_struct_0(A_216), k2_tops_2(u1_struct_0(A_216), u1_struct_0(B_215), C_217))=C_217 | ~m1_subset_1(k2_tops_2(u1_struct_0(B_215), u1_struct_0(A_216), k2_tops_2(u1_struct_0(A_216), u1_struct_0(B_215), C_217)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216), u1_struct_0(B_215)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_215), u1_struct_0(A_216), k2_tops_2(u1_struct_0(A_216), u1_struct_0(B_215), C_217)), u1_struct_0(A_216), u1_struct_0(B_215)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_215), u1_struct_0(A_216), k2_tops_2(u1_struct_0(A_216), u1_struct_0(B_215), C_217))) | ~v2_funct_1(C_217) | k2_relset_1(u1_struct_0(A_216), u1_struct_0(B_215), C_217)!=k2_struct_0(B_215) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216), u1_struct_0(B_215)))) | ~v1_funct_2(C_217, u1_struct_0(A_216), u1_struct_0(B_215)) | ~v1_funct_1(C_217) | ~l1_struct_0(B_215) | v2_struct_0(B_215) | ~l1_struct_0(A_216))), inference(resolution, [status(thm)], [c_232, c_4])).
% 5.18/2.04  tff(c_814, plain, (![B_230, A_231, C_232]: (k2_tops_2(u1_struct_0(B_230), u1_struct_0(A_231), k2_tops_2(u1_struct_0(A_231), u1_struct_0(B_230), C_232))=C_232 | ~v1_funct_2(k2_tops_2(u1_struct_0(B_230), u1_struct_0(A_231), k2_tops_2(u1_struct_0(A_231), u1_struct_0(B_230), C_232)), u1_struct_0(A_231), u1_struct_0(B_230)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_230), u1_struct_0(A_231), k2_tops_2(u1_struct_0(A_231), u1_struct_0(B_230), C_232))) | ~v2_funct_1(C_232) | k2_relset_1(u1_struct_0(A_231), u1_struct_0(B_230), C_232)!=k2_struct_0(B_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_231), u1_struct_0(B_230)))) | ~v1_funct_2(C_232, u1_struct_0(A_231), u1_struct_0(B_230)) | ~v1_funct_1(C_232) | ~l1_struct_0(B_230) | v2_struct_0(B_230) | ~l1_struct_0(A_231) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_231), u1_struct_0(B_230), C_232), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_230), u1_struct_0(A_231)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_231), u1_struct_0(B_230), C_232), u1_struct_0(B_230), u1_struct_0(A_231)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_231), u1_struct_0(B_230), C_232)))), inference(resolution, [status(thm)], [c_20, c_764])).
% 5.18/2.04  tff(c_820, plain, (![B_233, A_234, C_235]: (k2_tops_2(u1_struct_0(B_233), u1_struct_0(A_234), k2_tops_2(u1_struct_0(A_234), u1_struct_0(B_233), C_235))=C_235 | ~v1_funct_1(k2_tops_2(u1_struct_0(B_233), u1_struct_0(A_234), k2_tops_2(u1_struct_0(A_234), u1_struct_0(B_233), C_235))) | ~v2_funct_1(C_235) | k2_relset_1(u1_struct_0(A_234), u1_struct_0(B_233), C_235)!=k2_struct_0(B_233) | ~l1_struct_0(B_233) | v2_struct_0(B_233) | ~l1_struct_0(A_234) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_234), u1_struct_0(B_233), C_235), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_233), u1_struct_0(A_234)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_234), u1_struct_0(B_233), C_235), u1_struct_0(B_233), u1_struct_0(A_234)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_234), u1_struct_0(B_233), C_235)) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_234), u1_struct_0(B_233)))) | ~v1_funct_2(C_235, u1_struct_0(A_234), u1_struct_0(B_233)) | ~v1_funct_1(C_235))), inference(resolution, [status(thm)], [c_91, c_814])).
% 5.18/2.04  tff(c_826, plain, (![B_236, A_237, C_238]: (k2_tops_2(u1_struct_0(B_236), u1_struct_0(A_237), k2_tops_2(u1_struct_0(A_237), u1_struct_0(B_236), C_238))=C_238 | ~v1_funct_1(k2_tops_2(u1_struct_0(B_236), u1_struct_0(A_237), k2_tops_2(u1_struct_0(A_237), u1_struct_0(B_236), C_238))) | ~v2_funct_1(C_238) | k2_relset_1(u1_struct_0(A_237), u1_struct_0(B_236), C_238)!=k2_struct_0(B_236) | ~l1_struct_0(B_236) | v2_struct_0(B_236) | ~l1_struct_0(A_237) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_237), u1_struct_0(B_236), C_238), u1_struct_0(B_236), u1_struct_0(A_237)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_237), u1_struct_0(B_236), C_238)) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_237), u1_struct_0(B_236)))) | ~v1_funct_2(C_238, u1_struct_0(A_237), u1_struct_0(B_236)) | ~v1_funct_1(C_238))), inference(resolution, [status(thm)], [c_20, c_820])).
% 5.18/2.04  tff(c_833, plain, (k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))='#skF_3' | ~v2_funct_1('#skF_3') | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_165, c_826])).
% 5.18/2.04  tff(c_837, plain, (k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_70, c_82, c_198, c_208, c_152, c_105, c_833])).
% 5.18/2.04  tff(c_838, plain, (k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_56, c_837])).
% 5.18/2.04  tff(c_32, plain, (![A_30, B_34, C_36]: (r2_funct_2(u1_struct_0(A_30), u1_struct_0(B_34), k2_tops_2(u1_struct_0(B_34), u1_struct_0(A_30), k2_tops_2(u1_struct_0(A_30), u1_struct_0(B_34), C_36)), C_36) | ~v2_funct_1(C_36) | k2_relset_1(u1_struct_0(A_30), u1_struct_0(B_34), C_36)!=k2_struct_0(B_34) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30), u1_struct_0(B_34)))) | ~v1_funct_2(C_36, u1_struct_0(A_30), u1_struct_0(B_34)) | ~v1_funct_1(C_36) | ~l1_struct_0(B_34) | v2_struct_0(B_34) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.18/2.04  tff(c_916, plain, (r2_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_838, c_32])).
% 5.18/2.04  tff(c_999, plain, (r2_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_198, c_70, c_82, c_742, c_207, c_916])).
% 5.18/2.04  tff(c_1000, plain, (r2_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_999])).
% 5.18/2.04  tff(c_1021, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_1000])).
% 5.18/2.04  tff(c_1024, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1021])).
% 5.18/2.04  tff(c_1028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1024])).
% 5.18/2.04  tff(c_1030, plain, (m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_1000])).
% 5.18/2.04  tff(c_34, plain, (![B_45, A_37, C_49, D_51]: (k8_relset_1(u1_struct_0(B_45), u1_struct_0(A_37), k2_tops_2(u1_struct_0(A_37), u1_struct_0(B_45), C_49), D_51)=k7_relset_1(u1_struct_0(A_37), u1_struct_0(B_45), C_49, D_51) | ~v2_funct_1(C_49) | k2_relset_1(u1_struct_0(A_37), u1_struct_0(B_45), C_49)!=k2_struct_0(B_45) | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_37), u1_struct_0(B_45)))) | ~v1_funct_2(C_49, u1_struct_0(A_37), u1_struct_0(B_45)) | ~v1_funct_1(C_49) | ~l1_struct_0(B_45) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.18/2.04  tff(c_913, plain, (![D_51]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), D_51)=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_51) | ~v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~l1_struct_0('#skF_1') | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_838, c_34])).
% 5.18/2.04  tff(c_997, plain, (![D_51]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), D_51)=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_51) | ~m1_subset_1(D_51, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_198, c_70, c_82, c_742, c_207, c_913])).
% 5.18/2.04  tff(c_1117, plain, (![D_243]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), D_243)=k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_243) | ~m1_subset_1(D_243, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_997])).
% 5.18/2.04  tff(c_236, plain, (![A_131, B_132, C_133, D_134]: (v2_connsp_1(k7_relset_1(u1_struct_0(A_131), u1_struct_0(B_132), C_133, D_134), B_132) | ~v2_connsp_1(D_134, A_131) | ~v5_pre_topc(C_133, A_131, B_132) | ~m1_subset_1(D_134, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131), u1_struct_0(B_132)))) | ~v1_funct_2(C_133, u1_struct_0(A_131), u1_struct_0(B_132)) | ~v1_funct_1(C_133) | ~l1_pre_topc(B_132) | ~v2_pre_topc(B_132) | v2_struct_0(B_132) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_195])).
% 5.18/2.04  tff(c_242, plain, (![A_131, B_132, C_15, D_134]: (v2_connsp_1(k7_relset_1(u1_struct_0(A_131), u1_struct_0(B_132), k2_tops_2(u1_struct_0(B_132), u1_struct_0(A_131), C_15), D_134), B_132) | ~v2_connsp_1(D_134, A_131) | ~v5_pre_topc(k2_tops_2(u1_struct_0(B_132), u1_struct_0(A_131), C_15), A_131, B_132) | ~m1_subset_1(D_134, k1_zfmisc_1(u1_struct_0(A_131))) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_132), u1_struct_0(A_131), C_15), u1_struct_0(A_131), u1_struct_0(B_132)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_132), u1_struct_0(A_131), C_15)) | ~l1_pre_topc(B_132) | ~v2_pre_topc(B_132) | v2_struct_0(B_132) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_132), u1_struct_0(A_131)))) | ~v1_funct_2(C_15, u1_struct_0(B_132), u1_struct_0(A_131)) | ~v1_funct_1(C_15))), inference(resolution, [status(thm)], [c_20, c_236])).
% 5.18/2.04  tff(c_1126, plain, (![D_243]: (v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_243), '#skF_1') | ~v2_connsp_1(D_243, '#skF_2') | ~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(D_243, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(D_243, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_1117, c_242])).
% 5.18/2.04  tff(c_1132, plain, (![D_243]: (v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_243), '#skF_1') | ~v2_connsp_1(D_243, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2') | ~m1_subset_1(D_243, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_54, c_52, c_60, c_58, c_70, c_82, c_175, c_1126])).
% 5.18/2.04  tff(c_1135, plain, (![D_244]: (v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', D_244), '#skF_1') | ~v2_connsp_1(D_244, '#skF_2') | ~m1_subset_1(D_244, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_1132])).
% 5.18/2.04  tff(c_38, plain, (~v2_connsp_1(k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 5.18/2.04  tff(c_1138, plain, (~v2_connsp_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_1135, c_38])).
% 5.18/2.04  tff(c_1142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_1138])).
% 5.18/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.18/2.04  
% 5.18/2.04  Inference rules
% 5.18/2.04  ----------------------
% 5.18/2.04  #Ref     : 0
% 5.18/2.04  #Sup     : 202
% 5.18/2.04  #Fact    : 0
% 5.18/2.04  #Define  : 0
% 5.18/2.04  #Split   : 6
% 5.18/2.04  #Chain   : 0
% 5.18/2.04  #Close   : 0
% 5.18/2.04  
% 5.18/2.04  Ordering : KBO
% 5.18/2.04  
% 5.18/2.04  Simplification rules
% 5.18/2.04  ----------------------
% 5.18/2.04  #Subsume      : 22
% 5.18/2.04  #Demod        : 1091
% 5.18/2.04  #Tautology    : 128
% 5.18/2.04  #SimpNegUnit  : 34
% 5.18/2.04  #BackRed      : 2
% 5.18/2.04  
% 5.18/2.04  #Partial instantiations: 0
% 5.18/2.04  #Strategies tried      : 1
% 5.18/2.04  
% 5.18/2.04  Timing (in seconds)
% 5.18/2.04  ----------------------
% 5.18/2.05  Preprocessing        : 0.46
% 5.18/2.05  Parsing              : 0.22
% 5.18/2.05  CNF conversion       : 0.05
% 5.18/2.05  Main loop            : 0.72
% 5.18/2.05  Inferencing          : 0.26
% 5.18/2.05  Reduction            : 0.26
% 5.18/2.05  Demodulation         : 0.21
% 5.18/2.05  BG Simplification    : 0.04
% 5.18/2.05  Subsumption          : 0.13
% 5.18/2.05  Abstraction          : 0.03
% 5.18/2.05  MUC search           : 0.00
% 5.18/2.05  Cooper               : 0.00
% 5.18/2.05  Total                : 1.24
% 5.18/2.05  Index Insertion      : 0.00
% 5.18/2.05  Index Deletion       : 0.00
% 5.18/2.05  Index Matching       : 0.00
% 5.18/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
