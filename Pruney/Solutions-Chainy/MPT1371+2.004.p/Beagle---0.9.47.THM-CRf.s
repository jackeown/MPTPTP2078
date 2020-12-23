%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:00 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  119 (1052 expanded)
%              Number of leaves         :   40 ( 430 expanded)
%              Depth                    :   16
%              Number of atoms          :  375 (6830 expanded)
%              Number of equality atoms :   19 ( 646 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v4_pre_topc > v2_compts_1 > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( v1_compts_1(A)
                    & v8_pre_topc(B)
                    & k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                    & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C)
                    & v5_pre_topc(C,A,B) )
                 => v3_tops_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_compts_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( v4_pre_topc(D,B)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

tff(f_78,axiom,(
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

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_compts_1(A)
              & v4_pre_topc(B,A) )
           => v2_compts_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).

tff(f_161,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & l1_pre_topc(C) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) )
                 => ( ( v5_pre_topc(D,A,C)
                      & k2_relset_1(u1_struct_0(A),u1_struct_0(C),D) = k2_struct_0(C)
                      & v2_compts_1(B,A) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(A),u1_struct_0(C),D,B),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_compts_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_111,axiom,(
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

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_12,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_40,plain,(
    ~ v3_tops_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_48,plain,(
    k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_46,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_44,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_42,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_85,plain,(
    ! [A_85,B_86,C_87] :
      ( v1_funct_1(k2_tops_2(A_85,B_86,C_87))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_87,A_85,B_86)
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_92,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_85])).

tff(c_96,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_92])).

tff(c_103,plain,(
    ! [A_90,B_91,C_92] :
      ( v1_funct_2(k2_tops_2(A_90,B_91,C_92),B_91,A_90)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91)))
      | ~ v1_funct_2(C_92,A_90,B_91)
      | ~ v1_funct_1(C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_108,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_103])).

tff(c_112,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_108])).

tff(c_26,plain,(
    ! [A_35,B_36,C_37] :
      ( m1_subset_1(k2_tops_2(A_35,B_36,C_37),k1_zfmisc_1(k2_zfmisc_1(B_36,A_35)))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_2(C_37,A_35,B_36)
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_176,plain,(
    ! [A_111,B_112,C_113] :
      ( v4_pre_topc('#skF_1'(A_111,B_112,C_113),B_112)
      | v5_pre_topc(C_113,A_111,B_112)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(B_112))))
      | ~ v1_funct_2(C_113,u1_struct_0(A_111),u1_struct_0(B_112))
      | ~ v1_funct_1(C_113)
      | ~ l1_pre_topc(B_112)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_373,plain,(
    ! [A_181,B_182,C_183] :
      ( v4_pre_topc('#skF_1'(A_181,B_182,k2_tops_2(u1_struct_0(B_182),u1_struct_0(A_181),C_183)),B_182)
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_182),u1_struct_0(A_181),C_183),A_181,B_182)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_182),u1_struct_0(A_181),C_183),u1_struct_0(A_181),u1_struct_0(B_182))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_182),u1_struct_0(A_181),C_183))
      | ~ l1_pre_topc(B_182)
      | ~ l1_pre_topc(A_181)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_182),u1_struct_0(A_181))))
      | ~ v1_funct_2(C_183,u1_struct_0(B_182),u1_struct_0(A_181))
      | ~ v1_funct_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_26,c_176])).

tff(c_381,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2')
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_373])).

tff(c_386,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2')
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_60,c_66,c_96,c_381])).

tff(c_387,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_14,plain,(
    ! [C_34,A_28,B_32] :
      ( v3_tops_2(C_34,A_28,B_32)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_28),u1_struct_0(B_32),C_34),B_32,A_28)
      | ~ v5_pre_topc(C_34,A_28,B_32)
      | ~ v2_funct_1(C_34)
      | k2_relset_1(u1_struct_0(A_28),u1_struct_0(B_32),C_34) != k2_struct_0(B_32)
      | k1_relset_1(u1_struct_0(A_28),u1_struct_0(B_32),C_34) != k2_struct_0(A_28)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28),u1_struct_0(B_32))))
      | ~ v1_funct_2(C_34,u1_struct_0(A_28),u1_struct_0(B_32))
      | ~ v1_funct_1(C_34)
      | ~ l1_pre_topc(B_32)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_398,plain,
    ( v3_tops_2('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') != k2_struct_0('#skF_3')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_387,c_14])).

tff(c_401,plain,(
    v3_tops_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_58,c_56,c_54,c_48,c_46,c_44,c_42,c_398])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_401])).

tff(c_405,plain,(
    ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_207,plain,(
    ! [A_117,B_118,C_119] :
      ( m1_subset_1('#skF_1'(A_117,B_118,C_119),k1_zfmisc_1(u1_struct_0(B_118)))
      | v5_pre_topc(C_119,A_117,B_118)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117),u1_struct_0(B_118))))
      | ~ v1_funct_2(C_119,u1_struct_0(A_117),u1_struct_0(B_118))
      | ~ v1_funct_1(C_119)
      | ~ l1_pre_topc(B_118)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_216,plain,(
    ! [A_117,B_118,C_37] :
      ( m1_subset_1('#skF_1'(A_117,B_118,k2_tops_2(u1_struct_0(B_118),u1_struct_0(A_117),C_37)),k1_zfmisc_1(u1_struct_0(B_118)))
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_118),u1_struct_0(A_117),C_37),A_117,B_118)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_118),u1_struct_0(A_117),C_37),u1_struct_0(A_117),u1_struct_0(B_118))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_118),u1_struct_0(A_117),C_37))
      | ~ l1_pre_topc(B_118)
      | ~ l1_pre_topc(A_117)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_118),u1_struct_0(A_117))))
      | ~ v1_funct_2(C_37,u1_struct_0(B_118),u1_struct_0(A_117))
      | ~ v1_funct_1(C_37) ) ),
    inference(resolution,[status(thm)],[c_26,c_207])).

tff(c_52,plain,(
    v1_compts_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_404,plain,(
    v4_pre_topc('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_406,plain,(
    ! [A_187,B_188,C_189] :
      ( m1_subset_1('#skF_1'(A_187,B_188,k2_tops_2(u1_struct_0(B_188),u1_struct_0(A_187),C_189)),k1_zfmisc_1(u1_struct_0(B_188)))
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_188),u1_struct_0(A_187),C_189),A_187,B_188)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_188),u1_struct_0(A_187),C_189),u1_struct_0(A_187),u1_struct_0(B_188))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_188),u1_struct_0(A_187),C_189))
      | ~ l1_pre_topc(B_188)
      | ~ l1_pre_topc(A_187)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_188),u1_struct_0(A_187))))
      | ~ v1_funct_2(C_189,u1_struct_0(B_188),u1_struct_0(A_187))
      | ~ v1_funct_1(C_189) ) ),
    inference(resolution,[status(thm)],[c_26,c_207])).

tff(c_36,plain,(
    ! [B_58,A_56] :
      ( v2_compts_1(B_58,A_56)
      | ~ v4_pre_topc(B_58,A_56)
      | ~ v1_compts_1(A_56)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_483,plain,(
    ! [A_255,B_256,C_257] :
      ( v2_compts_1('#skF_1'(A_255,B_256,k2_tops_2(u1_struct_0(B_256),u1_struct_0(A_255),C_257)),B_256)
      | ~ v4_pre_topc('#skF_1'(A_255,B_256,k2_tops_2(u1_struct_0(B_256),u1_struct_0(A_255),C_257)),B_256)
      | ~ v1_compts_1(B_256)
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_256),u1_struct_0(A_255),C_257),A_255,B_256)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_256),u1_struct_0(A_255),C_257),u1_struct_0(A_255),u1_struct_0(B_256))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_256),u1_struct_0(A_255),C_257))
      | ~ l1_pre_topc(B_256)
      | ~ l1_pre_topc(A_255)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_256),u1_struct_0(A_255))))
      | ~ v1_funct_2(C_257,u1_struct_0(B_256),u1_struct_0(A_255))
      | ~ v1_funct_1(C_257) ) ),
    inference(resolution,[status(thm)],[c_406,c_36])).

tff(c_485,plain,
    ( v2_compts_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2')
    | ~ v1_compts_1('#skF_2')
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_404,c_483])).

tff(c_488,plain,
    ( v2_compts_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2')
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_60,c_66,c_96,c_112,c_52,c_485])).

tff(c_489,plain,(
    v2_compts_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_488])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_307,plain,(
    ! [A_160,C_161,D_162,B_163] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_160),u1_struct_0(C_161),D_162,B_163),C_161)
      | ~ v2_compts_1(B_163,A_160)
      | k2_relset_1(u1_struct_0(A_160),u1_struct_0(C_161),D_162) != k2_struct_0(C_161)
      | ~ v5_pre_topc(D_162,A_160,C_161)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_160),u1_struct_0(C_161))))
      | ~ v1_funct_2(D_162,u1_struct_0(A_160),u1_struct_0(C_161))
      | ~ v1_funct_1(D_162)
      | ~ l1_pre_topc(C_161)
      | v2_struct_0(C_161)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_315,plain,(
    ! [B_163] :
      ( v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',B_163),'#skF_3')
      | ~ v2_compts_1(B_163,'#skF_2')
      | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') != k2_struct_0('#skF_3')
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_307])).

tff(c_320,plain,(
    ! [B_163] :
      ( v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',B_163),'#skF_3')
      | ~ v2_compts_1(B_163,'#skF_2')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_58,c_56,c_42,c_46,c_315])).

tff(c_321,plain,(
    ! [B_163] :
      ( v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',B_163),'#skF_3')
      | ~ v2_compts_1(B_163,'#skF_2')
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_320])).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_50,plain,(
    v8_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k7_relset_1(A_1,B_2,C_3,D_4),k1_zfmisc_1(B_2))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [B_88,A_89] :
      ( v4_pre_topc(B_88,A_89)
      | ~ v2_compts_1(B_88,A_89)
      | ~ v8_pre_topc(A_89)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_156,plain,(
    ! [A_106,A_107,C_108,D_109] :
      ( v4_pre_topc(k7_relset_1(A_106,u1_struct_0(A_107),C_108,D_109),A_107)
      | ~ v2_compts_1(k7_relset_1(A_106,u1_struct_0(A_107),C_108,D_109),A_107)
      | ~ v8_pre_topc(A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,u1_struct_0(A_107)))) ) ),
    inference(resolution,[status(thm)],[c_2,c_97])).

tff(c_164,plain,(
    ! [D_109] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_109),'#skF_3')
      | ~ v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_109),'#skF_3')
      | ~ v8_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_156])).

tff(c_169,plain,(
    ! [D_109] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_109),'#skF_3')
      | ~ v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_109),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_164])).

tff(c_322,plain,(
    ! [B_164,A_165,C_166,D_167] :
      ( k8_relset_1(u1_struct_0(B_164),u1_struct_0(A_165),k2_tops_2(u1_struct_0(A_165),u1_struct_0(B_164),C_166),D_167) = k7_relset_1(u1_struct_0(A_165),u1_struct_0(B_164),C_166,D_167)
      | ~ v2_funct_1(C_166)
      | k2_relset_1(u1_struct_0(A_165),u1_struct_0(B_164),C_166) != k2_struct_0(B_164)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165),u1_struct_0(B_164))))
      | ~ v1_funct_2(C_166,u1_struct_0(A_165),u1_struct_0(B_164))
      | ~ v1_funct_1(C_166)
      | ~ l1_struct_0(B_164)
      | ~ l1_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6,plain,(
    ! [A_5,B_17,C_23] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_5),u1_struct_0(B_17),C_23,'#skF_1'(A_5,B_17,C_23)),A_5)
      | v5_pre_topc(C_23,A_5,B_17)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5),u1_struct_0(B_17))))
      | ~ v1_funct_2(C_23,u1_struct_0(A_5),u1_struct_0(B_17))
      | ~ v1_funct_1(C_23)
      | ~ l1_pre_topc(B_17)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_522,plain,(
    ! [A_294,B_295,C_296] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_294),u1_struct_0(B_295),C_296,'#skF_1'(B_295,A_294,k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_295),C_296))),B_295)
      | v5_pre_topc(k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_295),C_296),B_295,A_294)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_295),C_296),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_295),u1_struct_0(A_294))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_295),C_296),u1_struct_0(B_295),u1_struct_0(A_294))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_295),C_296))
      | ~ l1_pre_topc(A_294)
      | ~ l1_pre_topc(B_295)
      | ~ v2_funct_1(C_296)
      | k2_relset_1(u1_struct_0(A_294),u1_struct_0(B_295),C_296) != k2_struct_0(B_295)
      | ~ m1_subset_1('#skF_1'(B_295,A_294,k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_295),C_296)),k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_294),u1_struct_0(B_295))))
      | ~ v1_funct_2(C_296,u1_struct_0(A_294),u1_struct_0(B_295))
      | ~ v1_funct_1(C_296)
      | ~ l1_struct_0(B_295)
      | ~ l1_struct_0(A_294) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_6])).

tff(c_534,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') != k2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))),'#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_522])).

tff(c_539,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_46,c_44,c_60,c_66,c_96,c_112,c_534])).

tff(c_540,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_539])).

tff(c_541,plain,(
    ~ v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_544,plain,
    ( ~ v2_compts_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_321,c_541])).

tff(c_547,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_544])).

tff(c_550,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_216,c_547])).

tff(c_553,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_60,c_66,c_96,c_112,c_550])).

tff(c_555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_553])).

tff(c_556,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_558,plain,(
    ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_556])).

tff(c_561,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_558])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_561])).

tff(c_567,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_10,plain,(
    ! [A_5,B_17,C_23] :
      ( m1_subset_1('#skF_1'(A_5,B_17,C_23),k1_zfmisc_1(u1_struct_0(B_17)))
      | v5_pre_topc(C_23,A_5,B_17)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5),u1_struct_0(B_17))))
      | ~ v1_funct_2(C_23,u1_struct_0(A_5),u1_struct_0(B_17))
      | ~ v1_funct_1(C_23)
      | ~ l1_pre_topc(B_17)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_580,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_567,c_10])).

tff(c_616,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_66,c_96,c_112,c_580])).

tff(c_617,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_405,c_616])).

tff(c_566,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_692,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_566])).

tff(c_693,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_692])).

tff(c_696,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_693])).

tff(c_700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_696])).

tff(c_701,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_705,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_701])).

tff(c_709,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:32:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.63  
% 3.72/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.63  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v4_pre_topc > v2_compts_1 > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.72/1.63  
% 3.72/1.63  %Foreground sorts:
% 3.72/1.63  
% 3.72/1.63  
% 3.72/1.63  %Background operators:
% 3.72/1.63  
% 3.72/1.63  
% 3.72/1.63  %Foreground operators:
% 3.72/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.72/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.72/1.63  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.72/1.63  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.72/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.72/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.72/1.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.72/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.63  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.72/1.63  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 3.72/1.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.72/1.63  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.72/1.63  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.72/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.72/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.72/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.72/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.72/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.72/1.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.72/1.63  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.72/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.72/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.72/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.63  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.72/1.63  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.72/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.72/1.63  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 3.72/1.63  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.72/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.72/1.63  
% 4.06/1.65  tff(f_195, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((((v1_compts_1(A) & v8_pre_topc(B)) & (k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A))) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) => v3_tops_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_compts_1)).
% 4.06/1.65  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.06/1.65  tff(f_90, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 4.06/1.65  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 4.06/1.65  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 4.06/1.65  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_compts_1(A) & v4_pre_topc(B, A)) => v2_compts_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_compts_1)).
% 4.06/1.65  tff(f_161, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(C))))) => (((v5_pre_topc(D, A, C) & (k2_relset_1(u1_struct_0(A), u1_struct_0(C), D) = k2_struct_0(C))) & v2_compts_1(B, A)) => v2_compts_1(k7_relset_1(u1_struct_0(A), u1_struct_0(C), D, B), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_compts_1)).
% 4.06/1.65  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.06/1.65  tff(f_124, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 4.06/1.65  tff(f_111, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k8_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tops_2)).
% 4.06/1.65  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_12, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.06/1.65  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_40, plain, (~v3_tops_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_56, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_48, plain, (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_46, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_44, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_42, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_85, plain, (![A_85, B_86, C_87]: (v1_funct_1(k2_tops_2(A_85, B_86, C_87)) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_87, A_85, B_86) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.65  tff(c_92, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_85])).
% 4.06/1.65  tff(c_96, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_92])).
% 4.06/1.65  tff(c_103, plain, (![A_90, B_91, C_92]: (v1_funct_2(k2_tops_2(A_90, B_91, C_92), B_91, A_90) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))) | ~v1_funct_2(C_92, A_90, B_91) | ~v1_funct_1(C_92))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.65  tff(c_108, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_103])).
% 4.06/1.65  tff(c_112, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_108])).
% 4.06/1.65  tff(c_26, plain, (![A_35, B_36, C_37]: (m1_subset_1(k2_tops_2(A_35, B_36, C_37), k1_zfmisc_1(k2_zfmisc_1(B_36, A_35))) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_2(C_37, A_35, B_36) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.06/1.65  tff(c_176, plain, (![A_111, B_112, C_113]: (v4_pre_topc('#skF_1'(A_111, B_112, C_113), B_112) | v5_pre_topc(C_113, A_111, B_112) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111), u1_struct_0(B_112)))) | ~v1_funct_2(C_113, u1_struct_0(A_111), u1_struct_0(B_112)) | ~v1_funct_1(C_113) | ~l1_pre_topc(B_112) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.06/1.65  tff(c_373, plain, (![A_181, B_182, C_183]: (v4_pre_topc('#skF_1'(A_181, B_182, k2_tops_2(u1_struct_0(B_182), u1_struct_0(A_181), C_183)), B_182) | v5_pre_topc(k2_tops_2(u1_struct_0(B_182), u1_struct_0(A_181), C_183), A_181, B_182) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_182), u1_struct_0(A_181), C_183), u1_struct_0(A_181), u1_struct_0(B_182)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_182), u1_struct_0(A_181), C_183)) | ~l1_pre_topc(B_182) | ~l1_pre_topc(A_181) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_182), u1_struct_0(A_181)))) | ~v1_funct_2(C_183, u1_struct_0(B_182), u1_struct_0(A_181)) | ~v1_funct_1(C_183))), inference(resolution, [status(thm)], [c_26, c_176])).
% 4.06/1.65  tff(c_381, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2') | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_112, c_373])).
% 4.06/1.65  tff(c_386, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2') | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_60, c_66, c_96, c_381])).
% 4.06/1.65  tff(c_387, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_386])).
% 4.06/1.65  tff(c_14, plain, (![C_34, A_28, B_32]: (v3_tops_2(C_34, A_28, B_32) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_28), u1_struct_0(B_32), C_34), B_32, A_28) | ~v5_pre_topc(C_34, A_28, B_32) | ~v2_funct_1(C_34) | k2_relset_1(u1_struct_0(A_28), u1_struct_0(B_32), C_34)!=k2_struct_0(B_32) | k1_relset_1(u1_struct_0(A_28), u1_struct_0(B_32), C_34)!=k2_struct_0(A_28) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_28), u1_struct_0(B_32)))) | ~v1_funct_2(C_34, u1_struct_0(A_28), u1_struct_0(B_32)) | ~v1_funct_1(C_34) | ~l1_pre_topc(B_32) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.06/1.65  tff(c_398, plain, (v3_tops_2('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v2_funct_1('#skF_4') | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_387, c_14])).
% 4.06/1.65  tff(c_401, plain, (v3_tops_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_58, c_56, c_54, c_48, c_46, c_44, c_42, c_398])).
% 4.06/1.65  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_401])).
% 4.06/1.65  tff(c_405, plain, (~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_386])).
% 4.06/1.65  tff(c_207, plain, (![A_117, B_118, C_119]: (m1_subset_1('#skF_1'(A_117, B_118, C_119), k1_zfmisc_1(u1_struct_0(B_118))) | v5_pre_topc(C_119, A_117, B_118) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117), u1_struct_0(B_118)))) | ~v1_funct_2(C_119, u1_struct_0(A_117), u1_struct_0(B_118)) | ~v1_funct_1(C_119) | ~l1_pre_topc(B_118) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.06/1.65  tff(c_216, plain, (![A_117, B_118, C_37]: (m1_subset_1('#skF_1'(A_117, B_118, k2_tops_2(u1_struct_0(B_118), u1_struct_0(A_117), C_37)), k1_zfmisc_1(u1_struct_0(B_118))) | v5_pre_topc(k2_tops_2(u1_struct_0(B_118), u1_struct_0(A_117), C_37), A_117, B_118) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_118), u1_struct_0(A_117), C_37), u1_struct_0(A_117), u1_struct_0(B_118)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_118), u1_struct_0(A_117), C_37)) | ~l1_pre_topc(B_118) | ~l1_pre_topc(A_117) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_118), u1_struct_0(A_117)))) | ~v1_funct_2(C_37, u1_struct_0(B_118), u1_struct_0(A_117)) | ~v1_funct_1(C_37))), inference(resolution, [status(thm)], [c_26, c_207])).
% 4.06/1.65  tff(c_52, plain, (v1_compts_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_404, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_386])).
% 4.06/1.65  tff(c_406, plain, (![A_187, B_188, C_189]: (m1_subset_1('#skF_1'(A_187, B_188, k2_tops_2(u1_struct_0(B_188), u1_struct_0(A_187), C_189)), k1_zfmisc_1(u1_struct_0(B_188))) | v5_pre_topc(k2_tops_2(u1_struct_0(B_188), u1_struct_0(A_187), C_189), A_187, B_188) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_188), u1_struct_0(A_187), C_189), u1_struct_0(A_187), u1_struct_0(B_188)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_188), u1_struct_0(A_187), C_189)) | ~l1_pre_topc(B_188) | ~l1_pre_topc(A_187) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_188), u1_struct_0(A_187)))) | ~v1_funct_2(C_189, u1_struct_0(B_188), u1_struct_0(A_187)) | ~v1_funct_1(C_189))), inference(resolution, [status(thm)], [c_26, c_207])).
% 4.06/1.65  tff(c_36, plain, (![B_58, A_56]: (v2_compts_1(B_58, A_56) | ~v4_pre_topc(B_58, A_56) | ~v1_compts_1(A_56) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.06/1.65  tff(c_483, plain, (![A_255, B_256, C_257]: (v2_compts_1('#skF_1'(A_255, B_256, k2_tops_2(u1_struct_0(B_256), u1_struct_0(A_255), C_257)), B_256) | ~v4_pre_topc('#skF_1'(A_255, B_256, k2_tops_2(u1_struct_0(B_256), u1_struct_0(A_255), C_257)), B_256) | ~v1_compts_1(B_256) | v5_pre_topc(k2_tops_2(u1_struct_0(B_256), u1_struct_0(A_255), C_257), A_255, B_256) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_256), u1_struct_0(A_255), C_257), u1_struct_0(A_255), u1_struct_0(B_256)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_256), u1_struct_0(A_255), C_257)) | ~l1_pre_topc(B_256) | ~l1_pre_topc(A_255) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_256), u1_struct_0(A_255)))) | ~v1_funct_2(C_257, u1_struct_0(B_256), u1_struct_0(A_255)) | ~v1_funct_1(C_257))), inference(resolution, [status(thm)], [c_406, c_36])).
% 4.06/1.65  tff(c_485, plain, (v2_compts_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2') | ~v1_compts_1('#skF_2') | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_404, c_483])).
% 4.06/1.65  tff(c_488, plain, (v2_compts_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2') | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_60, c_66, c_96, c_112, c_52, c_485])).
% 4.06/1.65  tff(c_489, plain, (v2_compts_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_405, c_488])).
% 4.06/1.65  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_307, plain, (![A_160, C_161, D_162, B_163]: (v2_compts_1(k7_relset_1(u1_struct_0(A_160), u1_struct_0(C_161), D_162, B_163), C_161) | ~v2_compts_1(B_163, A_160) | k2_relset_1(u1_struct_0(A_160), u1_struct_0(C_161), D_162)!=k2_struct_0(C_161) | ~v5_pre_topc(D_162, A_160, C_161) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_160), u1_struct_0(C_161)))) | ~v1_funct_2(D_162, u1_struct_0(A_160), u1_struct_0(C_161)) | ~v1_funct_1(D_162) | ~l1_pre_topc(C_161) | v2_struct_0(C_161) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.06/1.65  tff(c_315, plain, (![B_163]: (v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', B_163), '#skF_3') | ~v2_compts_1(B_163, '#skF_2') | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')!=k2_struct_0('#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_307])).
% 4.06/1.65  tff(c_320, plain, (![B_163]: (v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', B_163), '#skF_3') | ~v2_compts_1(B_163, '#skF_2') | v2_struct_0('#skF_3') | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_58, c_56, c_42, c_46, c_315])).
% 4.06/1.65  tff(c_321, plain, (![B_163]: (v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', B_163), '#skF_3') | ~v2_compts_1(B_163, '#skF_2') | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_320])).
% 4.06/1.65  tff(c_62, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_50, plain, (v8_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.06/1.65  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (m1_subset_1(k7_relset_1(A_1, B_2, C_3, D_4), k1_zfmisc_1(B_2)) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.06/1.65  tff(c_97, plain, (![B_88, A_89]: (v4_pre_topc(B_88, A_89) | ~v2_compts_1(B_88, A_89) | ~v8_pre_topc(A_89) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.06/1.65  tff(c_156, plain, (![A_106, A_107, C_108, D_109]: (v4_pre_topc(k7_relset_1(A_106, u1_struct_0(A_107), C_108, D_109), A_107) | ~v2_compts_1(k7_relset_1(A_106, u1_struct_0(A_107), C_108, D_109), A_107) | ~v8_pre_topc(A_107) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, u1_struct_0(A_107)))))), inference(resolution, [status(thm)], [c_2, c_97])).
% 4.06/1.65  tff(c_164, plain, (![D_109]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_109), '#skF_3') | ~v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_109), '#skF_3') | ~v8_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_156])).
% 4.06/1.65  tff(c_169, plain, (![D_109]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_109), '#skF_3') | ~v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_109), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_164])).
% 4.06/1.65  tff(c_322, plain, (![B_164, A_165, C_166, D_167]: (k8_relset_1(u1_struct_0(B_164), u1_struct_0(A_165), k2_tops_2(u1_struct_0(A_165), u1_struct_0(B_164), C_166), D_167)=k7_relset_1(u1_struct_0(A_165), u1_struct_0(B_164), C_166, D_167) | ~v2_funct_1(C_166) | k2_relset_1(u1_struct_0(A_165), u1_struct_0(B_164), C_166)!=k2_struct_0(B_164) | ~m1_subset_1(D_167, k1_zfmisc_1(u1_struct_0(A_165))) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_165), u1_struct_0(B_164)))) | ~v1_funct_2(C_166, u1_struct_0(A_165), u1_struct_0(B_164)) | ~v1_funct_1(C_166) | ~l1_struct_0(B_164) | ~l1_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.06/1.65  tff(c_6, plain, (![A_5, B_17, C_23]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_5), u1_struct_0(B_17), C_23, '#skF_1'(A_5, B_17, C_23)), A_5) | v5_pre_topc(C_23, A_5, B_17) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5), u1_struct_0(B_17)))) | ~v1_funct_2(C_23, u1_struct_0(A_5), u1_struct_0(B_17)) | ~v1_funct_1(C_23) | ~l1_pre_topc(B_17) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.06/1.65  tff(c_522, plain, (![A_294, B_295, C_296]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_294), u1_struct_0(B_295), C_296, '#skF_1'(B_295, A_294, k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_295), C_296))), B_295) | v5_pre_topc(k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_295), C_296), B_295, A_294) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_295), C_296), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_295), u1_struct_0(A_294)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_295), C_296), u1_struct_0(B_295), u1_struct_0(A_294)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_295), C_296)) | ~l1_pre_topc(A_294) | ~l1_pre_topc(B_295) | ~v2_funct_1(C_296) | k2_relset_1(u1_struct_0(A_294), u1_struct_0(B_295), C_296)!=k2_struct_0(B_295) | ~m1_subset_1('#skF_1'(B_295, A_294, k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_295), C_296)), k1_zfmisc_1(u1_struct_0(A_294))) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_294), u1_struct_0(B_295)))) | ~v1_funct_2(C_296, u1_struct_0(A_294), u1_struct_0(B_295)) | ~v1_funct_1(C_296) | ~l1_struct_0(B_295) | ~l1_struct_0(A_294))), inference(superposition, [status(thm), theory('equality')], [c_322, c_6])).
% 4.06/1.65  tff(c_534, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_funct_1('#skF_4') | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')!=k2_struct_0('#skF_3') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | ~v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'))), '#skF_3')), inference(resolution, [status(thm)], [c_169, c_522])).
% 4.06/1.65  tff(c_539, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | ~v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'))), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_46, c_44, c_60, c_66, c_96, c_112, c_534])).
% 4.06/1.65  tff(c_540, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | ~v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'))), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_405, c_539])).
% 4.06/1.65  tff(c_541, plain, (~v2_compts_1(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'))), '#skF_3')), inference(splitLeft, [status(thm)], [c_540])).
% 4.06/1.65  tff(c_544, plain, (~v2_compts_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_321, c_541])).
% 4.06/1.65  tff(c_547, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_489, c_544])).
% 4.06/1.65  tff(c_550, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_216, c_547])).
% 4.06/1.66  tff(c_553, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_60, c_66, c_96, c_112, c_550])).
% 4.06/1.66  tff(c_555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_405, c_553])).
% 4.06/1.66  tff(c_556, plain, (~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_540])).
% 4.06/1.66  tff(c_558, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_556])).
% 4.06/1.66  tff(c_561, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_558])).
% 4.06/1.66  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_561])).
% 4.06/1.66  tff(c_567, plain, (m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_556])).
% 4.06/1.66  tff(c_10, plain, (![A_5, B_17, C_23]: (m1_subset_1('#skF_1'(A_5, B_17, C_23), k1_zfmisc_1(u1_struct_0(B_17))) | v5_pre_topc(C_23, A_5, B_17) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5), u1_struct_0(B_17)))) | ~v1_funct_2(C_23, u1_struct_0(A_5), u1_struct_0(B_17)) | ~v1_funct_1(C_23) | ~l1_pre_topc(B_17) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.06/1.66  tff(c_580, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_567, c_10])).
% 4.06/1.66  tff(c_616, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_66, c_96, c_112, c_580])).
% 4.06/1.66  tff(c_617, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_405, c_616])).
% 4.06/1.66  tff(c_566, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_556])).
% 4.06/1.66  tff(c_692, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_566])).
% 4.06/1.66  tff(c_693, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_692])).
% 4.06/1.66  tff(c_696, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_693])).
% 4.06/1.66  tff(c_700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_696])).
% 4.06/1.66  tff(c_701, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_692])).
% 4.06/1.66  tff(c_705, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_701])).
% 4.06/1.66  tff(c_709, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_705])).
% 4.06/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.66  
% 4.06/1.66  Inference rules
% 4.06/1.66  ----------------------
% 4.06/1.66  #Ref     : 0
% 4.06/1.66  #Sup     : 117
% 4.06/1.66  #Fact    : 0
% 4.06/1.66  #Define  : 0
% 4.06/1.66  #Split   : 5
% 4.06/1.66  #Chain   : 0
% 4.06/1.66  #Close   : 0
% 4.06/1.66  
% 4.06/1.66  Ordering : KBO
% 4.06/1.66  
% 4.06/1.66  Simplification rules
% 4.06/1.66  ----------------------
% 4.06/1.66  #Subsume      : 19
% 4.06/1.66  #Demod        : 219
% 4.06/1.66  #Tautology    : 24
% 4.06/1.66  #SimpNegUnit  : 8
% 4.06/1.66  #BackRed      : 0
% 4.06/1.66  
% 4.06/1.66  #Partial instantiations: 0
% 4.06/1.66  #Strategies tried      : 1
% 4.06/1.66  
% 4.06/1.66  Timing (in seconds)
% 4.06/1.66  ----------------------
% 4.06/1.66  Preprocessing        : 0.37
% 4.06/1.66  Parsing              : 0.20
% 4.06/1.66  CNF conversion       : 0.03
% 4.06/1.66  Main loop            : 0.52
% 4.06/1.66  Inferencing          : 0.21
% 4.06/1.66  Reduction            : 0.15
% 4.06/1.66  Demodulation         : 0.11
% 4.06/1.66  BG Simplification    : 0.03
% 4.06/1.66  Subsumption          : 0.10
% 4.06/1.66  Abstraction          : 0.02
% 4.06/1.66  MUC search           : 0.00
% 4.06/1.66  Cooper               : 0.00
% 4.06/1.66  Total                : 0.93
% 4.06/1.66  Index Insertion      : 0.00
% 4.06/1.66  Index Deletion       : 0.00
% 4.06/1.66  Index Matching       : 0.00
% 4.06/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
