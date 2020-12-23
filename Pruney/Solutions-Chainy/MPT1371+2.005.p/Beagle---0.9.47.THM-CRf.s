%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:01 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 787 expanded)
%              Number of leaves         :   36 ( 333 expanded)
%              Depth                    :   13
%              Number of atoms          :  290 (5274 expanded)
%              Number of equality atoms :   19 ( 524 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v4_pre_topc > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

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

tff(f_175,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_46,axiom,(
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

tff(f_74,axiom,(
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

tff(f_141,axiom,(
    ! [A] :
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
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v5_pre_topc(C,A,B) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( v4_pre_topc(D,A)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).

tff(f_107,axiom,(
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

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_10,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_24,plain,(
    ! [A_31,B_32,C_33] :
      ( m1_subset_1(k2_tops_2(A_31,B_32,C_33),k1_zfmisc_1(k2_zfmisc_1(B_32,A_31)))
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ~ v3_tops_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_42,plain,(
    k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_40,plain,(
    k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_38,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_36,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_72,plain,(
    ! [A_69,B_70,C_71] :
      ( v1_funct_1(k2_tops_2(A_69,B_70,C_71))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_funct_2(C_71,A_69,B_70)
      | ~ v1_funct_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_75,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_72])).

tff(c_78,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_75])).

tff(c_79,plain,(
    ! [A_72,B_73,C_74] :
      ( v1_funct_2(k2_tops_2(A_72,B_73,C_74),B_73,A_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_2(C_74,A_72,B_73)
      | ~ v1_funct_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_79])).

tff(c_84,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_81])).

tff(c_117,plain,(
    ! [A_84,B_85,C_86] :
      ( v4_pre_topc('#skF_1'(A_84,B_85,C_86),B_85)
      | v5_pre_topc(C_86,A_84,B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84),u1_struct_0(B_85))))
      | ~ v1_funct_2(C_86,u1_struct_0(A_84),u1_struct_0(B_85))
      | ~ v1_funct_1(C_86)
      | ~ l1_pre_topc(B_85)
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_240,plain,(
    ! [A_129,B_130,C_131] :
      ( v4_pre_topc('#skF_1'(A_129,B_130,k2_tops_2(u1_struct_0(B_130),u1_struct_0(A_129),C_131)),B_130)
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_130),u1_struct_0(A_129),C_131),A_129,B_130)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_130),u1_struct_0(A_129),C_131),u1_struct_0(A_129),u1_struct_0(B_130))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_130),u1_struct_0(A_129),C_131))
      | ~ l1_pre_topc(B_130)
      | ~ l1_pre_topc(A_129)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_130),u1_struct_0(A_129))))
      | ~ v1_funct_2(C_131,u1_struct_0(B_130),u1_struct_0(A_129))
      | ~ v1_funct_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_24,c_117])).

tff(c_245,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2')
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_240])).

tff(c_249,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2')
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_54,c_60,c_78,c_245])).

tff(c_250,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_12,plain,(
    ! [C_30,A_24,B_28] :
      ( v3_tops_2(C_30,A_24,B_28)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_24),u1_struct_0(B_28),C_30),B_28,A_24)
      | ~ v5_pre_topc(C_30,A_24,B_28)
      | ~ v2_funct_1(C_30)
      | k2_relset_1(u1_struct_0(A_24),u1_struct_0(B_28),C_30) != k2_struct_0(B_28)
      | k1_relset_1(u1_struct_0(A_24),u1_struct_0(B_28),C_30) != k2_struct_0(A_24)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_24),u1_struct_0(B_28))))
      | ~ v1_funct_2(C_30,u1_struct_0(A_24),u1_struct_0(B_28))
      | ~ v1_funct_1(C_30)
      | ~ l1_pre_topc(B_28)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_252,plain,
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
    inference(resolution,[status(thm)],[c_250,c_12])).

tff(c_255,plain,(
    v3_tops_2('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_52,c_50,c_48,c_42,c_40,c_38,c_36,c_252])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_255])).

tff(c_259,plain,(
    ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_127,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1('#skF_1'(A_87,B_88,C_89),k1_zfmisc_1(u1_struct_0(B_88)))
      | v5_pre_topc(C_89,A_87,B_88)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_87),u1_struct_0(B_88))))
      | ~ v1_funct_2(C_89,u1_struct_0(A_87),u1_struct_0(B_88))
      | ~ v1_funct_1(C_89)
      | ~ l1_pre_topc(B_88)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_133,plain,(
    ! [A_87,B_88,C_33] :
      ( m1_subset_1('#skF_1'(A_87,B_88,k2_tops_2(u1_struct_0(B_88),u1_struct_0(A_87),C_33)),k1_zfmisc_1(u1_struct_0(B_88)))
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_88),u1_struct_0(A_87),C_33),A_87,B_88)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_88),u1_struct_0(A_87),C_33),u1_struct_0(A_87),u1_struct_0(B_88))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_88),u1_struct_0(A_87),C_33))
      | ~ l1_pre_topc(B_88)
      | ~ l1_pre_topc(A_87)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_88),u1_struct_0(A_87))))
      | ~ v1_funct_2(C_33,u1_struct_0(B_88),u1_struct_0(A_87))
      | ~ v1_funct_1(C_33) ) ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_258,plain,(
    v4_pre_topc('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_46,plain,(
    v1_compts_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_44,plain,(
    v8_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_260,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_132),u1_struct_0(B_133),C_134,D_135),B_133)
      | ~ v4_pre_topc(D_135,A_132)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ v5_pre_topc(C_134,A_132,B_133)
      | k2_relset_1(u1_struct_0(A_132),u1_struct_0(B_133),C_134) != k2_struct_0(B_133)
      | ~ v8_pre_topc(B_133)
      | ~ v1_compts_1(A_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132),u1_struct_0(B_133))))
      | ~ v1_funct_2(C_134,u1_struct_0(A_132),u1_struct_0(B_133))
      | ~ v1_funct_1(C_134)
      | ~ l1_pre_topc(B_133)
      | ~ v2_pre_topc(B_133)
      | v2_struct_0(B_133)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_265,plain,(
    ! [D_135] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_135),'#skF_3')
      | ~ v4_pre_topc(D_135,'#skF_2')
      | ~ m1_subset_1(D_135,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') != k2_struct_0('#skF_3')
      | ~ v8_pre_topc('#skF_3')
      | ~ v1_compts_1('#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_260])).

tff(c_269,plain,(
    ! [D_135] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_135),'#skF_3')
      | ~ v4_pre_topc(D_135,'#skF_2')
      | ~ m1_subset_1(D_135,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_50,c_46,c_44,c_40,c_36,c_265])).

tff(c_270,plain,(
    ! [D_135] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_135),'#skF_3')
      | ~ v4_pre_topc(D_135,'#skF_2')
      | ~ m1_subset_1(D_135,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_269])).

tff(c_201,plain,(
    ! [B_116,A_117,C_118,D_119] :
      ( k8_relset_1(u1_struct_0(B_116),u1_struct_0(A_117),k2_tops_2(u1_struct_0(A_117),u1_struct_0(B_116),C_118),D_119) = k7_relset_1(u1_struct_0(A_117),u1_struct_0(B_116),C_118,D_119)
      | ~ v2_funct_1(C_118)
      | k2_relset_1(u1_struct_0(A_117),u1_struct_0(B_116),C_118) != k2_struct_0(B_116)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117),u1_struct_0(B_116))))
      | ~ v1_funct_2(C_118,u1_struct_0(A_117),u1_struct_0(B_116))
      | ~ v1_funct_1(C_118)
      | ~ l1_struct_0(B_116)
      | ~ l1_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4,plain,(
    ! [A_1,B_13,C_19] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_1),u1_struct_0(B_13),C_19,'#skF_1'(A_1,B_13,C_19)),A_1)
      | v5_pre_topc(C_19,A_1,B_13)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1),u1_struct_0(B_13))))
      | ~ v1_funct_2(C_19,u1_struct_0(A_1),u1_struct_0(B_13))
      | ~ v1_funct_1(C_19)
      | ~ l1_pre_topc(B_13)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_350,plain,(
    ! [A_179,B_180,C_181] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_179),u1_struct_0(B_180),C_181,'#skF_1'(B_180,A_179,k2_tops_2(u1_struct_0(A_179),u1_struct_0(B_180),C_181))),B_180)
      | v5_pre_topc(k2_tops_2(u1_struct_0(A_179),u1_struct_0(B_180),C_181),B_180,A_179)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_179),u1_struct_0(B_180),C_181),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_180),u1_struct_0(A_179))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_179),u1_struct_0(B_180),C_181),u1_struct_0(B_180),u1_struct_0(A_179))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_179),u1_struct_0(B_180),C_181))
      | ~ l1_pre_topc(A_179)
      | ~ l1_pre_topc(B_180)
      | ~ v2_funct_1(C_181)
      | k2_relset_1(u1_struct_0(A_179),u1_struct_0(B_180),C_181) != k2_struct_0(B_180)
      | ~ m1_subset_1('#skF_1'(B_180,A_179,k2_tops_2(u1_struct_0(A_179),u1_struct_0(B_180),C_181)),k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_179),u1_struct_0(B_180))))
      | ~ v1_funct_2(C_181,u1_struct_0(A_179),u1_struct_0(B_180))
      | ~ v1_funct_1(C_181)
      | ~ l1_struct_0(B_180)
      | ~ l1_struct_0(A_179) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_4])).

tff(c_358,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4') != k2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_270,c_350])).

tff(c_362,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_52,c_50,c_48,c_40,c_38,c_54,c_60,c_78,c_84,c_358])).

tff(c_363,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_362])).

tff(c_364,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2',k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_363])).

tff(c_367,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_364])).

tff(c_370,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_54,c_60,c_78,c_84,c_367])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_370])).

tff(c_373,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_375,plain,(
    ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_373])).

tff(c_378,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_375])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_378])).

tff(c_383,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_373])).

tff(c_385,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_388,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_385])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_388])).

tff(c_393,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_465,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_393])).

tff(c_469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.50  
% 3.31/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.50  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v4_pre_topc > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.31/1.50  
% 3.31/1.50  %Foreground sorts:
% 3.31/1.50  
% 3.31/1.50  
% 3.31/1.50  %Background operators:
% 3.31/1.50  
% 3.31/1.50  
% 3.31/1.50  %Foreground operators:
% 3.31/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.31/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.31/1.50  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.31/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.31/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.50  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.31/1.50  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 3.31/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.31/1.50  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.31/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.31/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.31/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.31/1.50  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.50  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.31/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.31/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.50  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 3.31/1.50  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.31/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.50  
% 3.31/1.52  tff(f_175, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((((v1_compts_1(A) & v8_pre_topc(B)) & (k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A))) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) => v3_tops_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_compts_1)).
% 3.31/1.52  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.31/1.52  tff(f_86, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 3.31/1.52  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 3.31/1.52  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 3.31/1.52  tff(f_141, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_compts_1(A) & v8_pre_topc(B)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v5_pre_topc(C, A, B)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(D, A) => v4_pre_topc(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_compts_1)).
% 3.31/1.52  tff(f_107, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k8_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tops_2)).
% 3.31/1.52  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_10, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.31/1.52  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_50, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_24, plain, (![A_31, B_32, C_33]: (m1_subset_1(k2_tops_2(A_31, B_32, C_33), k1_zfmisc_1(k2_zfmisc_1(B_32, A_31))) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.31/1.52  tff(c_34, plain, (~v3_tops_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_42, plain, (k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_40, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_38, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_36, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_72, plain, (![A_69, B_70, C_71]: (v1_funct_1(k2_tops_2(A_69, B_70, C_71)) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_funct_2(C_71, A_69, B_70) | ~v1_funct_1(C_71))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.31/1.52  tff(c_75, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_72])).
% 3.31/1.52  tff(c_78, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_75])).
% 3.31/1.52  tff(c_79, plain, (![A_72, B_73, C_74]: (v1_funct_2(k2_tops_2(A_72, B_73, C_74), B_73, A_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_2(C_74, A_72, B_73) | ~v1_funct_1(C_74))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.31/1.52  tff(c_81, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_79])).
% 3.31/1.52  tff(c_84, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_81])).
% 3.31/1.52  tff(c_117, plain, (![A_84, B_85, C_86]: (v4_pre_topc('#skF_1'(A_84, B_85, C_86), B_85) | v5_pre_topc(C_86, A_84, B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_84), u1_struct_0(B_85)))) | ~v1_funct_2(C_86, u1_struct_0(A_84), u1_struct_0(B_85)) | ~v1_funct_1(C_86) | ~l1_pre_topc(B_85) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.31/1.52  tff(c_240, plain, (![A_129, B_130, C_131]: (v4_pre_topc('#skF_1'(A_129, B_130, k2_tops_2(u1_struct_0(B_130), u1_struct_0(A_129), C_131)), B_130) | v5_pre_topc(k2_tops_2(u1_struct_0(B_130), u1_struct_0(A_129), C_131), A_129, B_130) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_130), u1_struct_0(A_129), C_131), u1_struct_0(A_129), u1_struct_0(B_130)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_130), u1_struct_0(A_129), C_131)) | ~l1_pre_topc(B_130) | ~l1_pre_topc(A_129) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_130), u1_struct_0(A_129)))) | ~v1_funct_2(C_131, u1_struct_0(B_130), u1_struct_0(A_129)) | ~v1_funct_1(C_131))), inference(resolution, [status(thm)], [c_24, c_117])).
% 3.31/1.52  tff(c_245, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2') | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_240])).
% 3.31/1.52  tff(c_249, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2') | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_54, c_60, c_78, c_245])).
% 3.31/1.52  tff(c_250, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_249])).
% 3.31/1.52  tff(c_12, plain, (![C_30, A_24, B_28]: (v3_tops_2(C_30, A_24, B_28) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_24), u1_struct_0(B_28), C_30), B_28, A_24) | ~v5_pre_topc(C_30, A_24, B_28) | ~v2_funct_1(C_30) | k2_relset_1(u1_struct_0(A_24), u1_struct_0(B_28), C_30)!=k2_struct_0(B_28) | k1_relset_1(u1_struct_0(A_24), u1_struct_0(B_28), C_30)!=k2_struct_0(A_24) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_24), u1_struct_0(B_28)))) | ~v1_funct_2(C_30, u1_struct_0(A_24), u1_struct_0(B_28)) | ~v1_funct_1(C_30) | ~l1_pre_topc(B_28) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.31/1.52  tff(c_252, plain, (v3_tops_2('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v2_funct_1('#skF_4') | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')!=k2_struct_0('#skF_3') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_250, c_12])).
% 3.31/1.52  tff(c_255, plain, (v3_tops_2('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_52, c_50, c_48, c_42, c_40, c_38, c_36, c_252])).
% 3.31/1.52  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_255])).
% 3.31/1.52  tff(c_259, plain, (~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_249])).
% 3.31/1.52  tff(c_127, plain, (![A_87, B_88, C_89]: (m1_subset_1('#skF_1'(A_87, B_88, C_89), k1_zfmisc_1(u1_struct_0(B_88))) | v5_pre_topc(C_89, A_87, B_88) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_87), u1_struct_0(B_88)))) | ~v1_funct_2(C_89, u1_struct_0(A_87), u1_struct_0(B_88)) | ~v1_funct_1(C_89) | ~l1_pre_topc(B_88) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.31/1.52  tff(c_133, plain, (![A_87, B_88, C_33]: (m1_subset_1('#skF_1'(A_87, B_88, k2_tops_2(u1_struct_0(B_88), u1_struct_0(A_87), C_33)), k1_zfmisc_1(u1_struct_0(B_88))) | v5_pre_topc(k2_tops_2(u1_struct_0(B_88), u1_struct_0(A_87), C_33), A_87, B_88) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_88), u1_struct_0(A_87), C_33), u1_struct_0(A_87), u1_struct_0(B_88)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_88), u1_struct_0(A_87), C_33)) | ~l1_pre_topc(B_88) | ~l1_pre_topc(A_87) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_88), u1_struct_0(A_87)))) | ~v1_funct_2(C_33, u1_struct_0(B_88), u1_struct_0(A_87)) | ~v1_funct_1(C_33))), inference(resolution, [status(thm)], [c_24, c_127])).
% 3.31/1.52  tff(c_258, plain, (v4_pre_topc('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_249])).
% 3.31/1.52  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_46, plain, (v1_compts_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_44, plain, (v8_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.31/1.52  tff(c_260, plain, (![A_132, B_133, C_134, D_135]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_132), u1_struct_0(B_133), C_134, D_135), B_133) | ~v4_pre_topc(D_135, A_132) | ~m1_subset_1(D_135, k1_zfmisc_1(u1_struct_0(A_132))) | ~v5_pre_topc(C_134, A_132, B_133) | k2_relset_1(u1_struct_0(A_132), u1_struct_0(B_133), C_134)!=k2_struct_0(B_133) | ~v8_pre_topc(B_133) | ~v1_compts_1(A_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_132), u1_struct_0(B_133)))) | ~v1_funct_2(C_134, u1_struct_0(A_132), u1_struct_0(B_133)) | ~v1_funct_1(C_134) | ~l1_pre_topc(B_133) | ~v2_pre_topc(B_133) | v2_struct_0(B_133) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.31/1.52  tff(c_265, plain, (![D_135]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_135), '#skF_3') | ~v4_pre_topc(D_135, '#skF_2') | ~m1_subset_1(D_135, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')!=k2_struct_0('#skF_3') | ~v8_pre_topc('#skF_3') | ~v1_compts_1('#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_260])).
% 3.31/1.52  tff(c_269, plain, (![D_135]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_135), '#skF_3') | ~v4_pre_topc(D_135, '#skF_2') | ~m1_subset_1(D_135, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_50, c_46, c_44, c_40, c_36, c_265])).
% 3.31/1.52  tff(c_270, plain, (![D_135]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_135), '#skF_3') | ~v4_pre_topc(D_135, '#skF_2') | ~m1_subset_1(D_135, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_269])).
% 3.31/1.52  tff(c_201, plain, (![B_116, A_117, C_118, D_119]: (k8_relset_1(u1_struct_0(B_116), u1_struct_0(A_117), k2_tops_2(u1_struct_0(A_117), u1_struct_0(B_116), C_118), D_119)=k7_relset_1(u1_struct_0(A_117), u1_struct_0(B_116), C_118, D_119) | ~v2_funct_1(C_118) | k2_relset_1(u1_struct_0(A_117), u1_struct_0(B_116), C_118)!=k2_struct_0(B_116) | ~m1_subset_1(D_119, k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_117), u1_struct_0(B_116)))) | ~v1_funct_2(C_118, u1_struct_0(A_117), u1_struct_0(B_116)) | ~v1_funct_1(C_118) | ~l1_struct_0(B_116) | ~l1_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.31/1.52  tff(c_4, plain, (![A_1, B_13, C_19]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_1), u1_struct_0(B_13), C_19, '#skF_1'(A_1, B_13, C_19)), A_1) | v5_pre_topc(C_19, A_1, B_13) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1), u1_struct_0(B_13)))) | ~v1_funct_2(C_19, u1_struct_0(A_1), u1_struct_0(B_13)) | ~v1_funct_1(C_19) | ~l1_pre_topc(B_13) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.31/1.52  tff(c_350, plain, (![A_179, B_180, C_181]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_179), u1_struct_0(B_180), C_181, '#skF_1'(B_180, A_179, k2_tops_2(u1_struct_0(A_179), u1_struct_0(B_180), C_181))), B_180) | v5_pre_topc(k2_tops_2(u1_struct_0(A_179), u1_struct_0(B_180), C_181), B_180, A_179) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_179), u1_struct_0(B_180), C_181), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_180), u1_struct_0(A_179)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_179), u1_struct_0(B_180), C_181), u1_struct_0(B_180), u1_struct_0(A_179)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_179), u1_struct_0(B_180), C_181)) | ~l1_pre_topc(A_179) | ~l1_pre_topc(B_180) | ~v2_funct_1(C_181) | k2_relset_1(u1_struct_0(A_179), u1_struct_0(B_180), C_181)!=k2_struct_0(B_180) | ~m1_subset_1('#skF_1'(B_180, A_179, k2_tops_2(u1_struct_0(A_179), u1_struct_0(B_180), C_181)), k1_zfmisc_1(u1_struct_0(A_179))) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_179), u1_struct_0(B_180)))) | ~v1_funct_2(C_181, u1_struct_0(A_179), u1_struct_0(B_180)) | ~v1_funct_1(C_181) | ~l1_struct_0(B_180) | ~l1_struct_0(A_179))), inference(superposition, [status(thm), theory('equality')], [c_201, c_4])).
% 3.31/1.52  tff(c_358, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_funct_1('#skF_4') | k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')!=k2_struct_0('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_270, c_350])).
% 3.31/1.52  tff(c_362, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_52, c_50, c_48, c_40, c_38, c_54, c_60, c_78, c_84, c_358])).
% 3.31/1.52  tff(c_363, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_259, c_362])).
% 3.31/1.52  tff(c_364, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_363])).
% 3.31/1.52  tff(c_367, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_364])).
% 3.31/1.52  tff(c_370, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_54, c_60, c_78, c_84, c_367])).
% 3.31/1.52  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_370])).
% 3.31/1.52  tff(c_373, plain, (~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_363])).
% 3.31/1.52  tff(c_375, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_373])).
% 3.31/1.52  tff(c_378, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_375])).
% 3.31/1.52  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_378])).
% 3.31/1.52  tff(c_383, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_373])).
% 3.31/1.52  tff(c_385, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_383])).
% 3.31/1.52  tff(c_388, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_385])).
% 3.31/1.52  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_388])).
% 3.31/1.52  tff(c_393, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_383])).
% 3.31/1.52  tff(c_465, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_393])).
% 3.31/1.52  tff(c_469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_465])).
% 3.31/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  Inference rules
% 3.31/1.52  ----------------------
% 3.31/1.52  #Ref     : 0
% 3.31/1.52  #Sup     : 72
% 3.31/1.52  #Fact    : 0
% 3.31/1.52  #Define  : 0
% 3.31/1.52  #Split   : 5
% 3.31/1.52  #Chain   : 0
% 3.31/1.52  #Close   : 0
% 3.31/1.52  
% 3.31/1.52  Ordering : KBO
% 3.31/1.52  
% 3.31/1.52  Simplification rules
% 3.31/1.52  ----------------------
% 3.31/1.52  #Subsume      : 17
% 3.31/1.52  #Demod        : 180
% 3.31/1.52  #Tautology    : 18
% 3.31/1.52  #SimpNegUnit  : 7
% 3.31/1.52  #BackRed      : 0
% 3.31/1.52  
% 3.31/1.52  #Partial instantiations: 0
% 3.31/1.52  #Strategies tried      : 1
% 3.31/1.52  
% 3.31/1.52  Timing (in seconds)
% 3.31/1.52  ----------------------
% 3.31/1.52  Preprocessing        : 0.36
% 3.31/1.52  Parsing              : 0.20
% 3.31/1.52  CNF conversion       : 0.03
% 3.31/1.52  Main loop            : 0.39
% 3.31/1.52  Inferencing          : 0.15
% 3.31/1.52  Reduction            : 0.12
% 3.31/1.52  Demodulation         : 0.09
% 3.31/1.52  BG Simplification    : 0.03
% 3.31/1.52  Subsumption          : 0.08
% 3.31/1.52  Abstraction          : 0.02
% 3.31/1.52  MUC search           : 0.00
% 3.31/1.53  Cooper               : 0.00
% 3.31/1.53  Total                : 0.79
% 3.31/1.53  Index Insertion      : 0.00
% 3.31/1.53  Index Deletion       : 0.00
% 3.31/1.53  Index Matching       : 0.00
% 3.31/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
