%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:00 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 412 expanded)
%              Number of leaves         :   36 ( 164 expanded)
%              Depth                    :   11
%              Number of atoms          :  235 (1528 expanded)
%              Number of equality atoms :   17 ( 188 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_143,negated_conjecture,(
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
                    & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v5_pre_topc(C,A,B) )
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ( v4_pre_topc(D,A)
                       => v4_pre_topc(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> v2_compts_1(k2_struct_0(A),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(f_108,axiom,(
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

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_12,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_12,c_54])).

tff(c_66,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_59])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_67,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_59])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_128,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_67,c_38])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_132,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_128,c_2])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_28])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_69,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_40])).

tff(c_84,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_69])).

tff(c_30,plain,(
    v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_32,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_79,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_66,c_32])).

tff(c_36,plain,(
    v1_compts_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_16,plain,(
    ! [A_10] :
      ( v2_compts_1(k2_struct_0(A_10),A_10)
      | ~ v1_compts_1(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,(
    ! [A_55] :
      ( m1_subset_1(k2_struct_0(A_55),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [A_57] :
      ( r1_tarski(k2_struct_0(A_57),u1_struct_0(A_57))
      | ~ l1_struct_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_114,plain,
    ( r1_tarski(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_111])).

tff(c_118,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_121,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_118])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_121])).

tff(c_127,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_26,plain,(
    v4_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_10,plain,(
    ! [A_8] :
      ( m1_subset_1(k2_struct_0(A_8),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,B_53)
      | ~ m1_subset_1(A_52,k1_zfmisc_1(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    r1_tarski('#skF_4',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_74,c_85])).

tff(c_212,plain,(
    ! [C_73,A_74,B_75] :
      ( v2_compts_1(C_73,A_74)
      | ~ v4_pre_topc(C_73,A_74)
      | ~ r1_tarski(C_73,B_75)
      | ~ v2_compts_1(B_75,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_373,plain,(
    ! [A_101] :
      ( v2_compts_1('#skF_4',A_101)
      | ~ v4_pre_topc('#skF_4',A_101)
      | ~ v2_compts_1(k2_struct_0('#skF_1'),A_101)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_92,c_212])).

tff(c_377,plain,
    ( v2_compts_1('#skF_4','#skF_1')
    | ~ v4_pre_topc('#skF_4','#skF_1')
    | ~ v2_compts_1(k2_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_373])).

tff(c_389,plain,
    ( v2_compts_1('#skF_4','#skF_1')
    | ~ v2_compts_1(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_52,c_50,c_74,c_67,c_26,c_377])).

tff(c_395,plain,(
    ~ v2_compts_1(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_398,plain,
    ( ~ v1_compts_1('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_395])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36,c_398])).

tff(c_403,plain,(
    v2_compts_1('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_292,plain,(
    ! [A_81,C_82,D_83,B_84] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_81),u1_struct_0(C_82),D_83,B_84),C_82)
      | ~ v2_compts_1(B_84,A_81)
      | k2_relset_1(u1_struct_0(A_81),u1_struct_0(C_82),D_83) != k2_struct_0(C_82)
      | ~ v5_pre_topc(D_83,A_81,C_82)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81),u1_struct_0(C_82))))
      | ~ v1_funct_2(D_83,u1_struct_0(A_81),u1_struct_0(C_82))
      | ~ v1_funct_1(D_83)
      | ~ l1_pre_topc(C_82)
      | v2_struct_0(C_82)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_303,plain,(
    ! [A_81,D_83,B_84] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_81),u1_struct_0('#skF_2'),D_83,B_84),'#skF_2')
      | ~ v2_compts_1(B_84,A_81)
      | k2_relset_1(u1_struct_0(A_81),u1_struct_0('#skF_2'),D_83) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(D_83,A_81,'#skF_2')
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_83,u1_struct_0(A_81),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_83)
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_292])).

tff(c_315,plain,(
    ! [A_81,D_83,B_84] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_81),k2_struct_0('#skF_2'),D_83,B_84),'#skF_2')
      | ~ v2_compts_1(B_84,A_81)
      | k2_relset_1(u1_struct_0(A_81),k2_struct_0('#skF_2'),D_83) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(D_83,A_81,'#skF_2')
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_83,u1_struct_0(A_81),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(D_83)
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_66,c_66,c_66,c_303])).

tff(c_337,plain,(
    ! [A_92,D_93,B_94] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_92),k2_struct_0('#skF_2'),D_93,B_94),'#skF_2')
      | ~ v2_compts_1(B_94,A_92)
      | k2_relset_1(u1_struct_0(A_92),k2_struct_0('#skF_2'),D_93) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(D_93,A_92,'#skF_2')
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_93,u1_struct_0(A_92),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(D_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_315])).

tff(c_430,plain,(
    ! [A_106,A_107,B_108] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(A_106),k2_struct_0('#skF_2'),A_107,B_108),'#skF_2')
      | ~ v2_compts_1(B_108,A_106)
      | k2_relset_1(u1_struct_0(A_106),k2_struct_0('#skF_2'),A_107) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_107,A_106,'#skF_2')
      | ~ v1_funct_2(A_107,u1_struct_0(A_106),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ r1_tarski(A_107,k2_zfmisc_1(u1_struct_0(A_106),k2_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_337])).

tff(c_433,plain,(
    ! [A_107,B_108] :
      ( v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_107,B_108),'#skF_2')
      | ~ v2_compts_1(B_108,'#skF_1')
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_107) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_107,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_107,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_107,k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_430])).

tff(c_946,plain,(
    ! [A_200,B_201] :
      ( v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_200,B_201),'#skF_2')
      | ~ v2_compts_1(B_201,'#skF_1')
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),A_200) != k2_struct_0('#skF_2')
      | ~ v5_pre_topc(A_200,'#skF_1','#skF_2')
      | ~ v1_funct_2(A_200,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_200)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ r1_tarski(A_200,k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_50,c_67,c_67,c_67,c_433])).

tff(c_168,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( m1_subset_1(k7_relset_1(A_58,B_59,C_60,D_61),k1_zfmisc_1(B_59))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_173,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( r1_tarski(k7_relset_1(A_62,B_63,C_64,D_65),B_63)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_183,plain,(
    ! [D_65] : r1_tarski(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_65),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_128,c_173])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_187,plain,(
    ! [B_71,A_72] :
      ( v4_pre_topc(B_71,A_72)
      | ~ v2_compts_1(B_71,A_72)
      | ~ v8_pre_topc(A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_200,plain,(
    ! [B_71] :
      ( v4_pre_topc(B_71,'#skF_2')
      | ~ v2_compts_1(B_71,'#skF_2')
      | ~ v8_pre_topc('#skF_2')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_187])).

tff(c_234,plain,(
    ! [B_76] :
      ( v4_pre_topc(B_76,'#skF_2')
      | ~ v2_compts_1(B_76,'#skF_2')
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_200])).

tff(c_257,plain,(
    ! [A_77] :
      ( v4_pre_topc(A_77,'#skF_2')
      | ~ v2_compts_1(A_77,'#skF_2')
      | ~ r1_tarski(A_77,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_4,c_234])).

tff(c_318,plain,(
    ! [D_85] :
      ( v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_85),'#skF_2')
      | ~ v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_85),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_183,c_257])).

tff(c_24,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_148,plain,(
    ~ v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_67,c_24])).

tff(c_322,plain,(
    ~ v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_318,c_148])).

tff(c_949,plain,
    ( ~ v2_compts_1('#skF_4','#skF_1')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ r1_tarski('#skF_3',k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_946,c_322])).

tff(c_953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_74,c_42,c_84,c_30,c_79,c_403,c_949])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:45:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.75  
% 3.72/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.75  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k7_relset_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.72/1.75  
% 3.72/1.75  %Foreground sorts:
% 3.72/1.75  
% 3.72/1.75  
% 3.72/1.75  %Background operators:
% 3.72/1.75  
% 3.72/1.75  
% 3.72/1.75  %Foreground operators:
% 3.72/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.72/1.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.72/1.75  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.72/1.75  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.72/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.72/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.72/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.75  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.72/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.72/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.72/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.72/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.72/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.72/1.75  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.72/1.75  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.72/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.72/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.72/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.75  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.72/1.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.72/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.72/1.75  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 3.72/1.75  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.72/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.72/1.75  
% 4.08/1.77  tff(f_143, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_compts_1(A) & v8_pre_topc(B)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v5_pre_topc(C, A, B)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(D, A) => v4_pre_topc(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_compts_1)).
% 4.08/1.77  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.08/1.77  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.08/1.77  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.08/1.77  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (v1_compts_1(A) <=> v2_compts_1(k2_struct_0(A), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_compts_1)).
% 4.08/1.77  tff(f_41, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 4.08/1.77  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 4.08/1.77  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(C))))) => (((v5_pre_topc(D, A, C) & (k2_relset_1(u1_struct_0(A), u1_struct_0(C), D) = k2_struct_0(C))) & v2_compts_1(B, A)) => v2_compts_1(k7_relset_1(u1_struct_0(A), u1_struct_0(C), D, B), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_compts_1)).
% 4.08/1.77  tff(f_33, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.08/1.77  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 4.08/1.77  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_12, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.08/1.77  tff(c_54, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.08/1.77  tff(c_59, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_pre_topc(A_49))), inference(resolution, [status(thm)], [c_12, c_54])).
% 4.08/1.77  tff(c_66, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_59])).
% 4.08/1.77  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_67, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_59])).
% 4.08/1.77  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_128, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_67, c_38])).
% 4.08/1.77  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.08/1.77  tff(c_132, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_128, c_2])).
% 4.08/1.77  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_28])).
% 4.08/1.77  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_69, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_40])).
% 4.08/1.77  tff(c_84, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_69])).
% 4.08/1.77  tff(c_30, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_32, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_79, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_66, c_32])).
% 4.08/1.77  tff(c_36, plain, (v1_compts_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_16, plain, (![A_10]: (v2_compts_1(k2_struct_0(A_10), A_10) | ~v1_compts_1(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.08/1.77  tff(c_95, plain, (![A_55]: (m1_subset_1(k2_struct_0(A_55), k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.08/1.77  tff(c_111, plain, (![A_57]: (r1_tarski(k2_struct_0(A_57), u1_struct_0(A_57)) | ~l1_struct_0(A_57))), inference(resolution, [status(thm)], [c_95, c_2])).
% 4.08/1.77  tff(c_114, plain, (r1_tarski(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_67, c_111])).
% 4.08/1.77  tff(c_118, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_114])).
% 4.08/1.77  tff(c_121, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_118])).
% 4.08/1.77  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_121])).
% 4.08/1.77  tff(c_127, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_114])).
% 4.08/1.77  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_26, plain, (v4_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_10, plain, (![A_8]: (m1_subset_1(k2_struct_0(A_8), k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.08/1.77  tff(c_85, plain, (![A_52, B_53]: (r1_tarski(A_52, B_53) | ~m1_subset_1(A_52, k1_zfmisc_1(B_53)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.08/1.77  tff(c_92, plain, (r1_tarski('#skF_4', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_74, c_85])).
% 4.08/1.77  tff(c_212, plain, (![C_73, A_74, B_75]: (v2_compts_1(C_73, A_74) | ~v4_pre_topc(C_73, A_74) | ~r1_tarski(C_73, B_75) | ~v2_compts_1(B_75, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.08/1.77  tff(c_373, plain, (![A_101]: (v2_compts_1('#skF_4', A_101) | ~v4_pre_topc('#skF_4', A_101) | ~v2_compts_1(k2_struct_0('#skF_1'), A_101) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(resolution, [status(thm)], [c_92, c_212])).
% 4.08/1.77  tff(c_377, plain, (v2_compts_1('#skF_4', '#skF_1') | ~v4_pre_topc('#skF_4', '#skF_1') | ~v2_compts_1(k2_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_373])).
% 4.08/1.77  tff(c_389, plain, (v2_compts_1('#skF_4', '#skF_1') | ~v2_compts_1(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_52, c_50, c_74, c_67, c_26, c_377])).
% 4.08/1.77  tff(c_395, plain, (~v2_compts_1(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_389])).
% 4.08/1.77  tff(c_398, plain, (~v1_compts_1('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_395])).
% 4.08/1.77  tff(c_402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_36, c_398])).
% 4.08/1.77  tff(c_403, plain, (v2_compts_1('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_389])).
% 4.08/1.77  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.08/1.77  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_292, plain, (![A_81, C_82, D_83, B_84]: (v2_compts_1(k7_relset_1(u1_struct_0(A_81), u1_struct_0(C_82), D_83, B_84), C_82) | ~v2_compts_1(B_84, A_81) | k2_relset_1(u1_struct_0(A_81), u1_struct_0(C_82), D_83)!=k2_struct_0(C_82) | ~v5_pre_topc(D_83, A_81, C_82) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81), u1_struct_0(C_82)))) | ~v1_funct_2(D_83, u1_struct_0(A_81), u1_struct_0(C_82)) | ~v1_funct_1(D_83) | ~l1_pre_topc(C_82) | v2_struct_0(C_82) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.08/1.77  tff(c_303, plain, (![A_81, D_83, B_84]: (v2_compts_1(k7_relset_1(u1_struct_0(A_81), u1_struct_0('#skF_2'), D_83, B_84), '#skF_2') | ~v2_compts_1(B_84, A_81) | k2_relset_1(u1_struct_0(A_81), u1_struct_0('#skF_2'), D_83)!=k2_struct_0('#skF_2') | ~v5_pre_topc(D_83, A_81, '#skF_2') | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_83, u1_struct_0(A_81), u1_struct_0('#skF_2')) | ~v1_funct_1(D_83) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(superposition, [status(thm), theory('equality')], [c_66, c_292])).
% 4.08/1.77  tff(c_315, plain, (![A_81, D_83, B_84]: (v2_compts_1(k7_relset_1(u1_struct_0(A_81), k2_struct_0('#skF_2'), D_83, B_84), '#skF_2') | ~v2_compts_1(B_84, A_81) | k2_relset_1(u1_struct_0(A_81), k2_struct_0('#skF_2'), D_83)!=k2_struct_0('#skF_2') | ~v5_pre_topc(D_83, A_81, '#skF_2') | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_81), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_83, u1_struct_0(A_81), k2_struct_0('#skF_2')) | ~v1_funct_1(D_83) | v2_struct_0('#skF_2') | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_66, c_66, c_66, c_303])).
% 4.08/1.77  tff(c_337, plain, (![A_92, D_93, B_94]: (v2_compts_1(k7_relset_1(u1_struct_0(A_92), k2_struct_0('#skF_2'), D_93, B_94), '#skF_2') | ~v2_compts_1(B_94, A_92) | k2_relset_1(u1_struct_0(A_92), k2_struct_0('#skF_2'), D_93)!=k2_struct_0('#skF_2') | ~v5_pre_topc(D_93, A_92, '#skF_2') | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_92), k2_struct_0('#skF_2')))) | ~v1_funct_2(D_93, u1_struct_0(A_92), k2_struct_0('#skF_2')) | ~v1_funct_1(D_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(negUnitSimplification, [status(thm)], [c_48, c_315])).
% 4.08/1.77  tff(c_430, plain, (![A_106, A_107, B_108]: (v2_compts_1(k7_relset_1(u1_struct_0(A_106), k2_struct_0('#skF_2'), A_107, B_108), '#skF_2') | ~v2_compts_1(B_108, A_106) | k2_relset_1(u1_struct_0(A_106), k2_struct_0('#skF_2'), A_107)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_107, A_106, '#skF_2') | ~v1_funct_2(A_107, u1_struct_0(A_106), k2_struct_0('#skF_2')) | ~v1_funct_1(A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~r1_tarski(A_107, k2_zfmisc_1(u1_struct_0(A_106), k2_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_4, c_337])).
% 4.08/1.77  tff(c_433, plain, (![A_107, B_108]: (v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_107, B_108), '#skF_2') | ~v2_compts_1(B_108, '#skF_1') | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_107)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_107, '#skF_1', '#skF_2') | ~v1_funct_2(A_107, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_107, k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_67, c_430])).
% 4.08/1.77  tff(c_946, plain, (![A_200, B_201]: (v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_200, B_201), '#skF_2') | ~v2_compts_1(B_201, '#skF_1') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), A_200)!=k2_struct_0('#skF_2') | ~v5_pre_topc(A_200, '#skF_1', '#skF_2') | ~v1_funct_2(A_200, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_200) | ~m1_subset_1(B_201, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski(A_200, k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_50, c_67, c_67, c_67, c_433])).
% 4.08/1.77  tff(c_168, plain, (![A_58, B_59, C_60, D_61]: (m1_subset_1(k7_relset_1(A_58, B_59, C_60, D_61), k1_zfmisc_1(B_59)) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.08/1.77  tff(c_173, plain, (![A_62, B_63, C_64, D_65]: (r1_tarski(k7_relset_1(A_62, B_63, C_64, D_65), B_63) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(resolution, [status(thm)], [c_168, c_2])).
% 4.08/1.77  tff(c_183, plain, (![D_65]: (r1_tarski(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_65), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_128, c_173])).
% 4.08/1.77  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_34, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_187, plain, (![B_71, A_72]: (v4_pre_topc(B_71, A_72) | ~v2_compts_1(B_71, A_72) | ~v8_pre_topc(A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.08/1.77  tff(c_200, plain, (![B_71]: (v4_pre_topc(B_71, '#skF_2') | ~v2_compts_1(B_71, '#skF_2') | ~v8_pre_topc('#skF_2') | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_187])).
% 4.08/1.77  tff(c_234, plain, (![B_76]: (v4_pre_topc(B_76, '#skF_2') | ~v2_compts_1(B_76, '#skF_2') | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_200])).
% 4.08/1.77  tff(c_257, plain, (![A_77]: (v4_pre_topc(A_77, '#skF_2') | ~v2_compts_1(A_77, '#skF_2') | ~r1_tarski(A_77, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_4, c_234])).
% 4.08/1.77  tff(c_318, plain, (![D_85]: (v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_85), '#skF_2') | ~v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_85), '#skF_2'))), inference(resolution, [status(thm)], [c_183, c_257])).
% 4.08/1.77  tff(c_24, plain, (~v4_pre_topc(k7_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.08/1.77  tff(c_148, plain, (~v4_pre_topc(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_67, c_24])).
% 4.08/1.77  tff(c_322, plain, (~v2_compts_1(k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_318, c_148])).
% 4.08/1.77  tff(c_949, plain, (~v2_compts_1('#skF_4', '#skF_1') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~r1_tarski('#skF_3', k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_946, c_322])).
% 4.08/1.77  tff(c_953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_74, c_42, c_84, c_30, c_79, c_403, c_949])).
% 4.08/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.77  
% 4.08/1.77  Inference rules
% 4.08/1.77  ----------------------
% 4.08/1.77  #Ref     : 0
% 4.08/1.77  #Sup     : 175
% 4.08/1.77  #Fact    : 0
% 4.08/1.77  #Define  : 0
% 4.08/1.77  #Split   : 9
% 4.08/1.77  #Chain   : 0
% 4.08/1.77  #Close   : 0
% 4.08/1.77  
% 4.08/1.77  Ordering : KBO
% 4.08/1.77  
% 4.08/1.77  Simplification rules
% 4.08/1.77  ----------------------
% 4.08/1.77  #Subsume      : 49
% 4.08/1.77  #Demod        : 459
% 4.08/1.77  #Tautology    : 31
% 4.08/1.77  #SimpNegUnit  : 10
% 4.08/1.77  #BackRed      : 2
% 4.08/1.77  
% 4.08/1.77  #Partial instantiations: 0
% 4.08/1.77  #Strategies tried      : 1
% 4.08/1.77  
% 4.08/1.77  Timing (in seconds)
% 4.08/1.77  ----------------------
% 4.08/1.77  Preprocessing        : 0.43
% 4.08/1.77  Parsing              : 0.24
% 4.08/1.77  CNF conversion       : 0.03
% 4.08/1.78  Main loop            : 0.51
% 4.08/1.78  Inferencing          : 0.18
% 4.08/1.78  Reduction            : 0.18
% 4.08/1.78  Demodulation         : 0.13
% 4.08/1.78  BG Simplification    : 0.02
% 4.08/1.78  Subsumption          : 0.09
% 4.08/1.78  Abstraction          : 0.03
% 4.08/1.78  MUC search           : 0.00
% 4.08/1.78  Cooper               : 0.00
% 4.08/1.78  Total                : 0.98
% 4.08/1.78  Index Insertion      : 0.00
% 4.08/1.78  Index Deletion       : 0.00
% 4.08/1.78  Index Matching       : 0.00
% 4.08/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
