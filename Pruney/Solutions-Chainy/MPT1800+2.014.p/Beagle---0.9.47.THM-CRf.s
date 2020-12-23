%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:59 EST 2020

% Result     : Theorem 5.46s
% Output     : CNFRefutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 503 expanded)
%              Number of leaves         :   29 ( 189 expanded)
%              Depth                    :   21
%              Number of atoms          :  376 (2052 expanded)
%              Number of equality atoms :   61 ( 323 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( ( v1_tsep_1(B,A)
                & m1_pre_topc(B,A) )
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k8_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tsep_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
            & ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_40,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_53,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40])).

tff(c_63,plain,(
    ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( v1_pre_topc(k8_tmap_1(A_15,B_16))
      | ~ m1_pre_topc(B_16,A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( l1_pre_topc(k8_tmap_1(A_15,B_16))
      | ~ m1_pre_topc(B_16,A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_82,plain,(
    ! [B_36,A_37] :
      ( u1_struct_0(B_36) = '#skF_1'(A_37,B_36)
      | v1_tsep_1(B_36,A_37)
      | ~ m1_pre_topc(B_36,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_63])).

tff(c_88,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_85])).

tff(c_28,plain,(
    ! [B_29,A_27] :
      ( m1_subset_1(u1_struct_0(B_29),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_93,plain,(
    ! [A_27] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc('#skF_3',A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_28])).

tff(c_50,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_65,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_50])).

tff(c_211,plain,(
    ! [B_58,A_59] :
      ( v3_pre_topc(B_58,A_59)
      | k6_tmap_1(A_59,B_58) != g1_pre_topc(u1_struct_0(A_59),u1_pre_topc(A_59))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_217,plain,(
    ! [B_58] :
      ( v3_pre_topc(B_58,'#skF_2')
      | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2',B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_211])).

tff(c_223,plain,(
    ! [B_58] :
      ( v3_pre_topc(B_58,'#skF_2')
      | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2',B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_217])).

tff(c_225,plain,(
    ! [B_60] :
      ( v3_pre_topc(B_60,'#skF_2')
      | k8_tmap_1('#skF_2','#skF_3') != k6_tmap_1('#skF_2',B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_223])).

tff(c_233,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_225])).

tff(c_243,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_233])).

tff(c_247,plain,(
    k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_114,plain,(
    ! [A_47,B_48] :
      ( u1_struct_0(k8_tmap_1(A_47,B_48)) = u1_struct_0(A_47)
      | ~ m1_pre_topc(B_48,A_47)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_870,plain,(
    ! [A_116,B_117] :
      ( g1_pre_topc(u1_struct_0(A_116),u1_pre_topc(k8_tmap_1(A_116,B_117))) = k8_tmap_1(A_116,B_117)
      | ~ v1_pre_topc(k8_tmap_1(A_116,B_117))
      | ~ l1_pre_topc(k8_tmap_1(A_116,B_117))
      | ~ m1_pre_topc(B_117,A_116)
      | v2_struct_0(B_117)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_2])).

tff(c_10,plain,(
    ! [A_2,B_8] :
      ( m1_subset_1('#skF_1'(A_2,B_8),k1_zfmisc_1(u1_struct_0(A_2)))
      | v1_tsep_1(B_8,A_2)
      | ~ m1_pre_topc(B_8,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_425,plain,(
    ! [A_77,B_78] :
      ( k5_tmap_1(A_77,u1_struct_0(B_78)) = u1_pre_topc(k8_tmap_1(A_77,B_78))
      | ~ m1_subset_1(u1_struct_0(B_78),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc(B_78,A_77)
      | v2_struct_0(B_78)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_434,plain,(
    ! [A_77] :
      ( k5_tmap_1(A_77,u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1(A_77,'#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc('#skF_3',A_77)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_425])).

tff(c_441,plain,(
    ! [A_77] :
      ( k5_tmap_1(A_77,'#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1(A_77,'#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc('#skF_3',A_77)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_434])).

tff(c_476,plain,(
    ! [A_81] :
      ( k5_tmap_1(A_81,'#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1(A_81,'#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_pre_topc('#skF_3',A_81)
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_441])).

tff(c_483,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_476])).

tff(c_492,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_483])).

tff(c_493,plain,(
    k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_38,c_492])).

tff(c_172,plain,(
    ! [A_54,B_55] :
      ( g1_pre_topc(u1_struct_0(A_54),k5_tmap_1(A_54,B_55)) = k6_tmap_1(A_54,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_188,plain,(
    ! [A_56,B_57] :
      ( g1_pre_topc(u1_struct_0(A_56),k5_tmap_1(A_56,u1_struct_0(B_57))) = k6_tmap_1(A_56,u1_struct_0(B_57))
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56)
      | ~ m1_pre_topc(B_57,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_28,c_172])).

tff(c_206,plain,(
    ! [A_56] :
      ( g1_pre_topc(u1_struct_0(A_56),k5_tmap_1(A_56,'#skF_1'('#skF_2','#skF_3'))) = k6_tmap_1(A_56,u1_struct_0('#skF_3'))
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56)
      | ~ m1_pre_topc('#skF_3',A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_188])).

tff(c_585,plain,(
    ! [A_90] :
      ( g1_pre_topc(u1_struct_0(A_90),k5_tmap_1(A_90,'#skF_1'('#skF_2','#skF_3'))) = k6_tmap_1(A_90,'#skF_1'('#skF_2','#skF_3'))
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90)
      | ~ m1_pre_topc('#skF_3',A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_206])).

tff(c_597,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_585])).

tff(c_607,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_597])).

tff(c_608,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) = k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_607])).

tff(c_876,plain,
    ( k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_608])).

tff(c_891,plain,
    ( k6_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_876])).

tff(c_892,plain,
    ( ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_32,c_247,c_891])).

tff(c_898,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_892])).

tff(c_901,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_898])).

tff(c_904,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_901])).

tff(c_906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_904])).

tff(c_907,plain,(
    ~ v1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_892])).

tff(c_911,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_907])).

tff(c_914,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_911])).

tff(c_916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_914])).

tff(c_917,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_6,plain,(
    ! [A_2,B_8] :
      ( ~ v3_pre_topc('#skF_1'(A_2,B_8),A_2)
      | v1_tsep_1(B_8,A_2)
      | ~ m1_pre_topc(B_8,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_937,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_917,c_6])).

tff(c_940,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_937])).

tff(c_942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_940])).

tff(c_944,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_1059,plain,(
    ! [A_154,B_155] :
      ( k5_tmap_1(A_154,u1_struct_0(B_155)) = u1_pre_topc(k8_tmap_1(A_154,B_155))
      | ~ m1_subset_1(u1_struct_0(B_155),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_pre_topc(B_155,A_154)
      | v2_struct_0(B_155)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1070,plain,(
    ! [A_156,B_157] :
      ( k5_tmap_1(A_156,u1_struct_0(B_157)) = u1_pre_topc(k8_tmap_1(A_156,B_157))
      | v2_struct_0(B_157)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156)
      | ~ m1_pre_topc(B_157,A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_28,c_1059])).

tff(c_996,plain,(
    ! [A_140,B_141] :
      ( g1_pre_topc(u1_struct_0(A_140),k5_tmap_1(A_140,B_141)) = k6_tmap_1(A_140,B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1004,plain,(
    ! [A_27,B_29] :
      ( g1_pre_topc(u1_struct_0(A_27),k5_tmap_1(A_27,u1_struct_0(B_29))) = k6_tmap_1(A_27,u1_struct_0(B_29))
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27)
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_28,c_996])).

tff(c_1213,plain,(
    ! [A_184,B_185] :
      ( g1_pre_topc(u1_struct_0(A_184),u1_pre_topc(k8_tmap_1(A_184,B_185))) = k6_tmap_1(A_184,u1_struct_0(B_185))
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184)
      | v2_struct_0(B_185)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1070,c_1004])).

tff(c_960,plain,(
    ! [A_134,B_135] :
      ( u1_struct_0(k8_tmap_1(A_134,B_135)) = u1_struct_0(A_134)
      | ~ m1_pre_topc(B_135,A_134)
      | v2_struct_0(B_135)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_975,plain,(
    ! [A_134,B_135] :
      ( g1_pre_topc(u1_struct_0(A_134),u1_pre_topc(k8_tmap_1(A_134,B_135))) = k8_tmap_1(A_134,B_135)
      | ~ v1_pre_topc(k8_tmap_1(A_134,B_135))
      | ~ l1_pre_topc(k8_tmap_1(A_134,B_135))
      | ~ m1_pre_topc(B_135,A_134)
      | v2_struct_0(B_135)
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_2])).

tff(c_2223,plain,(
    ! [A_286,B_287] :
      ( k6_tmap_1(A_286,u1_struct_0(B_287)) = k8_tmap_1(A_286,B_287)
      | ~ v1_pre_topc(k8_tmap_1(A_286,B_287))
      | ~ l1_pre_topc(k8_tmap_1(A_286,B_287))
      | ~ m1_pre_topc(B_287,A_286)
      | v2_struct_0(B_287)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286)
      | ~ m1_pre_topc(B_287,A_286)
      | ~ l1_pre_topc(A_286)
      | v2_struct_0(B_287)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286)
      | ~ m1_pre_topc(B_287,A_286)
      | ~ l1_pre_topc(A_286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1213,c_975])).

tff(c_2235,plain,(
    ! [A_291,B_292] :
      ( k6_tmap_1(A_291,u1_struct_0(B_292)) = k8_tmap_1(A_291,B_292)
      | ~ l1_pre_topc(k8_tmap_1(A_291,B_292))
      | v2_struct_0(B_292)
      | ~ m1_pre_topc(B_292,A_291)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(resolution,[status(thm)],[c_18,c_2223])).

tff(c_2240,plain,(
    ! [A_293,B_294] :
      ( k6_tmap_1(A_293,u1_struct_0(B_294)) = k8_tmap_1(A_293,B_294)
      | v2_struct_0(B_294)
      | ~ m1_pre_topc(B_294,A_293)
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(resolution,[status(thm)],[c_14,c_2235])).

tff(c_981,plain,(
    ! [B_136,A_137] :
      ( v3_pre_topc(u1_struct_0(B_136),A_137)
      | ~ m1_subset_1(u1_struct_0(B_136),k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ v1_tsep_1(B_136,A_137)
      | ~ m1_pre_topc(B_136,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_991,plain,(
    ! [B_29,A_27] :
      ( v3_pre_topc(u1_struct_0(B_29),A_27)
      | ~ v1_tsep_1(B_29,A_27)
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_28,c_981])).

tff(c_1025,plain,(
    ! [A_146,B_147] :
      ( k6_tmap_1(A_146,B_147) = g1_pre_topc(u1_struct_0(A_146),u1_pre_topc(A_146))
      | ~ v3_pre_topc(B_147,A_146)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1050,plain,(
    ! [A_152,B_153] :
      ( k6_tmap_1(A_152,u1_struct_0(B_153)) = g1_pre_topc(u1_struct_0(A_152),u1_pre_topc(A_152))
      | ~ v3_pre_topc(u1_struct_0(B_153),A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152)
      | ~ m1_pre_topc(B_153,A_152)
      | ~ l1_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_28,c_1025])).

tff(c_1085,plain,(
    ! [A_158,B_159] :
      ( k6_tmap_1(A_158,u1_struct_0(B_159)) = g1_pre_topc(u1_struct_0(A_158),u1_pre_topc(A_158))
      | ~ v2_pre_topc(A_158)
      | v2_struct_0(A_158)
      | ~ v1_tsep_1(B_159,A_158)
      | ~ m1_pre_topc(B_159,A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_991,c_1050])).

tff(c_943,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_1098,plain,(
    ! [B_159] :
      ( k6_tmap_1('#skF_2',u1_struct_0(B_159)) != k8_tmap_1('#skF_2','#skF_3')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_159,'#skF_2')
      | ~ m1_pre_topc(B_159,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1085,c_943])).

tff(c_1120,plain,(
    ! [B_159] :
      ( k6_tmap_1('#skF_2',u1_struct_0(B_159)) != k8_tmap_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_159,'#skF_2')
      | ~ m1_pre_topc(B_159,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_1098])).

tff(c_1121,plain,(
    ! [B_159] :
      ( k6_tmap_1('#skF_2',u1_struct_0(B_159)) != k8_tmap_1('#skF_2','#skF_3')
      | ~ v1_tsep_1(B_159,'#skF_2')
      | ~ m1_pre_topc(B_159,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1120])).

tff(c_2293,plain,(
    ! [B_294] :
      ( k8_tmap_1('#skF_2',B_294) != k8_tmap_1('#skF_2','#skF_3')
      | ~ v1_tsep_1(B_294,'#skF_2')
      | ~ m1_pre_topc(B_294,'#skF_2')
      | v2_struct_0(B_294)
      | ~ m1_pre_topc(B_294,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2240,c_1121])).

tff(c_2340,plain,(
    ! [B_294] :
      ( k8_tmap_1('#skF_2',B_294) != k8_tmap_1('#skF_2','#skF_3')
      | ~ v1_tsep_1(B_294,'#skF_2')
      | v2_struct_0(B_294)
      | ~ m1_pre_topc(B_294,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2293])).

tff(c_2343,plain,(
    ! [B_295] :
      ( k8_tmap_1('#skF_2',B_295) != k8_tmap_1('#skF_2','#skF_3')
      | ~ v1_tsep_1(B_295,'#skF_2')
      | v2_struct_0(B_295)
      | ~ m1_pre_topc(B_295,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2340])).

tff(c_2350,plain,
    ( v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_944,c_2343])).

tff(c_2356,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2350])).

tff(c_2358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:57:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.46/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.00  
% 5.46/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.00  %$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.46/2.00  
% 5.46/2.00  %Foreground sorts:
% 5.46/2.00  
% 5.46/2.00  
% 5.46/2.00  %Background operators:
% 5.46/2.00  
% 5.46/2.00  
% 5.46/2.00  %Foreground operators:
% 5.46/2.00  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.46/2.00  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.46/2.00  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.46/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.46/2.00  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.46/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.46/2.00  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 5.46/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.46/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.46/2.00  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.46/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.46/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.46/2.00  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.46/2.00  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 5.46/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.46/2.00  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.46/2.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.46/2.00  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 5.46/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.46/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.46/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.46/2.00  
% 5.46/2.02  tff(f_135, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k8_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_tmap_1)).
% 5.46/2.02  tff(f_72, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 5.46/2.02  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tsep_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 5.46/2.02  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.46/2.02  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 5.46/2.02  tff(f_108, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 5.46/2.02  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 5.46/2.02  tff(f_57, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 5.46/2.02  tff(c_32, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.46/2.02  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.46/2.02  tff(c_40, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.46/2.02  tff(c_53, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40])).
% 5.46/2.02  tff(c_63, plain, (~v1_tsep_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_53])).
% 5.46/2.02  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.46/2.02  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.46/2.02  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.46/2.02  tff(c_18, plain, (![A_15, B_16]: (v1_pre_topc(k8_tmap_1(A_15, B_16)) | ~m1_pre_topc(B_16, A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.46/2.02  tff(c_14, plain, (![A_15, B_16]: (l1_pre_topc(k8_tmap_1(A_15, B_16)) | ~m1_pre_topc(B_16, A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.46/2.02  tff(c_82, plain, (![B_36, A_37]: (u1_struct_0(B_36)='#skF_1'(A_37, B_36) | v1_tsep_1(B_36, A_37) | ~m1_pre_topc(B_36, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.46/2.02  tff(c_85, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_82, c_63])).
% 5.46/2.02  tff(c_88, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_85])).
% 5.46/2.02  tff(c_28, plain, (![B_29, A_27]: (m1_subset_1(u1_struct_0(B_29), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.46/2.02  tff(c_93, plain, (![A_27]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc('#skF_3', A_27) | ~l1_pre_topc(A_27))), inference(superposition, [status(thm), theory('equality')], [c_88, c_28])).
% 5.46/2.02  tff(c_50, plain, (v1_tsep_1('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.46/2.02  tff(c_65, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_63, c_50])).
% 5.46/2.02  tff(c_211, plain, (![B_58, A_59]: (v3_pre_topc(B_58, A_59) | k6_tmap_1(A_59, B_58)!=g1_pre_topc(u1_struct_0(A_59), u1_pre_topc(A_59)) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.46/2.02  tff(c_217, plain, (![B_58]: (v3_pre_topc(B_58, '#skF_2') | k8_tmap_1('#skF_2', '#skF_3')!=k6_tmap_1('#skF_2', B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_211])).
% 5.46/2.02  tff(c_223, plain, (![B_58]: (v3_pre_topc(B_58, '#skF_2') | k8_tmap_1('#skF_2', '#skF_3')!=k6_tmap_1('#skF_2', B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_217])).
% 5.46/2.02  tff(c_225, plain, (![B_60]: (v3_pre_topc(B_60, '#skF_2') | k8_tmap_1('#skF_2', '#skF_3')!=k6_tmap_1('#skF_2', B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_223])).
% 5.46/2.02  tff(c_233, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_93, c_225])).
% 5.46/2.02  tff(c_243, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_233])).
% 5.46/2.02  tff(c_247, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_243])).
% 5.46/2.02  tff(c_114, plain, (![A_47, B_48]: (u1_struct_0(k8_tmap_1(A_47, B_48))=u1_struct_0(A_47) | ~m1_pre_topc(B_48, A_47) | v2_struct_0(B_48) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.46/2.02  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.46/2.02  tff(c_870, plain, (![A_116, B_117]: (g1_pre_topc(u1_struct_0(A_116), u1_pre_topc(k8_tmap_1(A_116, B_117)))=k8_tmap_1(A_116, B_117) | ~v1_pre_topc(k8_tmap_1(A_116, B_117)) | ~l1_pre_topc(k8_tmap_1(A_116, B_117)) | ~m1_pre_topc(B_117, A_116) | v2_struct_0(B_117) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(superposition, [status(thm), theory('equality')], [c_114, c_2])).
% 5.46/2.02  tff(c_10, plain, (![A_2, B_8]: (m1_subset_1('#skF_1'(A_2, B_8), k1_zfmisc_1(u1_struct_0(A_2))) | v1_tsep_1(B_8, A_2) | ~m1_pre_topc(B_8, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.46/2.02  tff(c_425, plain, (![A_77, B_78]: (k5_tmap_1(A_77, u1_struct_0(B_78))=u1_pre_topc(k8_tmap_1(A_77, B_78)) | ~m1_subset_1(u1_struct_0(B_78), k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_pre_topc(B_78, A_77) | v2_struct_0(B_78) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.46/2.02  tff(c_434, plain, (![A_77]: (k5_tmap_1(A_77, u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1(A_77, '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_pre_topc('#skF_3', A_77) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(superposition, [status(thm), theory('equality')], [c_88, c_425])).
% 5.46/2.02  tff(c_441, plain, (![A_77]: (k5_tmap_1(A_77, '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1(A_77, '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_pre_topc('#skF_3', A_77) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_434])).
% 5.46/2.02  tff(c_476, plain, (![A_81]: (k5_tmap_1(A_81, '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1(A_81, '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_pre_topc('#skF_3', A_81) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(negUnitSimplification, [status(thm)], [c_32, c_441])).
% 5.46/2.02  tff(c_483, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_476])).
% 5.46/2.02  tff(c_492, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_36, c_483])).
% 5.46/2.02  tff(c_493, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_63, c_38, c_492])).
% 5.46/2.02  tff(c_172, plain, (![A_54, B_55]: (g1_pre_topc(u1_struct_0(A_54), k5_tmap_1(A_54, B_55))=k6_tmap_1(A_54, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.46/2.02  tff(c_188, plain, (![A_56, B_57]: (g1_pre_topc(u1_struct_0(A_56), k5_tmap_1(A_56, u1_struct_0(B_57)))=k6_tmap_1(A_56, u1_struct_0(B_57)) | ~v2_pre_topc(A_56) | v2_struct_0(A_56) | ~m1_pre_topc(B_57, A_56) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_28, c_172])).
% 5.46/2.02  tff(c_206, plain, (![A_56]: (g1_pre_topc(u1_struct_0(A_56), k5_tmap_1(A_56, '#skF_1'('#skF_2', '#skF_3')))=k6_tmap_1(A_56, u1_struct_0('#skF_3')) | ~v2_pre_topc(A_56) | v2_struct_0(A_56) | ~m1_pre_topc('#skF_3', A_56) | ~l1_pre_topc(A_56))), inference(superposition, [status(thm), theory('equality')], [c_88, c_188])).
% 5.46/2.02  tff(c_585, plain, (![A_90]: (g1_pre_topc(u1_struct_0(A_90), k5_tmap_1(A_90, '#skF_1'('#skF_2', '#skF_3')))=k6_tmap_1(A_90, '#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc(A_90) | v2_struct_0(A_90) | ~m1_pre_topc('#skF_3', A_90) | ~l1_pre_topc(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_206])).
% 5.46/2.02  tff(c_597, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')))=k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3')) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_493, c_585])).
% 5.46/2.02  tff(c_607, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')))=k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_36, c_597])).
% 5.46/2.02  tff(c_608, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')))=k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_607])).
% 5.46/2.02  tff(c_876, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=k8_tmap_1('#skF_2', '#skF_3') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_870, c_608])).
% 5.46/2.02  tff(c_891, plain, (k6_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=k8_tmap_1('#skF_2', '#skF_3') | ~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_876])).
% 5.46/2.02  tff(c_892, plain, (~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_32, c_247, c_891])).
% 5.46/2.02  tff(c_898, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_892])).
% 5.46/2.02  tff(c_901, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_14, c_898])).
% 5.46/2.02  tff(c_904, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_901])).
% 5.46/2.02  tff(c_906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_904])).
% 5.46/2.02  tff(c_907, plain, (~v1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_892])).
% 5.46/2.02  tff(c_911, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_907])).
% 5.46/2.02  tff(c_914, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_911])).
% 5.46/2.02  tff(c_916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_914])).
% 5.46/2.02  tff(c_917, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_243])).
% 5.46/2.02  tff(c_6, plain, (![A_2, B_8]: (~v3_pre_topc('#skF_1'(A_2, B_8), A_2) | v1_tsep_1(B_8, A_2) | ~m1_pre_topc(B_8, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.46/2.02  tff(c_937, plain, (v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_917, c_6])).
% 5.46/2.02  tff(c_940, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_937])).
% 5.46/2.02  tff(c_942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_940])).
% 5.46/2.02  tff(c_944, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_53])).
% 5.46/2.02  tff(c_1059, plain, (![A_154, B_155]: (k5_tmap_1(A_154, u1_struct_0(B_155))=u1_pre_topc(k8_tmap_1(A_154, B_155)) | ~m1_subset_1(u1_struct_0(B_155), k1_zfmisc_1(u1_struct_0(A_154))) | ~m1_pre_topc(B_155, A_154) | v2_struct_0(B_155) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.46/2.02  tff(c_1070, plain, (![A_156, B_157]: (k5_tmap_1(A_156, u1_struct_0(B_157))=u1_pre_topc(k8_tmap_1(A_156, B_157)) | v2_struct_0(B_157) | ~v2_pre_topc(A_156) | v2_struct_0(A_156) | ~m1_pre_topc(B_157, A_156) | ~l1_pre_topc(A_156))), inference(resolution, [status(thm)], [c_28, c_1059])).
% 5.46/2.02  tff(c_996, plain, (![A_140, B_141]: (g1_pre_topc(u1_struct_0(A_140), k5_tmap_1(A_140, B_141))=k6_tmap_1(A_140, B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.46/2.02  tff(c_1004, plain, (![A_27, B_29]: (g1_pre_topc(u1_struct_0(A_27), k5_tmap_1(A_27, u1_struct_0(B_29)))=k6_tmap_1(A_27, u1_struct_0(B_29)) | ~v2_pre_topc(A_27) | v2_struct_0(A_27) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_28, c_996])).
% 5.46/2.02  tff(c_1213, plain, (![A_184, B_185]: (g1_pre_topc(u1_struct_0(A_184), u1_pre_topc(k8_tmap_1(A_184, B_185)))=k6_tmap_1(A_184, u1_struct_0(B_185)) | ~v2_pre_topc(A_184) | v2_struct_0(A_184) | ~m1_pre_topc(B_185, A_184) | ~l1_pre_topc(A_184) | v2_struct_0(B_185) | ~v2_pre_topc(A_184) | v2_struct_0(A_184) | ~m1_pre_topc(B_185, A_184) | ~l1_pre_topc(A_184))), inference(superposition, [status(thm), theory('equality')], [c_1070, c_1004])).
% 5.46/2.02  tff(c_960, plain, (![A_134, B_135]: (u1_struct_0(k8_tmap_1(A_134, B_135))=u1_struct_0(A_134) | ~m1_pre_topc(B_135, A_134) | v2_struct_0(B_135) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.46/2.02  tff(c_975, plain, (![A_134, B_135]: (g1_pre_topc(u1_struct_0(A_134), u1_pre_topc(k8_tmap_1(A_134, B_135)))=k8_tmap_1(A_134, B_135) | ~v1_pre_topc(k8_tmap_1(A_134, B_135)) | ~l1_pre_topc(k8_tmap_1(A_134, B_135)) | ~m1_pre_topc(B_135, A_134) | v2_struct_0(B_135) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(superposition, [status(thm), theory('equality')], [c_960, c_2])).
% 5.46/2.02  tff(c_2223, plain, (![A_286, B_287]: (k6_tmap_1(A_286, u1_struct_0(B_287))=k8_tmap_1(A_286, B_287) | ~v1_pre_topc(k8_tmap_1(A_286, B_287)) | ~l1_pre_topc(k8_tmap_1(A_286, B_287)) | ~m1_pre_topc(B_287, A_286) | v2_struct_0(B_287) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286) | ~v2_pre_topc(A_286) | v2_struct_0(A_286) | ~m1_pre_topc(B_287, A_286) | ~l1_pre_topc(A_286) | v2_struct_0(B_287) | ~v2_pre_topc(A_286) | v2_struct_0(A_286) | ~m1_pre_topc(B_287, A_286) | ~l1_pre_topc(A_286))), inference(superposition, [status(thm), theory('equality')], [c_1213, c_975])).
% 5.46/2.02  tff(c_2235, plain, (![A_291, B_292]: (k6_tmap_1(A_291, u1_struct_0(B_292))=k8_tmap_1(A_291, B_292) | ~l1_pre_topc(k8_tmap_1(A_291, B_292)) | v2_struct_0(B_292) | ~m1_pre_topc(B_292, A_291) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(resolution, [status(thm)], [c_18, c_2223])).
% 5.46/2.02  tff(c_2240, plain, (![A_293, B_294]: (k6_tmap_1(A_293, u1_struct_0(B_294))=k8_tmap_1(A_293, B_294) | v2_struct_0(B_294) | ~m1_pre_topc(B_294, A_293) | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293) | v2_struct_0(A_293))), inference(resolution, [status(thm)], [c_14, c_2235])).
% 5.46/2.02  tff(c_981, plain, (![B_136, A_137]: (v3_pre_topc(u1_struct_0(B_136), A_137) | ~m1_subset_1(u1_struct_0(B_136), k1_zfmisc_1(u1_struct_0(A_137))) | ~v1_tsep_1(B_136, A_137) | ~m1_pre_topc(B_136, A_137) | ~l1_pre_topc(A_137))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.46/2.02  tff(c_991, plain, (![B_29, A_27]: (v3_pre_topc(u1_struct_0(B_29), A_27) | ~v1_tsep_1(B_29, A_27) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_28, c_981])).
% 5.46/2.02  tff(c_1025, plain, (![A_146, B_147]: (k6_tmap_1(A_146, B_147)=g1_pre_topc(u1_struct_0(A_146), u1_pre_topc(A_146)) | ~v3_pre_topc(B_147, A_146) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.46/2.02  tff(c_1050, plain, (![A_152, B_153]: (k6_tmap_1(A_152, u1_struct_0(B_153))=g1_pre_topc(u1_struct_0(A_152), u1_pre_topc(A_152)) | ~v3_pre_topc(u1_struct_0(B_153), A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152) | ~m1_pre_topc(B_153, A_152) | ~l1_pre_topc(A_152))), inference(resolution, [status(thm)], [c_28, c_1025])).
% 5.46/2.02  tff(c_1085, plain, (![A_158, B_159]: (k6_tmap_1(A_158, u1_struct_0(B_159))=g1_pre_topc(u1_struct_0(A_158), u1_pre_topc(A_158)) | ~v2_pre_topc(A_158) | v2_struct_0(A_158) | ~v1_tsep_1(B_159, A_158) | ~m1_pre_topc(B_159, A_158) | ~l1_pre_topc(A_158))), inference(resolution, [status(thm)], [c_991, c_1050])).
% 5.46/2.02  tff(c_943, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_53])).
% 5.46/2.02  tff(c_1098, plain, (![B_159]: (k6_tmap_1('#skF_2', u1_struct_0(B_159))!=k8_tmap_1('#skF_2', '#skF_3') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_159, '#skF_2') | ~m1_pre_topc(B_159, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1085, c_943])).
% 5.46/2.02  tff(c_1120, plain, (![B_159]: (k6_tmap_1('#skF_2', u1_struct_0(B_159))!=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_159, '#skF_2') | ~m1_pre_topc(B_159, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_1098])).
% 5.46/2.02  tff(c_1121, plain, (![B_159]: (k6_tmap_1('#skF_2', u1_struct_0(B_159))!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1(B_159, '#skF_2') | ~m1_pre_topc(B_159, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_1120])).
% 5.46/2.02  tff(c_2293, plain, (![B_294]: (k8_tmap_1('#skF_2', B_294)!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1(B_294, '#skF_2') | ~m1_pre_topc(B_294, '#skF_2') | v2_struct_0(B_294) | ~m1_pre_topc(B_294, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2240, c_1121])).
% 5.46/2.02  tff(c_2340, plain, (![B_294]: (k8_tmap_1('#skF_2', B_294)!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1(B_294, '#skF_2') | v2_struct_0(B_294) | ~m1_pre_topc(B_294, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2293])).
% 5.46/2.02  tff(c_2343, plain, (![B_295]: (k8_tmap_1('#skF_2', B_295)!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1(B_295, '#skF_2') | v2_struct_0(B_295) | ~m1_pre_topc(B_295, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_2340])).
% 5.46/2.02  tff(c_2350, plain, (v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_944, c_2343])).
% 5.46/2.02  tff(c_2356, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2350])).
% 5.46/2.02  tff(c_2358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_2356])).
% 5.46/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.02  
% 5.46/2.02  Inference rules
% 5.46/2.02  ----------------------
% 5.46/2.02  #Ref     : 1
% 5.46/2.02  #Sup     : 579
% 5.46/2.02  #Fact    : 0
% 5.46/2.02  #Define  : 0
% 5.46/2.02  #Split   : 6
% 5.46/2.02  #Chain   : 0
% 5.46/2.02  #Close   : 0
% 5.46/2.02  
% 5.46/2.02  Ordering : KBO
% 5.46/2.02  
% 5.46/2.02  Simplification rules
% 5.46/2.02  ----------------------
% 5.46/2.02  #Subsume      : 203
% 5.46/2.02  #Demod        : 246
% 5.46/2.02  #Tautology    : 118
% 5.46/2.02  #SimpNegUnit  : 90
% 5.46/2.02  #BackRed      : 0
% 5.46/2.02  
% 5.46/2.02  #Partial instantiations: 0
% 5.46/2.02  #Strategies tried      : 1
% 5.46/2.02  
% 5.46/2.02  Timing (in seconds)
% 5.46/2.02  ----------------------
% 5.46/2.03  Preprocessing        : 0.33
% 5.46/2.03  Parsing              : 0.17
% 5.46/2.03  CNF conversion       : 0.02
% 5.46/2.03  Main loop            : 0.92
% 5.46/2.03  Inferencing          : 0.36
% 5.46/2.03  Reduction            : 0.23
% 5.46/2.03  Demodulation         : 0.15
% 5.46/2.03  BG Simplification    : 0.05
% 5.46/2.03  Subsumption          : 0.23
% 5.46/2.03  Abstraction          : 0.05
% 5.46/2.03  MUC search           : 0.00
% 5.46/2.03  Cooper               : 0.00
% 5.46/2.03  Total                : 1.29
% 5.46/2.03  Index Insertion      : 0.00
% 5.46/2.03  Index Deletion       : 0.00
% 5.46/2.03  Index Matching       : 0.00
% 5.46/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
