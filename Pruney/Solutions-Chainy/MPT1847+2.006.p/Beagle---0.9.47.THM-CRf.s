%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:53 EST 2020

% Result     : Theorem 9.44s
% Output     : CNFRefutation 9.44s
% Verified   : 
% Statistics : Number of formulae       :  152 (2107 expanded)
%              Number of leaves         :   35 ( 743 expanded)
%              Depth                    :   18
%              Number of atoms          :  288 (5491 expanded)
%              Number of equality atoms :   45 ( 975 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( ( g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                    & v1_tex_2(B,A) )
                 => v1_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(c_48,plain,(
    ~ v1_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_81,plain,(
    ! [B_52,A_53] :
      ( l1_pre_topc(B_52)
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_81])).

tff(c_90,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_84])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ! [A_15] :
      ( u1_struct_0(A_15) = k2_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(resolution,[status(thm)],[c_22,c_62])).

tff(c_97,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_66])).

tff(c_570,plain,(
    ! [B_92,A_93] :
      ( u1_struct_0(B_92) = '#skF_1'(A_93,B_92)
      | v1_tex_2(B_92,A_93)
      | ~ m1_pre_topc(B_92,A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_573,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_570,c_48])).

tff(c_576,plain,(
    k2_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_97,c_573])).

tff(c_585,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_328,plain,(
    ! [A_77,B_78] :
      ( m1_pre_topc(k1_pre_topc(A_77,B_78),A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_7374,plain,(
    ! [A_330,A_331] :
      ( m1_pre_topc(k1_pre_topc(A_330,A_331),A_330)
      | ~ l1_pre_topc(A_330)
      | ~ r1_tarski(A_331,u1_struct_0(A_330)) ) ),
    inference(resolution,[status(thm)],[c_10,c_328])).

tff(c_7403,plain,(
    ! [A_332] :
      ( m1_pre_topc(k1_pre_topc(A_332,u1_struct_0(A_332)),A_332)
      | ~ l1_pre_topc(A_332) ) ),
    inference(resolution,[status(thm)],[c_6,c_7374])).

tff(c_24,plain,(
    ! [B_18,A_16] :
      ( l1_pre_topc(B_18)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_7436,plain,(
    ! [A_333] :
      ( l1_pre_topc(k1_pre_topc(A_333,u1_struct_0(A_333)))
      | ~ l1_pre_topc(A_333) ) ),
    inference(resolution,[status(thm)],[c_7403,c_24])).

tff(c_7445,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_7436])).

tff(c_7453,plain,(
    l1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_7445])).

tff(c_7422,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_7403])).

tff(c_7433,plain,(
    m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_7422])).

tff(c_672,plain,(
    ! [A_94,B_95] :
      ( m1_pre_topc(A_94,g1_pre_topc(u1_struct_0(B_95),u1_pre_topc(B_95)))
      | ~ m1_pre_topc(A_94,B_95)
      | ~ l1_pre_topc(B_95)
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_681,plain,(
    ! [A_94] :
      ( m1_pre_topc(A_94,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_94,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_672])).

tff(c_14240,plain,(
    ! [A_469] :
      ( m1_pre_topc(A_469,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_469,'#skF_4')
      | ~ l1_pre_topc(A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_681])).

tff(c_56,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_87,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_81])).

tff(c_93,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_87])).

tff(c_101,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_66])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_111,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_52])).

tff(c_120,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_111])).

tff(c_451,plain,(
    ! [B_85,A_86] :
      ( m1_pre_topc(B_85,A_86)
      | ~ m1_pre_topc(B_85,g1_pre_topc(u1_struct_0(A_86),u1_pre_topc(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_454,plain,(
    ! [B_85] :
      ( m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc(B_85,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_451])).

tff(c_462,plain,(
    ! [B_85] :
      ( m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc(B_85,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_120,c_454])).

tff(c_7611,plain,(
    ! [B_85] :
      ( m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc(B_85,g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_462])).

tff(c_14279,plain,(
    ! [A_470] :
      ( m1_pre_topc(A_470,'#skF_3')
      | ~ m1_pre_topc(A_470,'#skF_4')
      | ~ l1_pre_topc(A_470) ) ),
    inference(resolution,[status(thm)],[c_14240,c_7611])).

tff(c_67,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(resolution,[status(thm)],[c_22,c_62])).

tff(c_71,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_67])).

tff(c_179,plain,(
    ! [B_67,A_68] :
      ( m1_subset_1(u1_struct_0(B_67),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_203,plain,(
    ! [B_67] :
      ( m1_subset_1(u1_struct_0(B_67),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_67,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_179])).

tff(c_485,plain,(
    ! [B_88] :
      ( m1_subset_1(u1_struct_0(B_88),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_88,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_203])).

tff(c_500,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_485])).

tff(c_510,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_500])).

tff(c_44,plain,(
    ! [B_42,A_41] :
      ( v1_subset_1(B_42,A_41)
      | B_42 = A_41
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_537,plain,
    ( v1_subset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_510,c_44])).

tff(c_6756,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_576,c_537])).

tff(c_6757,plain,(
    k2_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6756])).

tff(c_102,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(A_54,k1_zfmisc_1(B_55))
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_46,plain,(
    ! [B_42] :
      ( ~ v1_subset_1(B_42,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_106,plain,(
    ! [B_55] :
      ( ~ v1_subset_1(B_55,B_55)
      | ~ r1_tarski(B_55,B_55) ) ),
    inference(resolution,[status(thm)],[c_102,c_46])).

tff(c_109,plain,(
    ! [B_55] : ~ v1_subset_1(B_55,B_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_106])).

tff(c_50,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_497,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_485])).

tff(c_508,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_497])).

tff(c_522,plain,
    ( v1_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_508,c_44])).

tff(c_900,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_522])).

tff(c_1196,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),k2_struct_0('#skF_3'))
    | k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_576,c_900,c_576,c_537])).

tff(c_1197,plain,(
    k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1196])).

tff(c_1214,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_101])).

tff(c_918,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_71])).

tff(c_1204,plain,(
    u1_struct_0('#skF_2') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_918])).

tff(c_32,plain,(
    ! [B_27,A_25] :
      ( m1_subset_1(u1_struct_0(B_27),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1160,plain,(
    ! [B_115,A_116] :
      ( v1_subset_1(u1_struct_0(B_115),u1_struct_0(A_116))
      | ~ m1_subset_1(u1_struct_0(B_115),k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ v1_tex_2(B_115,A_116)
      | ~ m1_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2177,plain,(
    ! [B_157,A_158] :
      ( v1_subset_1(u1_struct_0(B_157),u1_struct_0(A_158))
      | ~ v1_tex_2(B_157,A_158)
      | ~ m1_pre_topc(B_157,A_158)
      | ~ l1_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_32,c_1160])).

tff(c_2187,plain,(
    ! [B_157] :
      ( v1_subset_1(u1_struct_0(B_157),'#skF_1'('#skF_2','#skF_4'))
      | ~ v1_tex_2(B_157,'#skF_2')
      | ~ m1_pre_topc(B_157,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1204,c_2177])).

tff(c_5086,plain,(
    ! [B_231] :
      ( v1_subset_1(u1_struct_0(B_231),'#skF_1'('#skF_2','#skF_4'))
      | ~ v1_tex_2(B_231,'#skF_2')
      | ~ m1_pre_topc(B_231,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2187])).

tff(c_5104,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),'#skF_1'('#skF_2','#skF_4'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1214,c_5086])).

tff(c_5115,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_4'),'#skF_1'('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_5104])).

tff(c_5117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_5115])).

tff(c_5118,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1196])).

tff(c_764,plain,(
    ! [A_98,B_99] :
      ( ~ v1_subset_1('#skF_1'(A_98,B_99),u1_struct_0(A_98))
      | v1_tex_2(B_99,A_98)
      | ~ m1_pre_topc(B_99,A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_776,plain,(
    ! [B_99] :
      ( ~ v1_subset_1('#skF_1'('#skF_2',B_99),k2_struct_0('#skF_2'))
      | v1_tex_2(B_99,'#skF_2')
      | ~ m1_pre_topc(B_99,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_764])).

tff(c_783,plain,(
    ! [B_99] :
      ( ~ v1_subset_1('#skF_1'('#skF_2',B_99),k2_struct_0('#skF_2'))
      | v1_tex_2(B_99,'#skF_2')
      | ~ m1_pre_topc(B_99,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_776])).

tff(c_6742,plain,(
    ! [B_297] :
      ( ~ v1_subset_1('#skF_1'('#skF_2',B_297),k2_struct_0('#skF_3'))
      | v1_tex_2(B_297,'#skF_2')
      | ~ m1_pre_topc(B_297,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_783])).

tff(c_6745,plain,
    ( v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_5118,c_6742])).

tff(c_6751,plain,(
    v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6745])).

tff(c_6753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_6751])).

tff(c_6755,plain,(
    k2_struct_0('#skF_2') != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_522])).

tff(c_6759,plain,(
    k2_struct_0('#skF_3') != '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_6755])).

tff(c_151,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(u1_struct_0(B_65),u1_struct_0(A_66))
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_171,plain,(
    ! [B_65] :
      ( r1_tarski(u1_struct_0(B_65),k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_65,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_151])).

tff(c_226,plain,(
    ! [B_70] :
      ( r1_tarski(u1_struct_0(B_70),k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_70,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_171])).

tff(c_231,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_226])).

tff(c_240,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_231])).

tff(c_6775,plain,(
    r1_tarski(k2_struct_0('#skF_3'),'#skF_1'('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_240])).

tff(c_579,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_510])).

tff(c_6766,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1('#skF_1'('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_579])).

tff(c_266,plain,(
    ! [A_72,B_73] :
      ( v1_pre_topc(k1_pre_topc(A_72,B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_275,plain,(
    ! [B_73] :
      ( v1_pre_topc(k1_pre_topc('#skF_4',B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_266])).

tff(c_540,plain,(
    ! [B_89] :
      ( v1_pre_topc(k1_pre_topc('#skF_4',B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_275])).

tff(c_560,plain,(
    ! [A_91] :
      ( v1_pre_topc(k1_pre_topc('#skF_4',A_91))
      | ~ r1_tarski(A_91,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_540])).

tff(c_569,plain,(
    v1_pre_topc(k1_pre_topc('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_6,c_560])).

tff(c_661,plain,(
    v1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_569])).

tff(c_14,plain,(
    ! [A_5,B_9] :
      ( k2_struct_0(k1_pre_topc(A_5,B_9)) = B_9
      | ~ m1_pre_topc(k1_pre_topc(A_5,B_9),A_5)
      | ~ v1_pre_topc(k1_pre_topc(A_5,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7461,plain,
    ( k2_struct_0(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) = '#skF_1'('#skF_2','#skF_4')
    | ~ v1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_7433,c_14])).

tff(c_7467,plain,(
    k2_struct_0(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_6766,c_585,c_661,c_7461])).

tff(c_10413,plain,(
    ! [A_408] :
      ( u1_struct_0(k1_pre_topc(A_408,u1_struct_0(A_408))) = k2_struct_0(k1_pre_topc(A_408,u1_struct_0(A_408)))
      | ~ l1_pre_topc(A_408) ) ),
    inference(resolution,[status(thm)],[c_7436,c_66])).

tff(c_10650,plain,
    ( u1_struct_0(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) = k2_struct_0(k1_pre_topc('#skF_4',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_10413])).

tff(c_10667,plain,(
    u1_struct_0(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_7467,c_585,c_10650])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7823,plain,(
    ! [B_353,A_354] :
      ( u1_struct_0(B_353) = u1_struct_0(A_354)
      | ~ r1_tarski(u1_struct_0(A_354),u1_struct_0(B_353))
      | ~ m1_pre_topc(B_353,A_354)
      | ~ l1_pre_topc(A_354) ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_7841,plain,(
    ! [B_353] :
      ( u1_struct_0(B_353) = u1_struct_0('#skF_3')
      | ~ r1_tarski(k2_struct_0('#skF_3'),u1_struct_0(B_353))
      | ~ m1_pre_topc(B_353,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_7823])).

tff(c_7857,plain,(
    ! [B_353] :
      ( u1_struct_0(B_353) = k2_struct_0('#skF_3')
      | ~ r1_tarski(k2_struct_0('#skF_3'),u1_struct_0(B_353))
      | ~ m1_pre_topc(B_353,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_101,c_7841])).

tff(c_10691,plain,
    ( u1_struct_0(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) = k2_struct_0('#skF_3')
    | ~ r1_tarski(k2_struct_0('#skF_3'),'#skF_1'('#skF_2','#skF_4'))
    | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10667,c_7857])).

tff(c_10897,plain,
    ( k2_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6775,c_10667,c_10691])).

tff(c_10898,plain,(
    ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_6759,c_10897])).

tff(c_14296,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4')),'#skF_4')
    | ~ l1_pre_topc(k1_pre_topc('#skF_4','#skF_1'('#skF_2','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_14279,c_10898])).

tff(c_14341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7453,c_7433,c_14296])).

tff(c_14342,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_4'),k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6756])).

tff(c_14846,plain,(
    ! [B_502] :
      ( ~ v1_subset_1('#skF_1'('#skF_2',B_502),k2_struct_0('#skF_2'))
      | v1_tex_2(B_502,'#skF_2')
      | ~ m1_pre_topc(B_502,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_776])).

tff(c_14849,plain,
    ( v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_14342,c_14846])).

tff(c_14855,plain,(
    v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14849])).

tff(c_14857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_14855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.44/3.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.50  
% 9.44/3.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.50  %$ v1_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.44/3.50  
% 9.44/3.50  %Foreground sorts:
% 9.44/3.50  
% 9.44/3.50  
% 9.44/3.50  %Background operators:
% 9.44/3.50  
% 9.44/3.50  
% 9.44/3.50  %Foreground operators:
% 9.44/3.50  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 9.44/3.50  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.44/3.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.44/3.50  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 9.44/3.50  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 9.44/3.50  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 9.44/3.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.44/3.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.44/3.50  tff('#skF_2', type, '#skF_2': $i).
% 9.44/3.50  tff('#skF_3', type, '#skF_3': $i).
% 9.44/3.50  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.44/3.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.44/3.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.44/3.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.44/3.50  tff('#skF_4', type, '#skF_4': $i).
% 9.44/3.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.44/3.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.44/3.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.44/3.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.44/3.50  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.44/3.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.44/3.50  
% 9.44/3.52  tff(f_138, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (((g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) & v1_tex_2(B, A)) => v1_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tex_2)).
% 9.44/3.52  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.44/3.52  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.44/3.52  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.44/3.52  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 9.44/3.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.44/3.52  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.44/3.52  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 9.44/3.52  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 9.44/3.52  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 9.44/3.52  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 9.44/3.52  tff(f_123, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 9.44/3.52  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 9.44/3.52  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 9.44/3.52  tff(c_48, plain, (~v1_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.44/3.52  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.44/3.52  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.44/3.52  tff(c_81, plain, (![B_52, A_53]: (l1_pre_topc(B_52) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.44/3.52  tff(c_84, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_81])).
% 9.44/3.52  tff(c_90, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_84])).
% 9.44/3.52  tff(c_22, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.44/3.52  tff(c_62, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.44/3.52  tff(c_66, plain, (![A_15]: (u1_struct_0(A_15)=k2_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(resolution, [status(thm)], [c_22, c_62])).
% 9.44/3.52  tff(c_97, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_90, c_66])).
% 9.44/3.52  tff(c_570, plain, (![B_92, A_93]: (u1_struct_0(B_92)='#skF_1'(A_93, B_92) | v1_tex_2(B_92, A_93) | ~m1_pre_topc(B_92, A_93) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.44/3.52  tff(c_573, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_570, c_48])).
% 9.44/3.52  tff(c_576, plain, (k2_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_97, c_573])).
% 9.44/3.52  tff(c_585, plain, (u1_struct_0('#skF_4')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_576, c_97])).
% 9.44/3.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.44/3.52  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.44/3.52  tff(c_328, plain, (![A_77, B_78]: (m1_pre_topc(k1_pre_topc(A_77, B_78), A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.44/3.52  tff(c_7374, plain, (![A_330, A_331]: (m1_pre_topc(k1_pre_topc(A_330, A_331), A_330) | ~l1_pre_topc(A_330) | ~r1_tarski(A_331, u1_struct_0(A_330)))), inference(resolution, [status(thm)], [c_10, c_328])).
% 9.44/3.52  tff(c_7403, plain, (![A_332]: (m1_pre_topc(k1_pre_topc(A_332, u1_struct_0(A_332)), A_332) | ~l1_pre_topc(A_332))), inference(resolution, [status(thm)], [c_6, c_7374])).
% 9.44/3.52  tff(c_24, plain, (![B_18, A_16]: (l1_pre_topc(B_18) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.44/3.52  tff(c_7436, plain, (![A_333]: (l1_pre_topc(k1_pre_topc(A_333, u1_struct_0(A_333))) | ~l1_pre_topc(A_333))), inference(resolution, [status(thm)], [c_7403, c_24])).
% 9.44/3.52  tff(c_7445, plain, (l1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_585, c_7436])).
% 9.44/3.52  tff(c_7453, plain, (l1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_7445])).
% 9.44/3.52  tff(c_7422, plain, (m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_585, c_7403])).
% 9.44/3.52  tff(c_7433, plain, (m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_7422])).
% 9.44/3.52  tff(c_672, plain, (![A_94, B_95]: (m1_pre_topc(A_94, g1_pre_topc(u1_struct_0(B_95), u1_pre_topc(B_95))) | ~m1_pre_topc(A_94, B_95) | ~l1_pre_topc(B_95) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.44/3.52  tff(c_681, plain, (![A_94]: (m1_pre_topc(A_94, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_94, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_94))), inference(superposition, [status(thm), theory('equality')], [c_585, c_672])).
% 9.44/3.52  tff(c_14240, plain, (![A_469]: (m1_pre_topc(A_469, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_469, '#skF_4') | ~l1_pre_topc(A_469))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_681])).
% 9.44/3.52  tff(c_56, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.44/3.52  tff(c_87, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_81])).
% 9.44/3.52  tff(c_93, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_87])).
% 9.44/3.52  tff(c_101, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_93, c_66])).
% 9.44/3.52  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.44/3.52  tff(c_111, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_52])).
% 9.44/3.52  tff(c_120, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_111])).
% 9.44/3.52  tff(c_451, plain, (![B_85, A_86]: (m1_pre_topc(B_85, A_86) | ~m1_pre_topc(B_85, g1_pre_topc(u1_struct_0(A_86), u1_pre_topc(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.44/3.52  tff(c_454, plain, (![B_85]: (m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc(B_85, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_451])).
% 9.44/3.52  tff(c_462, plain, (![B_85]: (m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc(B_85, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_120, c_454])).
% 9.44/3.52  tff(c_7611, plain, (![B_85]: (m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc(B_85, g1_pre_topc('#skF_1'('#skF_2', '#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_576, c_462])).
% 9.44/3.52  tff(c_14279, plain, (![A_470]: (m1_pre_topc(A_470, '#skF_3') | ~m1_pre_topc(A_470, '#skF_4') | ~l1_pre_topc(A_470))), inference(resolution, [status(thm)], [c_14240, c_7611])).
% 9.44/3.52  tff(c_67, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_pre_topc(A_50))), inference(resolution, [status(thm)], [c_22, c_62])).
% 9.44/3.52  tff(c_71, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_67])).
% 9.44/3.52  tff(c_179, plain, (![B_67, A_68]: (m1_subset_1(u1_struct_0(B_67), k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.44/3.52  tff(c_203, plain, (![B_67]: (m1_subset_1(u1_struct_0(B_67), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_67, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_179])).
% 9.44/3.52  tff(c_485, plain, (![B_88]: (m1_subset_1(u1_struct_0(B_88), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_88, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_203])).
% 9.44/3.52  tff(c_500, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_97, c_485])).
% 9.44/3.52  tff(c_510, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_500])).
% 9.44/3.52  tff(c_44, plain, (![B_42, A_41]: (v1_subset_1(B_42, A_41) | B_42=A_41 | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.44/3.52  tff(c_537, plain, (v1_subset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_510, c_44])).
% 9.44/3.52  tff(c_6756, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_576, c_576, c_537])).
% 9.44/3.52  tff(c_6757, plain, (k2_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_6756])).
% 9.44/3.52  tff(c_102, plain, (![A_54, B_55]: (m1_subset_1(A_54, k1_zfmisc_1(B_55)) | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.44/3.52  tff(c_46, plain, (![B_42]: (~v1_subset_1(B_42, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.44/3.52  tff(c_106, plain, (![B_55]: (~v1_subset_1(B_55, B_55) | ~r1_tarski(B_55, B_55))), inference(resolution, [status(thm)], [c_102, c_46])).
% 9.44/3.52  tff(c_109, plain, (![B_55]: (~v1_subset_1(B_55, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_106])).
% 9.44/3.52  tff(c_50, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.44/3.52  tff(c_497, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_485])).
% 9.44/3.52  tff(c_508, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_497])).
% 9.44/3.52  tff(c_522, plain, (v1_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_508, c_44])).
% 9.44/3.52  tff(c_900, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_522])).
% 9.44/3.52  tff(c_1196, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), k2_struct_0('#skF_3')) | k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_900, c_576, c_900, c_576, c_537])).
% 9.44/3.52  tff(c_1197, plain, (k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_1196])).
% 9.44/3.52  tff(c_1214, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_101])).
% 9.44/3.52  tff(c_918, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_900, c_71])).
% 9.44/3.52  tff(c_1204, plain, (u1_struct_0('#skF_2')='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_918])).
% 9.44/3.52  tff(c_32, plain, (![B_27, A_25]: (m1_subset_1(u1_struct_0(B_27), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_95])).
% 9.44/3.52  tff(c_1160, plain, (![B_115, A_116]: (v1_subset_1(u1_struct_0(B_115), u1_struct_0(A_116)) | ~m1_subset_1(u1_struct_0(B_115), k1_zfmisc_1(u1_struct_0(A_116))) | ~v1_tex_2(B_115, A_116) | ~m1_pre_topc(B_115, A_116) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.44/3.52  tff(c_2177, plain, (![B_157, A_158]: (v1_subset_1(u1_struct_0(B_157), u1_struct_0(A_158)) | ~v1_tex_2(B_157, A_158) | ~m1_pre_topc(B_157, A_158) | ~l1_pre_topc(A_158))), inference(resolution, [status(thm)], [c_32, c_1160])).
% 9.44/3.52  tff(c_2187, plain, (![B_157]: (v1_subset_1(u1_struct_0(B_157), '#skF_1'('#skF_2', '#skF_4')) | ~v1_tex_2(B_157, '#skF_2') | ~m1_pre_topc(B_157, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1204, c_2177])).
% 9.44/3.52  tff(c_5086, plain, (![B_231]: (v1_subset_1(u1_struct_0(B_231), '#skF_1'('#skF_2', '#skF_4')) | ~v1_tex_2(B_231, '#skF_2') | ~m1_pre_topc(B_231, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2187])).
% 9.44/3.52  tff(c_5104, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), '#skF_1'('#skF_2', '#skF_4')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1214, c_5086])).
% 9.44/3.52  tff(c_5115, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), '#skF_1'('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_5104])).
% 9.44/3.52  tff(c_5117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_5115])).
% 9.44/3.52  tff(c_5118, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1196])).
% 9.44/3.52  tff(c_764, plain, (![A_98, B_99]: (~v1_subset_1('#skF_1'(A_98, B_99), u1_struct_0(A_98)) | v1_tex_2(B_99, A_98) | ~m1_pre_topc(B_99, A_98) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_116])).
% 9.44/3.52  tff(c_776, plain, (![B_99]: (~v1_subset_1('#skF_1'('#skF_2', B_99), k2_struct_0('#skF_2')) | v1_tex_2(B_99, '#skF_2') | ~m1_pre_topc(B_99, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_764])).
% 9.44/3.52  tff(c_783, plain, (![B_99]: (~v1_subset_1('#skF_1'('#skF_2', B_99), k2_struct_0('#skF_2')) | v1_tex_2(B_99, '#skF_2') | ~m1_pre_topc(B_99, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_776])).
% 9.44/3.52  tff(c_6742, plain, (![B_297]: (~v1_subset_1('#skF_1'('#skF_2', B_297), k2_struct_0('#skF_3')) | v1_tex_2(B_297, '#skF_2') | ~m1_pre_topc(B_297, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_900, c_783])).
% 9.44/3.52  tff(c_6745, plain, (v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_5118, c_6742])).
% 9.44/3.52  tff(c_6751, plain, (v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6745])).
% 9.44/3.52  tff(c_6753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_6751])).
% 9.44/3.52  tff(c_6755, plain, (k2_struct_0('#skF_2')!=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_522])).
% 9.44/3.52  tff(c_6759, plain, (k2_struct_0('#skF_3')!='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_6755])).
% 9.44/3.52  tff(c_151, plain, (![B_65, A_66]: (r1_tarski(u1_struct_0(B_65), u1_struct_0(A_66)) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.44/3.52  tff(c_171, plain, (![B_65]: (r1_tarski(u1_struct_0(B_65), k2_struct_0('#skF_2')) | ~m1_pre_topc(B_65, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_151])).
% 9.44/3.52  tff(c_226, plain, (![B_70]: (r1_tarski(u1_struct_0(B_70), k2_struct_0('#skF_2')) | ~m1_pre_topc(B_70, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_171])).
% 9.44/3.52  tff(c_231, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_101, c_226])).
% 9.44/3.52  tff(c_240, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_231])).
% 9.44/3.52  tff(c_6775, plain, (r1_tarski(k2_struct_0('#skF_3'), '#skF_1'('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_240])).
% 9.44/3.52  tff(c_579, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_576, c_510])).
% 9.44/3.52  tff(c_6766, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_1'('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_579])).
% 9.44/3.52  tff(c_266, plain, (![A_72, B_73]: (v1_pre_topc(k1_pre_topc(A_72, B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.44/3.52  tff(c_275, plain, (![B_73]: (v1_pre_topc(k1_pre_topc('#skF_4', B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_266])).
% 9.44/3.52  tff(c_540, plain, (![B_89]: (v1_pre_topc(k1_pre_topc('#skF_4', B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_275])).
% 9.44/3.52  tff(c_560, plain, (![A_91]: (v1_pre_topc(k1_pre_topc('#skF_4', A_91)) | ~r1_tarski(A_91, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_540])).
% 9.44/3.52  tff(c_569, plain, (v1_pre_topc(k1_pre_topc('#skF_4', k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_560])).
% 9.44/3.52  tff(c_661, plain, (v1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_576, c_569])).
% 9.44/3.52  tff(c_14, plain, (![A_5, B_9]: (k2_struct_0(k1_pre_topc(A_5, B_9))=B_9 | ~m1_pre_topc(k1_pre_topc(A_5, B_9), A_5) | ~v1_pre_topc(k1_pre_topc(A_5, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.44/3.52  tff(c_7461, plain, (k2_struct_0(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))='#skF_1'('#skF_2', '#skF_4') | ~v1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_7433, c_14])).
% 9.44/3.52  tff(c_7467, plain, (k2_struct_0(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_6766, c_585, c_661, c_7461])).
% 9.44/3.52  tff(c_10413, plain, (![A_408]: (u1_struct_0(k1_pre_topc(A_408, u1_struct_0(A_408)))=k2_struct_0(k1_pre_topc(A_408, u1_struct_0(A_408))) | ~l1_pre_topc(A_408))), inference(resolution, [status(thm)], [c_7436, c_66])).
% 9.44/3.52  tff(c_10650, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))=k2_struct_0(k1_pre_topc('#skF_4', u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_585, c_10413])).
% 9.44/3.52  tff(c_10667, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))='#skF_1'('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_7467, c_585, c_10650])).
% 9.44/3.52  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.44/3.52  tff(c_7823, plain, (![B_353, A_354]: (u1_struct_0(B_353)=u1_struct_0(A_354) | ~r1_tarski(u1_struct_0(A_354), u1_struct_0(B_353)) | ~m1_pre_topc(B_353, A_354) | ~l1_pre_topc(A_354))), inference(resolution, [status(thm)], [c_151, c_2])).
% 9.44/3.52  tff(c_7841, plain, (![B_353]: (u1_struct_0(B_353)=u1_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), u1_struct_0(B_353)) | ~m1_pre_topc(B_353, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_101, c_7823])).
% 9.44/3.52  tff(c_7857, plain, (![B_353]: (u1_struct_0(B_353)=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), u1_struct_0(B_353)) | ~m1_pre_topc(B_353, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_101, c_7841])).
% 9.44/3.52  tff(c_10691, plain, (u1_struct_0(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))=k2_struct_0('#skF_3') | ~r1_tarski(k2_struct_0('#skF_3'), '#skF_1'('#skF_2', '#skF_4')) | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10667, c_7857])).
% 9.44/3.52  tff(c_10897, plain, (k2_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_4') | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6775, c_10667, c_10691])).
% 9.44/3.52  tff(c_10898, plain, (~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_6759, c_10897])).
% 9.44/3.52  tff(c_14296, plain, (~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')), '#skF_4') | ~l1_pre_topc(k1_pre_topc('#skF_4', '#skF_1'('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_14279, c_10898])).
% 9.44/3.52  tff(c_14341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7453, c_7433, c_14296])).
% 9.44/3.52  tff(c_14342, plain, (v1_subset_1('#skF_1'('#skF_2', '#skF_4'), k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_6756])).
% 9.44/3.52  tff(c_14846, plain, (![B_502]: (~v1_subset_1('#skF_1'('#skF_2', B_502), k2_struct_0('#skF_2')) | v1_tex_2(B_502, '#skF_2') | ~m1_pre_topc(B_502, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_776])).
% 9.44/3.52  tff(c_14849, plain, (v1_tex_2('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_14342, c_14846])).
% 9.44/3.52  tff(c_14855, plain, (v1_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_14849])).
% 9.44/3.52  tff(c_14857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_14855])).
% 9.44/3.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.44/3.52  
% 9.44/3.52  Inference rules
% 9.44/3.52  ----------------------
% 9.44/3.52  #Ref     : 0
% 9.44/3.52  #Sup     : 3232
% 9.44/3.52  #Fact    : 0
% 9.44/3.52  #Define  : 0
% 9.44/3.52  #Split   : 17
% 9.44/3.52  #Chain   : 0
% 9.44/3.52  #Close   : 0
% 9.44/3.52  
% 9.44/3.52  Ordering : KBO
% 9.44/3.52  
% 9.44/3.52  Simplification rules
% 9.44/3.52  ----------------------
% 9.44/3.52  #Subsume      : 709
% 9.44/3.52  #Demod        : 4027
% 9.44/3.52  #Tautology    : 817
% 9.44/3.52  #SimpNegUnit  : 245
% 9.44/3.52  #BackRed      : 74
% 9.44/3.52  
% 9.44/3.52  #Partial instantiations: 0
% 9.44/3.52  #Strategies tried      : 1
% 9.44/3.52  
% 9.44/3.52  Timing (in seconds)
% 9.44/3.52  ----------------------
% 9.44/3.53  Preprocessing        : 0.33
% 9.44/3.53  Parsing              : 0.17
% 9.44/3.53  CNF conversion       : 0.02
% 9.44/3.53  Main loop            : 2.40
% 9.44/3.53  Inferencing          : 0.64
% 9.44/3.53  Reduction            : 0.96
% 9.44/3.53  Demodulation         : 0.68
% 9.44/3.53  BG Simplification    : 0.07
% 9.44/3.53  Subsumption          : 0.56
% 9.44/3.53  Abstraction          : 0.09
% 9.44/3.53  MUC search           : 0.00
% 9.44/3.53  Cooper               : 0.00
% 9.44/3.53  Total                : 2.78
% 9.44/3.53  Index Insertion      : 0.00
% 9.44/3.53  Index Deletion       : 0.00
% 9.44/3.53  Index Matching       : 0.00
% 9.44/3.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
