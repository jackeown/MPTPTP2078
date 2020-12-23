%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:52 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 270 expanded)
%              Number of leaves         :   30 ( 109 expanded)
%              Depth                    :   11
%              Number of atoms          :  212 ( 868 expanded)
%              Number of equality atoms :   25 ( 109 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_109,plain,(
    ! [A_60,B_61] :
      ( l1_pre_topc(k6_tmap_1(A_60,B_61))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_112,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_109])).

tff(c_115,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_112])).

tff(c_116,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_115])).

tff(c_34,plain,(
    ! [A_46] :
      ( m1_pre_topc(A_46,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_57,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_71,plain,(
    ! [A_53,B_54] :
      ( m1_pre_topc(A_53,g1_pre_topc(u1_struct_0(B_54),u1_pre_topc(B_54)))
      | ~ m1_pre_topc(A_53,B_54)
      | ~ l1_pre_topc(B_54)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_77,plain,(
    ! [A_53] :
      ( m1_pre_topc(A_53,k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_pre_topc(A_53,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_71])).

tff(c_80,plain,(
    ! [A_53] :
      ( m1_pre_topc(A_53,k6_tmap_1('#skF_1','#skF_2'))
      | ~ m1_pre_topc(A_53,'#skF_1')
      | ~ l1_pre_topc(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_77])).

tff(c_179,plain,(
    ! [B_71,A_72] :
      ( r2_hidden(B_71,k5_tmap_1(A_72,B_71))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_183,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_179])).

tff(c_187,plain,
    ( r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_183])).

tff(c_188,plain,(
    r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_187])).

tff(c_453,plain,(
    ! [A_90,B_91] :
      ( u1_pre_topc(k6_tmap_1(A_90,B_91)) = k5_tmap_1(A_90,B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_468,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_453])).

tff(c_475,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_468])).

tff(c_476,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_475])).

tff(c_151,plain,(
    ! [C_67,A_68,B_69] :
      ( m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(B_69)))
      | ~ m1_pre_topc(B_69,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_155,plain,(
    ! [A_70] :
      ( m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_pre_topc('#skF_1',A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_36,c_151])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_pre_topc(B_3,A_1)
      | ~ r2_hidden(B_3,u1_pre_topc(A_1))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_177,plain,(
    ! [A_70] :
      ( v3_pre_topc('#skF_2',A_70)
      | ~ r2_hidden('#skF_2',u1_pre_topc(A_70))
      | ~ m1_pre_topc('#skF_1',A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_492,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ r2_hidden('#skF_2',k5_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_177])).

tff(c_510,plain,
    ( v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_188,c_492])).

tff(c_516,plain,(
    ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_510])).

tff(c_519,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_516])).

tff(c_522,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_519])).

tff(c_554,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_522])).

tff(c_558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_554])).

tff(c_560,plain,(
    m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_510])).

tff(c_559,plain,(
    v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_510])).

tff(c_247,plain,(
    ! [A_82,B_83] :
      ( u1_struct_0(k6_tmap_1(A_82,B_83)) = u1_struct_0(A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_253,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_247])).

tff(c_257,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_253])).

tff(c_258,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_257])).

tff(c_44,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_63,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_44])).

tff(c_1084,plain,(
    ! [D_115,C_116,A_117] :
      ( v3_pre_topc(D_115,C_116)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0(C_116)))
      | ~ v3_pre_topc(D_115,A_117)
      | ~ m1_pre_topc(C_116,A_117)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1094,plain,(
    ! [A_117] :
      ( v3_pre_topc('#skF_2','#skF_1')
      | ~ v3_pre_topc('#skF_2',A_117)
      | ~ m1_pre_topc('#skF_1',A_117)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_36,c_1084])).

tff(c_1100,plain,(
    ! [A_118] :
      ( ~ v3_pre_topc('#skF_2',A_118)
      | ~ m1_pre_topc('#skF_1',A_118)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_1094])).

tff(c_1109,plain,
    ( ~ v3_pre_topc('#skF_2',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_pre_topc('#skF_1',k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_1100])).

tff(c_1119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_36,c_560,c_559,c_1109])).

tff(c_1121,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1120,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1129,plain,(
    ! [B_121,A_122] :
      ( r2_hidden(B_121,u1_pre_topc(A_122))
      | ~ v3_pre_topc(B_121,A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1132,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1129])).

tff(c_1135,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1120,c_1132])).

tff(c_1459,plain,(
    ! [A_156,B_157] :
      ( k5_tmap_1(A_156,B_157) = u1_pre_topc(A_156)
      | ~ r2_hidden(B_157,u1_pre_topc(A_156))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156)
      | ~ v2_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1471,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1459])).

tff(c_1477,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1135,c_1471])).

tff(c_1478,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1477])).

tff(c_1627,plain,(
    ! [A_162,B_163] :
      ( g1_pre_topc(u1_struct_0(A_162),k5_tmap_1(A_162,B_163)) = k6_tmap_1(A_162,B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1635,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1627])).

tff(c_1641,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1478,c_1635])).

tff(c_1643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1121,c_1641])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.68  
% 4.10/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.69  %$ v3_pre_topc > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.10/1.69  
% 4.10/1.69  %Foreground sorts:
% 4.10/1.69  
% 4.10/1.69  
% 4.10/1.69  %Background operators:
% 4.10/1.69  
% 4.10/1.69  
% 4.10/1.69  %Foreground operators:
% 4.10/1.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.10/1.69  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.10/1.69  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.10/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.69  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.10/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.10/1.69  tff('#skF_2', type, '#skF_2': $i).
% 4.10/1.69  tff('#skF_1', type, '#skF_1': $i).
% 4.10/1.69  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.10/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.69  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 4.10/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.69  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.10/1.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.10/1.69  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 4.10/1.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.10/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.69  
% 4.10/1.71  tff(f_163, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 4.10/1.71  tff(f_104, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 4.10/1.71  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.10/1.71  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.10/1.71  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_tmap_1)).
% 4.10/1.71  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 4.10/1.71  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.10/1.71  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 4.10/1.71  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 4.10/1.71  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 4.10/1.71  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 4.10/1.71  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.10/1.71  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.10/1.71  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.10/1.71  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.10/1.71  tff(c_109, plain, (![A_60, B_61]: (l1_pre_topc(k6_tmap_1(A_60, B_61)) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.10/1.71  tff(c_112, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_109])).
% 4.10/1.71  tff(c_115, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_112])).
% 4.10/1.71  tff(c_116, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_115])).
% 4.10/1.71  tff(c_34, plain, (![A_46]: (m1_pre_topc(A_46, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_148])).
% 4.10/1.71  tff(c_50, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.10/1.71  tff(c_57, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 4.10/1.71  tff(c_71, plain, (![A_53, B_54]: (m1_pre_topc(A_53, g1_pre_topc(u1_struct_0(B_54), u1_pre_topc(B_54))) | ~m1_pre_topc(A_53, B_54) | ~l1_pre_topc(B_54) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.10/1.71  tff(c_77, plain, (![A_53]: (m1_pre_topc(A_53, k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc(A_53, '#skF_1') | ~l1_pre_topc('#skF_1') | ~l1_pre_topc(A_53))), inference(superposition, [status(thm), theory('equality')], [c_57, c_71])).
% 4.10/1.71  tff(c_80, plain, (![A_53]: (m1_pre_topc(A_53, k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc(A_53, '#skF_1') | ~l1_pre_topc(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_77])).
% 4.10/1.71  tff(c_179, plain, (![B_71, A_72]: (r2_hidden(B_71, k5_tmap_1(A_72, B_71)) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.10/1.71  tff(c_183, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_179])).
% 4.10/1.71  tff(c_187, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_183])).
% 4.10/1.71  tff(c_188, plain, (r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_187])).
% 4.10/1.71  tff(c_453, plain, (![A_90, B_91]: (u1_pre_topc(k6_tmap_1(A_90, B_91))=k5_tmap_1(A_90, B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.10/1.71  tff(c_468, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_453])).
% 4.10/1.71  tff(c_475, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_468])).
% 4.10/1.71  tff(c_476, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_475])).
% 4.10/1.71  tff(c_151, plain, (![C_67, A_68, B_69]: (m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0(B_69))) | ~m1_pre_topc(B_69, A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.10/1.71  tff(c_155, plain, (![A_70]: (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_pre_topc('#skF_1', A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_36, c_151])).
% 4.10/1.71  tff(c_2, plain, (![B_3, A_1]: (v3_pre_topc(B_3, A_1) | ~r2_hidden(B_3, u1_pre_topc(A_1)) | ~m1_subset_1(B_3, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.10/1.71  tff(c_177, plain, (![A_70]: (v3_pre_topc('#skF_2', A_70) | ~r2_hidden('#skF_2', u1_pre_topc(A_70)) | ~m1_pre_topc('#skF_1', A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_155, c_2])).
% 4.10/1.71  tff(c_492, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~r2_hidden('#skF_2', k5_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_476, c_177])).
% 4.10/1.71  tff(c_510, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_188, c_492])).
% 4.10/1.71  tff(c_516, plain, (~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_510])).
% 4.10/1.71  tff(c_519, plain, (~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_80, c_516])).
% 4.10/1.71  tff(c_522, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_519])).
% 4.10/1.71  tff(c_554, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_522])).
% 4.10/1.71  tff(c_558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_554])).
% 4.10/1.71  tff(c_560, plain, (m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_510])).
% 4.10/1.71  tff(c_559, plain, (v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_510])).
% 4.10/1.71  tff(c_247, plain, (![A_82, B_83]: (u1_struct_0(k6_tmap_1(A_82, B_83))=u1_struct_0(A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.10/1.71  tff(c_253, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_247])).
% 4.10/1.71  tff(c_257, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_253])).
% 4.10/1.71  tff(c_258, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_257])).
% 4.10/1.71  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.10/1.71  tff(c_63, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_44])).
% 4.10/1.71  tff(c_1084, plain, (![D_115, C_116, A_117]: (v3_pre_topc(D_115, C_116) | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0(C_116))) | ~v3_pre_topc(D_115, A_117) | ~m1_pre_topc(C_116, A_117) | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.10/1.71  tff(c_1094, plain, (![A_117]: (v3_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc('#skF_2', A_117) | ~m1_pre_topc('#skF_1', A_117) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_36, c_1084])).
% 4.10/1.71  tff(c_1100, plain, (![A_118]: (~v3_pre_topc('#skF_2', A_118) | ~m1_pre_topc('#skF_1', A_118) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(negUnitSimplification, [status(thm)], [c_63, c_1094])).
% 4.10/1.71  tff(c_1109, plain, (~v3_pre_topc('#skF_2', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_pre_topc('#skF_1', k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_258, c_1100])).
% 4.10/1.71  tff(c_1119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_36, c_560, c_559, c_1109])).
% 4.10/1.71  tff(c_1121, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 4.10/1.71  tff(c_1120, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 4.10/1.71  tff(c_1129, plain, (![B_121, A_122]: (r2_hidden(B_121, u1_pre_topc(A_122)) | ~v3_pre_topc(B_121, A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.10/1.71  tff(c_1132, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1129])).
% 4.10/1.71  tff(c_1135, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1120, c_1132])).
% 4.10/1.71  tff(c_1459, plain, (![A_156, B_157]: (k5_tmap_1(A_156, B_157)=u1_pre_topc(A_156) | ~r2_hidden(B_157, u1_pre_topc(A_156)) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156) | ~v2_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.10/1.71  tff(c_1471, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1459])).
% 4.10/1.71  tff(c_1477, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1135, c_1471])).
% 4.10/1.71  tff(c_1478, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_1477])).
% 4.10/1.71  tff(c_1627, plain, (![A_162, B_163]: (g1_pre_topc(u1_struct_0(A_162), k5_tmap_1(A_162, B_163))=k6_tmap_1(A_162, B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.10/1.71  tff(c_1635, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1627])).
% 4.10/1.71  tff(c_1641, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1478, c_1635])).
% 4.10/1.71  tff(c_1643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1121, c_1641])).
% 4.10/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.71  
% 4.10/1.71  Inference rules
% 4.10/1.71  ----------------------
% 4.10/1.71  #Ref     : 0
% 4.10/1.71  #Sup     : 321
% 4.10/1.71  #Fact    : 0
% 4.10/1.71  #Define  : 0
% 4.10/1.71  #Split   : 6
% 4.10/1.71  #Chain   : 0
% 4.10/1.71  #Close   : 0
% 4.10/1.71  
% 4.10/1.71  Ordering : KBO
% 4.10/1.71  
% 4.10/1.71  Simplification rules
% 4.10/1.71  ----------------------
% 4.10/1.71  #Subsume      : 28
% 4.10/1.71  #Demod        : 421
% 4.10/1.71  #Tautology    : 131
% 4.10/1.71  #SimpNegUnit  : 38
% 4.10/1.71  #BackRed      : 3
% 4.10/1.71  
% 4.10/1.71  #Partial instantiations: 0
% 4.10/1.71  #Strategies tried      : 1
% 4.10/1.71  
% 4.10/1.71  Timing (in seconds)
% 4.10/1.71  ----------------------
% 4.10/1.71  Preprocessing        : 0.35
% 4.10/1.71  Parsing              : 0.18
% 4.10/1.71  CNF conversion       : 0.03
% 4.10/1.71  Main loop            : 0.58
% 4.10/1.71  Inferencing          : 0.19
% 4.10/1.71  Reduction            : 0.18
% 4.10/1.71  Demodulation         : 0.13
% 4.10/1.71  BG Simplification    : 0.03
% 4.10/1.71  Subsumption          : 0.13
% 4.10/1.71  Abstraction          : 0.03
% 4.10/1.71  MUC search           : 0.00
% 4.10/1.71  Cooper               : 0.00
% 4.10/1.71  Total                : 0.98
% 4.10/1.71  Index Insertion      : 0.00
% 4.10/1.71  Index Deletion       : 0.00
% 4.10/1.71  Index Matching       : 0.00
% 4.10/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
