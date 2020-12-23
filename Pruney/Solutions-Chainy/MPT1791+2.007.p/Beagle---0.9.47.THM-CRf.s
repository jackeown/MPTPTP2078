%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:50 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 760 expanded)
%              Number of leaves         :   33 ( 272 expanded)
%              Depth                    :   15
%              Number of atoms          :  349 (1950 expanded)
%              Number of equality atoms :   66 ( 409 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > k1_tops_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

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

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_12,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_12,c_52])).

tff(c_61,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_57])).

tff(c_50,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_67,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_50])).

tff(c_68,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_44,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_108,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_61,c_44])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_36])).

tff(c_166,plain,(
    ! [B_41,A_42] :
      ( v3_pre_topc(B_41,A_42)
      | ~ r2_hidden(B_41,u1_pre_topc(A_42))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_172,plain,(
    ! [B_41] :
      ( v3_pre_topc(B_41,'#skF_1')
      | ~ r2_hidden(B_41,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_166])).

tff(c_176,plain,(
    ! [B_43] :
      ( v3_pre_topc(B_43,'#skF_1')
      | ~ r2_hidden(B_43,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_172])).

tff(c_182,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_176])).

tff(c_188,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_182])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_781,plain,(
    ! [B_72,A_73] :
      ( r2_hidden(B_72,u1_pre_topc(A_73))
      | k5_tmap_1(A_73,B_72) != u1_pre_topc(A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_793,plain,(
    ! [B_72] :
      ( r2_hidden(B_72,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_72) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_781])).

tff(c_800,plain,(
    ! [B_72] :
      ( r2_hidden(B_72,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_72) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_793])).

tff(c_805,plain,(
    ! [B_74] :
      ( r2_hidden(B_74,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_74) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_800])).

tff(c_811,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_805])).

tff(c_816,plain,(
    k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_811])).

tff(c_16,plain,(
    ! [A_10] :
      ( k1_tops_1(A_10,k2_struct_0(A_10)) = k2_struct_0(A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_69,plain,(
    ! [A_30] :
      ( m1_subset_1(k2_struct_0(A_30),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_69])).

tff(c_77,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_80,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_77])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_85,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_118,plain,(
    ! [A_33,B_34] :
      ( v3_pre_topc(k1_tops_1(A_33,B_34),A_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_122,plain,(
    ! [B_34] :
      ( v3_pre_topc(k1_tops_1('#skF_1',B_34),'#skF_1')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_118])).

tff(c_126,plain,(
    ! [B_35] :
      ( v3_pre_topc(k1_tops_1('#skF_1',B_35),'#skF_1')
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_122])).

tff(c_133,plain,(
    v3_pre_topc(k1_tops_1('#skF_1',k2_struct_0('#skF_1')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_126])).

tff(c_137,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_133])).

tff(c_139,plain,(
    v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_137])).

tff(c_140,plain,(
    ! [B_36,A_37] :
      ( r2_hidden(B_36,u1_pre_topc(A_37))
      | ~ v3_pre_topc(B_36,A_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_146,plain,(
    ! [B_36] :
      ( r2_hidden(B_36,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_36,'#skF_1')
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_140])).

tff(c_154,plain,(
    ! [B_39] :
      ( r2_hidden(B_39,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_39,'#skF_1')
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_146])).

tff(c_157,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_154])).

tff(c_163,plain,(
    r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_157])).

tff(c_821,plain,(
    ! [A_75,B_76] :
      ( k5_tmap_1(A_75,B_76) = u1_pre_topc(A_75)
      | ~ r2_hidden(B_76,u1_pre_topc(A_75))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_833,plain,(
    ! [B_76] :
      ( k5_tmap_1('#skF_1',B_76) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_76,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_821])).

tff(c_840,plain,(
    ! [B_76] :
      ( k5_tmap_1('#skF_1',B_76) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_76,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_833])).

tff(c_846,plain,(
    ! [B_77] :
      ( k5_tmap_1('#skF_1',B_77) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_77,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_840])).

tff(c_849,plain,
    ( k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) = u1_pre_topc('#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_85,c_846])).

tff(c_855,plain,(
    k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_849])).

tff(c_242,plain,(
    ! [A_53,B_54] :
      ( l1_pre_topc(k6_tmap_1(A_53,B_54))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_248,plain,(
    ! [B_54] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_54))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_242])).

tff(c_251,plain,(
    ! [B_54] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_54))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_248])).

tff(c_253,plain,(
    ! [B_55] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_251])).

tff(c_260,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_85,c_253])).

tff(c_220,plain,(
    ! [A_48,B_49] :
      ( v1_pre_topc(k6_tmap_1(A_48,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_226,plain,(
    ! [B_49] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_220])).

tff(c_229,plain,(
    ! [B_49] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_226])).

tff(c_231,plain,(
    ! [B_50] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_229])).

tff(c_238,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_85,c_231])).

tff(c_430,plain,(
    ! [A_62,B_63] :
      ( u1_struct_0(k6_tmap_1(A_62,B_63)) = u1_struct_0(A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_442,plain,(
    ! [B_63] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_63)) = u1_struct_0('#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_430])).

tff(c_449,plain,(
    ! [B_63] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_63)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_61,c_442])).

tff(c_460,plain,(
    ! [B_65] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_65)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_449])).

tff(c_467,plain,(
    u1_struct_0(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_85,c_460])).

tff(c_679,plain,(
    ! [A_66,B_67] :
      ( u1_pre_topc(k6_tmap_1(A_66,B_67)) = k5_tmap_1(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_691,plain,(
    ! [B_67] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_67)) = k5_tmap_1('#skF_1',B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_679])).

tff(c_698,plain,(
    ! [B_67] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_67)) = k5_tmap_1('#skF_1',B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_691])).

tff(c_705,plain,(
    ! [B_68] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_68)) = k5_tmap_1('#skF_1',B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_698])).

tff(c_712,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_85,c_705])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_742,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))),k5_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ v1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_2])).

tff(c_750,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),k5_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k6_tmap_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_238,c_467,c_742])).

tff(c_858,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_750])).

tff(c_861,plain,(
    k6_tmap_1('#skF_1',k2_struct_0('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_858])).

tff(c_860,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_712])).

tff(c_886,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_861,c_860])).

tff(c_713,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_705])).

tff(c_927,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_886,c_713])).

tff(c_929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_816,c_927])).

tff(c_931,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_930,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_1073,plain,(
    ! [B_96,A_97] :
      ( r2_hidden(B_96,u1_pre_topc(A_97))
      | ~ v3_pre_topc(B_96,A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1079,plain,(
    ! [B_96] :
      ( r2_hidden(B_96,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_96,'#skF_1')
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_1073])).

tff(c_1092,plain,(
    ! [B_99] :
      ( r2_hidden(B_99,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_99,'#skF_1')
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1079])).

tff(c_1098,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_1092])).

tff(c_1104,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_1098])).

tff(c_1718,plain,(
    ! [A_129,B_130] :
      ( k5_tmap_1(A_129,B_130) = u1_pre_topc(A_129)
      | ~ r2_hidden(B_130,u1_pre_topc(A_129))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1730,plain,(
    ! [B_130] :
      ( k5_tmap_1('#skF_1',B_130) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_130,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_1718])).

tff(c_1737,plain,(
    ! [B_130] :
      ( k5_tmap_1('#skF_1',B_130) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_130,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1730])).

tff(c_1745,plain,(
    ! [B_131] :
      ( k5_tmap_1('#skF_1',B_131) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_131,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1737])).

tff(c_1751,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_1745])).

tff(c_1757,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_1751])).

tff(c_1111,plain,(
    ! [A_102,B_103] :
      ( l1_pre_topc(k6_tmap_1(A_102,B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1117,plain,(
    ! [B_103] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_1111])).

tff(c_1120,plain,(
    ! [B_103] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1117])).

tff(c_1122,plain,(
    ! [B_104] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_104))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1120])).

tff(c_1130,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_1122])).

tff(c_1288,plain,(
    ! [A_112,B_113] :
      ( v1_pre_topc(k6_tmap_1(A_112,B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1300,plain,(
    ! [B_113] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_1288])).

tff(c_1307,plain,(
    ! [B_113] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1300])).

tff(c_1309,plain,(
    ! [B_114] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_114))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1307])).

tff(c_1317,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_1309])).

tff(c_1352,plain,(
    ! [A_120,B_121] :
      ( u1_struct_0(k6_tmap_1(A_120,B_121)) = u1_struct_0(A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1364,plain,(
    ! [B_121] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_121)) = u1_struct_0('#skF_1')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_1352])).

tff(c_1371,plain,(
    ! [B_121] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_121)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_61,c_1364])).

tff(c_1394,plain,(
    ! [B_124] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_124)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1371])).

tff(c_1402,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_1394])).

tff(c_1373,plain,(
    ! [A_122,B_123] :
      ( u1_pre_topc(k6_tmap_1(A_122,B_123)) = k5_tmap_1(A_122,B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1385,plain,(
    ! [B_123] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_123)) = k5_tmap_1('#skF_1',B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_1373])).

tff(c_1392,plain,(
    ! [B_123] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_123)) = k5_tmap_1('#skF_1',B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1385])).

tff(c_1523,plain,(
    ! [B_125] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_125)) = k5_tmap_1('#skF_1',B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1392])).

tff(c_1531,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1523])).

tff(c_1599,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_2])).

tff(c_1607,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1317,c_1402,c_1599])).

tff(c_1758,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1757,c_1607])).

tff(c_1762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_931,c_1758])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.61  
% 3.62/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.61  %$ m2_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > k1_tops_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.62/1.61  
% 3.62/1.61  %Foreground sorts:
% 3.62/1.61  
% 3.62/1.61  
% 3.62/1.61  %Background operators:
% 3.62/1.61  
% 3.62/1.61  
% 3.62/1.61  %Foreground operators:
% 3.62/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.62/1.61  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.62/1.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.62/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.61  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.62/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.62/1.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.62/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.61  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.62/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.62/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.61  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.62/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.62/1.61  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.62/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.62/1.61  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.62/1.61  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.62/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.61  
% 3.62/1.63  tff(f_147, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.62/1.63  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.62/1.63  tff(f_35, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.62/1.63  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.62/1.63  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 3.62/1.63  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 3.62/1.63  tff(f_48, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.62/1.63  tff(f_60, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.62/1.63  tff(f_104, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.62/1.63  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.62/1.63  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.62/1.63  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.63  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.62/1.63  tff(c_52, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.62/1.63  tff(c_57, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_12, c_52])).
% 3.62/1.63  tff(c_61, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_57])).
% 3.62/1.63  tff(c_50, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.63  tff(c_67, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_50])).
% 3.62/1.63  tff(c_68, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_67])).
% 3.62/1.63  tff(c_44, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.63  tff(c_108, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_61, c_44])).
% 3.62/1.63  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.63  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_36])).
% 3.62/1.63  tff(c_166, plain, (![B_41, A_42]: (v3_pre_topc(B_41, A_42) | ~r2_hidden(B_41, u1_pre_topc(A_42)) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.63  tff(c_172, plain, (![B_41]: (v3_pre_topc(B_41, '#skF_1') | ~r2_hidden(B_41, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_41, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_166])).
% 3.62/1.63  tff(c_176, plain, (![B_43]: (v3_pre_topc(B_43, '#skF_1') | ~r2_hidden(B_43, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_172])).
% 3.62/1.63  tff(c_182, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_176])).
% 3.62/1.63  tff(c_188, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_108, c_182])).
% 3.62/1.63  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.63  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.62/1.63  tff(c_781, plain, (![B_72, A_73]: (r2_hidden(B_72, u1_pre_topc(A_73)) | k5_tmap_1(A_73, B_72)!=u1_pre_topc(A_73) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.62/1.63  tff(c_793, plain, (![B_72]: (r2_hidden(B_72, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_72)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_72, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_781])).
% 3.62/1.63  tff(c_800, plain, (![B_72]: (r2_hidden(B_72, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_72)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_72, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_793])).
% 3.62/1.63  tff(c_805, plain, (![B_74]: (r2_hidden(B_74, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_74)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_74, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_800])).
% 3.62/1.63  tff(c_811, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_805])).
% 3.62/1.63  tff(c_816, plain, (k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_188, c_811])).
% 3.62/1.63  tff(c_16, plain, (![A_10]: (k1_tops_1(A_10, k2_struct_0(A_10))=k2_struct_0(A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.62/1.63  tff(c_69, plain, (![A_30]: (m1_subset_1(k2_struct_0(A_30), k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.62/1.63  tff(c_72, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_69])).
% 3.62/1.63  tff(c_77, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_72])).
% 3.62/1.63  tff(c_80, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_77])).
% 3.62/1.63  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_80])).
% 3.62/1.63  tff(c_85, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_72])).
% 3.62/1.63  tff(c_118, plain, (![A_33, B_34]: (v3_pre_topc(k1_tops_1(A_33, B_34), A_33) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.62/1.63  tff(c_122, plain, (![B_34]: (v3_pre_topc(k1_tops_1('#skF_1', B_34), '#skF_1') | ~m1_subset_1(B_34, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_118])).
% 3.62/1.63  tff(c_126, plain, (![B_35]: (v3_pre_topc(k1_tops_1('#skF_1', B_35), '#skF_1') | ~m1_subset_1(B_35, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_122])).
% 3.62/1.63  tff(c_133, plain, (v3_pre_topc(k1_tops_1('#skF_1', k2_struct_0('#skF_1')), '#skF_1')), inference(resolution, [status(thm)], [c_85, c_126])).
% 3.62/1.63  tff(c_137, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_133])).
% 3.62/1.63  tff(c_139, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_137])).
% 3.62/1.63  tff(c_140, plain, (![B_36, A_37]: (r2_hidden(B_36, u1_pre_topc(A_37)) | ~v3_pre_topc(B_36, A_37) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_37))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.63  tff(c_146, plain, (![B_36]: (r2_hidden(B_36, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_36, '#skF_1') | ~m1_subset_1(B_36, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_140])).
% 3.62/1.63  tff(c_154, plain, (![B_39]: (r2_hidden(B_39, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_39, '#skF_1') | ~m1_subset_1(B_39, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_146])).
% 3.62/1.63  tff(c_157, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_85, c_154])).
% 3.62/1.63  tff(c_163, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_157])).
% 3.62/1.63  tff(c_821, plain, (![A_75, B_76]: (k5_tmap_1(A_75, B_76)=u1_pre_topc(A_75) | ~r2_hidden(B_76, u1_pre_topc(A_75)) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.62/1.63  tff(c_833, plain, (![B_76]: (k5_tmap_1('#skF_1', B_76)=u1_pre_topc('#skF_1') | ~r2_hidden(B_76, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_821])).
% 3.62/1.63  tff(c_840, plain, (![B_76]: (k5_tmap_1('#skF_1', B_76)=u1_pre_topc('#skF_1') | ~r2_hidden(B_76, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_833])).
% 3.62/1.63  tff(c_846, plain, (![B_77]: (k5_tmap_1('#skF_1', B_77)=u1_pre_topc('#skF_1') | ~r2_hidden(B_77, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_840])).
% 3.62/1.63  tff(c_849, plain, (k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))=u1_pre_topc('#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_85, c_846])).
% 3.62/1.63  tff(c_855, plain, (k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_849])).
% 3.62/1.63  tff(c_242, plain, (![A_53, B_54]: (l1_pre_topc(k6_tmap_1(A_53, B_54)) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.62/1.63  tff(c_248, plain, (![B_54]: (l1_pre_topc(k6_tmap_1('#skF_1', B_54)) | ~m1_subset_1(B_54, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_242])).
% 3.62/1.63  tff(c_251, plain, (![B_54]: (l1_pre_topc(k6_tmap_1('#skF_1', B_54)) | ~m1_subset_1(B_54, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_248])).
% 3.62/1.63  tff(c_253, plain, (![B_55]: (l1_pre_topc(k6_tmap_1('#skF_1', B_55)) | ~m1_subset_1(B_55, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_251])).
% 3.62/1.63  tff(c_260, plain, (l1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_85, c_253])).
% 3.62/1.63  tff(c_220, plain, (![A_48, B_49]: (v1_pre_topc(k6_tmap_1(A_48, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_48))) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.62/1.63  tff(c_226, plain, (![B_49]: (v1_pre_topc(k6_tmap_1('#skF_1', B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_220])).
% 3.62/1.63  tff(c_229, plain, (![B_49]: (v1_pre_topc(k6_tmap_1('#skF_1', B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_226])).
% 3.62/1.63  tff(c_231, plain, (![B_50]: (v1_pre_topc(k6_tmap_1('#skF_1', B_50)) | ~m1_subset_1(B_50, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_229])).
% 3.62/1.63  tff(c_238, plain, (v1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_85, c_231])).
% 3.62/1.63  tff(c_430, plain, (![A_62, B_63]: (u1_struct_0(k6_tmap_1(A_62, B_63))=u1_struct_0(A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.62/1.63  tff(c_442, plain, (![B_63]: (u1_struct_0(k6_tmap_1('#skF_1', B_63))=u1_struct_0('#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_430])).
% 3.62/1.63  tff(c_449, plain, (![B_63]: (u1_struct_0(k6_tmap_1('#skF_1', B_63))=k2_struct_0('#skF_1') | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_61, c_442])).
% 3.62/1.63  tff(c_460, plain, (![B_65]: (u1_struct_0(k6_tmap_1('#skF_1', B_65))=k2_struct_0('#skF_1') | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_449])).
% 3.62/1.63  tff(c_467, plain, (u1_struct_0(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_85, c_460])).
% 3.62/1.63  tff(c_679, plain, (![A_66, B_67]: (u1_pre_topc(k6_tmap_1(A_66, B_67))=k5_tmap_1(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.62/1.63  tff(c_691, plain, (![B_67]: (u1_pre_topc(k6_tmap_1('#skF_1', B_67))=k5_tmap_1('#skF_1', B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_679])).
% 3.62/1.63  tff(c_698, plain, (![B_67]: (u1_pre_topc(k6_tmap_1('#skF_1', B_67))=k5_tmap_1('#skF_1', B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_691])).
% 3.62/1.63  tff(c_705, plain, (![B_68]: (u1_pre_topc(k6_tmap_1('#skF_1', B_68))=k5_tmap_1('#skF_1', B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_698])).
% 3.62/1.63  tff(c_712, plain, (u1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_85, c_705])).
% 3.62/1.63  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.62/1.63  tff(c_742, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))), k5_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k6_tmap_1('#skF_1', k2_struct_0('#skF_1')) | ~v1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_712, c_2])).
% 3.62/1.63  tff(c_750, plain, (g1_pre_topc(k2_struct_0('#skF_1'), k5_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_238, c_467, c_742])).
% 3.62/1.63  tff(c_858, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_855, c_750])).
% 3.62/1.63  tff(c_861, plain, (k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_858])).
% 3.62/1.63  tff(c_860, plain, (u1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_855, c_712])).
% 3.62/1.63  tff(c_886, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_861, c_860])).
% 3.62/1.63  tff(c_713, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_705])).
% 3.62/1.63  tff(c_927, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_886, c_713])).
% 3.62/1.63  tff(c_929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_816, c_927])).
% 3.62/1.63  tff(c_931, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_67])).
% 3.62/1.63  tff(c_930, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_67])).
% 3.62/1.63  tff(c_1073, plain, (![B_96, A_97]: (r2_hidden(B_96, u1_pre_topc(A_97)) | ~v3_pre_topc(B_96, A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.62/1.63  tff(c_1079, plain, (![B_96]: (r2_hidden(B_96, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_96, '#skF_1') | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_1073])).
% 3.62/1.63  tff(c_1092, plain, (![B_99]: (r2_hidden(B_99, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_99, '#skF_1') | ~m1_subset_1(B_99, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1079])).
% 3.62/1.63  tff(c_1098, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_1092])).
% 3.62/1.63  tff(c_1104, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_930, c_1098])).
% 3.62/1.63  tff(c_1718, plain, (![A_129, B_130]: (k5_tmap_1(A_129, B_130)=u1_pre_topc(A_129) | ~r2_hidden(B_130, u1_pre_topc(A_129)) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.62/1.63  tff(c_1730, plain, (![B_130]: (k5_tmap_1('#skF_1', B_130)=u1_pre_topc('#skF_1') | ~r2_hidden(B_130, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_130, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_1718])).
% 3.62/1.63  tff(c_1737, plain, (![B_130]: (k5_tmap_1('#skF_1', B_130)=u1_pre_topc('#skF_1') | ~r2_hidden(B_130, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_130, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1730])).
% 3.62/1.63  tff(c_1745, plain, (![B_131]: (k5_tmap_1('#skF_1', B_131)=u1_pre_topc('#skF_1') | ~r2_hidden(B_131, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_131, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_1737])).
% 3.62/1.63  tff(c_1751, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_1745])).
% 3.62/1.63  tff(c_1757, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_1751])).
% 3.62/1.63  tff(c_1111, plain, (![A_102, B_103]: (l1_pre_topc(k6_tmap_1(A_102, B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.62/1.63  tff(c_1117, plain, (![B_103]: (l1_pre_topc(k6_tmap_1('#skF_1', B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_1111])).
% 3.62/1.63  tff(c_1120, plain, (![B_103]: (l1_pre_topc(k6_tmap_1('#skF_1', B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1117])).
% 3.62/1.63  tff(c_1122, plain, (![B_104]: (l1_pre_topc(k6_tmap_1('#skF_1', B_104)) | ~m1_subset_1(B_104, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_1120])).
% 3.62/1.63  tff(c_1130, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_1122])).
% 3.62/1.63  tff(c_1288, plain, (![A_112, B_113]: (v1_pre_topc(k6_tmap_1(A_112, B_113)) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.62/1.63  tff(c_1300, plain, (![B_113]: (v1_pre_topc(k6_tmap_1('#skF_1', B_113)) | ~m1_subset_1(B_113, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_1288])).
% 3.62/1.63  tff(c_1307, plain, (![B_113]: (v1_pre_topc(k6_tmap_1('#skF_1', B_113)) | ~m1_subset_1(B_113, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1300])).
% 3.62/1.63  tff(c_1309, plain, (![B_114]: (v1_pre_topc(k6_tmap_1('#skF_1', B_114)) | ~m1_subset_1(B_114, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_1307])).
% 3.62/1.63  tff(c_1317, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_1309])).
% 3.62/1.63  tff(c_1352, plain, (![A_120, B_121]: (u1_struct_0(k6_tmap_1(A_120, B_121))=u1_struct_0(A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.62/1.63  tff(c_1364, plain, (![B_121]: (u1_struct_0(k6_tmap_1('#skF_1', B_121))=u1_struct_0('#skF_1') | ~m1_subset_1(B_121, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_1352])).
% 3.62/1.63  tff(c_1371, plain, (![B_121]: (u1_struct_0(k6_tmap_1('#skF_1', B_121))=k2_struct_0('#skF_1') | ~m1_subset_1(B_121, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_61, c_1364])).
% 3.62/1.63  tff(c_1394, plain, (![B_124]: (u1_struct_0(k6_tmap_1('#skF_1', B_124))=k2_struct_0('#skF_1') | ~m1_subset_1(B_124, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_1371])).
% 3.62/1.63  tff(c_1402, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_1394])).
% 3.62/1.63  tff(c_1373, plain, (![A_122, B_123]: (u1_pre_topc(k6_tmap_1(A_122, B_123))=k5_tmap_1(A_122, B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.62/1.63  tff(c_1385, plain, (![B_123]: (u1_pre_topc(k6_tmap_1('#skF_1', B_123))=k5_tmap_1('#skF_1', B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_1373])).
% 3.62/1.63  tff(c_1392, plain, (![B_123]: (u1_pre_topc(k6_tmap_1('#skF_1', B_123))=k5_tmap_1('#skF_1', B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1385])).
% 3.62/1.63  tff(c_1523, plain, (![B_125]: (u1_pre_topc(k6_tmap_1('#skF_1', B_125))=k5_tmap_1('#skF_1', B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_42, c_1392])).
% 3.62/1.63  tff(c_1531, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_1523])).
% 3.62/1.63  tff(c_1599, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1531, c_2])).
% 3.62/1.63  tff(c_1607, plain, (g1_pre_topc(k2_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1317, c_1402, c_1599])).
% 3.62/1.63  tff(c_1758, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1757, c_1607])).
% 3.62/1.63  tff(c_1762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_931, c_1758])).
% 3.62/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.63  
% 3.62/1.63  Inference rules
% 3.62/1.63  ----------------------
% 3.62/1.63  #Ref     : 0
% 3.62/1.63  #Sup     : 361
% 3.62/1.63  #Fact    : 0
% 3.62/1.63  #Define  : 0
% 3.62/1.63  #Split   : 12
% 3.62/1.63  #Chain   : 0
% 3.62/1.63  #Close   : 0
% 3.62/1.63  
% 3.62/1.63  Ordering : KBO
% 3.62/1.63  
% 3.62/1.63  Simplification rules
% 3.62/1.63  ----------------------
% 3.62/1.63  #Subsume      : 4
% 3.62/1.63  #Demod        : 595
% 3.62/1.63  #Tautology    : 142
% 3.62/1.63  #SimpNegUnit  : 26
% 3.62/1.63  #BackRed      : 29
% 3.62/1.63  
% 3.62/1.63  #Partial instantiations: 0
% 3.62/1.63  #Strategies tried      : 1
% 3.62/1.63  
% 3.62/1.63  Timing (in seconds)
% 3.62/1.63  ----------------------
% 3.62/1.64  Preprocessing        : 0.32
% 3.62/1.64  Parsing              : 0.17
% 3.62/1.64  CNF conversion       : 0.02
% 3.62/1.64  Main loop            : 0.53
% 3.62/1.64  Inferencing          : 0.19
% 3.62/1.64  Reduction            : 0.19
% 3.62/1.64  Demodulation         : 0.13
% 3.62/1.64  BG Simplification    : 0.02
% 3.62/1.64  Subsumption          : 0.09
% 3.62/1.64  Abstraction          : 0.03
% 3.62/1.64  MUC search           : 0.00
% 3.62/1.64  Cooper               : 0.00
% 3.62/1.64  Total                : 0.91
% 3.62/1.64  Index Insertion      : 0.00
% 3.62/1.64  Index Deletion       : 0.00
% 3.62/1.64  Index Matching       : 0.00
% 3.62/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
