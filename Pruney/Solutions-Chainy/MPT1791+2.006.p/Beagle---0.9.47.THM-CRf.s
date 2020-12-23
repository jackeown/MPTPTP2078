%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:49 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 750 expanded)
%              Number of leaves         :   31 ( 266 expanded)
%              Depth                    :   14
%              Number of atoms          :  338 (1919 expanded)
%              Number of equality atoms :   64 ( 401 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_139,negated_conjecture,(
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

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_12,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    ! [A_26] :
      ( u1_struct_0(A_26) = k2_struct_0(A_26)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_12,c_50])).

tff(c_59,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_42,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_65,plain,
    ( g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_42])).

tff(c_66,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_60,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_34])).

tff(c_108,plain,(
    ! [B_31,A_32] :
      ( v3_pre_topc(B_31,A_32)
      | ~ r2_hidden(B_31,u1_pre_topc(A_32))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_114,plain,(
    ! [B_31] :
      ( v3_pre_topc(B_31,'#skF_1')
      | ~ r2_hidden(B_31,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_108])).

tff(c_118,plain,(
    ! [B_33] :
      ( v3_pre_topc(B_33,'#skF_1')
      | ~ r2_hidden(B_33,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_114])).

tff(c_124,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_118])).

tff(c_128,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_124])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_722,plain,(
    ! [B_66,A_67] :
      ( r2_hidden(B_66,u1_pre_topc(A_67))
      | k5_tmap_1(A_67,B_66) != u1_pre_topc(A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_734,plain,(
    ! [B_66] :
      ( r2_hidden(B_66,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_66) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_722])).

tff(c_741,plain,(
    ! [B_66] :
      ( r2_hidden(B_66,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_66) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_734])).

tff(c_745,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_68) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_741])).

tff(c_751,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_745])).

tff(c_756,plain,(
    k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_751])).

tff(c_67,plain,(
    ! [A_28] :
      ( m1_subset_1(k2_struct_0(A_28),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_70,plain,
    ( m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1')))
    | ~ l1_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_67])).

tff(c_72,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_75,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_72])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_75])).

tff(c_80,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_195,plain,(
    ! [A_42,B_43] :
      ( l1_pre_topc(k6_tmap_1(A_42,B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_201,plain,(
    ! [B_43] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_195])).

tff(c_204,plain,(
    ! [B_43] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_201])).

tff(c_206,plain,(
    ! [B_44] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_204])).

tff(c_213,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_80,c_206])).

tff(c_297,plain,(
    ! [A_46,B_47] :
      ( v1_pre_topc(k6_tmap_1(A_46,B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_309,plain,(
    ! [B_47] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_297])).

tff(c_316,plain,(
    ! [B_47] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_309])).

tff(c_318,plain,(
    ! [B_48] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_316])).

tff(c_325,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_80,c_318])).

tff(c_48,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_102,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_48])).

tff(c_103,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_102])).

tff(c_406,plain,(
    ! [A_57,B_58] :
      ( u1_struct_0(k6_tmap_1(A_57,B_58)) = u1_struct_0(A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_418,plain,(
    ! [B_58] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_58)) = u1_struct_0('#skF_1')
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_406])).

tff(c_425,plain,(
    ! [B_58] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_58)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_59,c_418])).

tff(c_427,plain,(
    ! [B_59] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_59)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_425])).

tff(c_434,plain,(
    u1_struct_0(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_427])).

tff(c_14,plain,(
    ! [A_8] :
      ( v3_pre_topc(k2_struct_0(A_8),A_8)
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_125,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_118])).

tff(c_129,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_130,plain,(
    ! [B_34,A_35] :
      ( r2_hidden(B_34,u1_pre_topc(A_35))
      | ~ v3_pre_topc(B_34,A_35)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,(
    ! [B_34] :
      ( r2_hidden(B_34,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_34,'#skF_1')
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_130])).

tff(c_140,plain,(
    ! [B_36] :
      ( r2_hidden(B_36,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_36,'#skF_1')
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_136])).

tff(c_143,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_140])).

tff(c_149,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_143])).

tff(c_154,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_149])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_154])).

tff(c_160,plain,(
    r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_846,plain,(
    ! [A_71,B_72] :
      ( k5_tmap_1(A_71,B_72) = u1_pre_topc(A_71)
      | ~ r2_hidden(B_72,u1_pre_topc(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_861,plain,(
    ! [B_72] :
      ( k5_tmap_1('#skF_1',B_72) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_72,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_846])).

tff(c_868,plain,(
    ! [B_72] :
      ( k5_tmap_1('#skF_1',B_72) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_72,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_861])).

tff(c_870,plain,(
    ! [B_73] :
      ( k5_tmap_1('#skF_1',B_73) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_73,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_868])).

tff(c_873,plain,
    ( k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) = u1_pre_topc('#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_870])).

tff(c_879,plain,(
    k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_873])).

tff(c_619,plain,(
    ! [A_60,B_61] :
      ( u1_pre_topc(k6_tmap_1(A_60,B_61)) = k5_tmap_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_631,plain,(
    ! [B_61] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_61)) = k5_tmap_1('#skF_1',B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_619])).

tff(c_638,plain,(
    ! [B_61] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_61)) = k5_tmap_1('#skF_1',B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_631])).

tff(c_646,plain,(
    ! [B_62] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_62)) = k5_tmap_1('#skF_1',B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_638])).

tff(c_653,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_646])).

tff(c_884,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_653])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_900,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ v1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_2])).

tff(c_908,plain,(
    k6_tmap_1('#skF_1',k2_struct_0('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_325,c_103,c_434,c_900])).

tff(c_911,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_908,c_884])).

tff(c_654,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_646])).

tff(c_956,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_654])).

tff(c_958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_956])).

tff(c_959,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_960,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_1008,plain,(
    ! [B_79,A_80] :
      ( r2_hidden(B_79,u1_pre_topc(A_80))
      | ~ v3_pre_topc(B_79,A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1014,plain,(
    ! [B_79] :
      ( r2_hidden(B_79,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_79,'#skF_1')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_1008])).

tff(c_1051,plain,(
    ! [B_83] :
      ( r2_hidden(B_83,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_83,'#skF_1')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1014])).

tff(c_1057,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1051])).

tff(c_1063,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_960,c_1057])).

tff(c_1615,plain,(
    ! [A_111,B_112] :
      ( k5_tmap_1(A_111,B_112) = u1_pre_topc(A_111)
      | ~ r2_hidden(B_112,u1_pre_topc(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1627,plain,(
    ! [B_112] :
      ( k5_tmap_1('#skF_1',B_112) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_112,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_1615])).

tff(c_1634,plain,(
    ! [B_112] :
      ( k5_tmap_1('#skF_1',B_112) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_112,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1627])).

tff(c_1640,plain,(
    ! [B_113] :
      ( k5_tmap_1('#skF_1',B_113) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_113,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1634])).

tff(c_1646,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_1640])).

tff(c_1652,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1646])).

tff(c_1502,plain,(
    ! [A_105,B_106] :
      ( u1_pre_topc(k6_tmap_1(A_105,B_106)) = k5_tmap_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1514,plain,(
    ! [B_106] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_106)) = k5_tmap_1('#skF_1',B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_1502])).

tff(c_1521,plain,(
    ! [B_106] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_106)) = k5_tmap_1('#skF_1',B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1514])).

tff(c_1525,plain,(
    ! [B_107] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_107)) = k5_tmap_1('#skF_1',B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1521])).

tff(c_1533,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1525])).

tff(c_1097,plain,(
    ! [A_90,B_91] :
      ( l1_pre_topc(k6_tmap_1(A_90,B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1103,plain,(
    ! [B_91] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_1097])).

tff(c_1106,plain,(
    ! [B_91] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1103])).

tff(c_1108,plain,(
    ! [B_92] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_92))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1106])).

tff(c_1116,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_1108])).

tff(c_1064,plain,(
    ! [A_84,B_85] :
      ( v1_pre_topc(k6_tmap_1(A_84,B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1070,plain,(
    ! [B_85] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_1064])).

tff(c_1073,plain,(
    ! [B_85] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1070])).

tff(c_1075,plain,(
    ! [B_86] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_86))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1073])).

tff(c_1083,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_1075])).

tff(c_1271,plain,(
    ! [A_102,B_103] :
      ( u1_struct_0(k6_tmap_1(A_102,B_103)) = u1_struct_0(A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1283,plain,(
    ! [B_103] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_103)) = u1_struct_0('#skF_1')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_1271])).

tff(c_1290,plain,(
    ! [B_103] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_103)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_59,c_1283])).

tff(c_1292,plain,(
    ! [B_104] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_104)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1290])).

tff(c_1300,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_1292])).

tff(c_1325,plain,
    ( g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1300,c_2])).

tff(c_1346,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_1083,c_1325])).

tff(c_1534,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1533,c_1346])).

tff(c_1653,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1652,c_1534])).

tff(c_1657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_959,c_1653])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:54:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.73  
% 3.79/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.73  %$ m2_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.79/1.73  
% 3.79/1.73  %Foreground sorts:
% 3.79/1.73  
% 3.79/1.73  
% 3.79/1.73  %Background operators:
% 3.79/1.73  
% 3.79/1.73  
% 3.79/1.73  %Foreground operators:
% 3.79/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.79/1.73  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.79/1.73  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.79/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.73  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.79/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.79/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.79/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.79/1.73  tff('#skF_1', type, '#skF_1': $i).
% 3.79/1.73  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.79/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/1.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.79/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.73  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.79/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.79/1.73  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.79/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.79/1.73  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.79/1.73  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.79/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/1.73  
% 4.09/1.76  tff(f_139, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 4.09/1.76  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.09/1.76  tff(f_35, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.09/1.76  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 4.09/1.76  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 4.09/1.76  tff(f_48, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 4.09/1.76  tff(f_96, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 4.09/1.76  tff(f_124, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 4.09/1.76  tff(f_58, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.09/1.76  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.09/1.76  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.09/1.76  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.09/1.76  tff(c_50, plain, (![A_26]: (u1_struct_0(A_26)=k2_struct_0(A_26) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.09/1.76  tff(c_55, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_12, c_50])).
% 4.09/1.76  tff(c_59, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_55])).
% 4.09/1.76  tff(c_42, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.09/1.76  tff(c_65, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_42])).
% 4.09/1.76  tff(c_66, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_65])).
% 4.09/1.76  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.09/1.76  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_34])).
% 4.09/1.76  tff(c_108, plain, (![B_31, A_32]: (v3_pre_topc(B_31, A_32) | ~r2_hidden(B_31, u1_pre_topc(A_32)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.09/1.76  tff(c_114, plain, (![B_31]: (v3_pre_topc(B_31, '#skF_1') | ~r2_hidden(B_31, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_31, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_108])).
% 4.09/1.76  tff(c_118, plain, (![B_33]: (v3_pre_topc(B_33, '#skF_1') | ~r2_hidden(B_33, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_33, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_114])).
% 4.09/1.76  tff(c_124, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_118])).
% 4.09/1.76  tff(c_128, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_66, c_124])).
% 4.09/1.76  tff(c_40, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.09/1.76  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.09/1.76  tff(c_722, plain, (![B_66, A_67]: (r2_hidden(B_66, u1_pre_topc(A_67)) | k5_tmap_1(A_67, B_66)!=u1_pre_topc(A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.09/1.76  tff(c_734, plain, (![B_66]: (r2_hidden(B_66, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_66)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_722])).
% 4.09/1.76  tff(c_741, plain, (![B_66]: (r2_hidden(B_66, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_66)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_734])).
% 4.09/1.76  tff(c_745, plain, (![B_68]: (r2_hidden(B_68, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_68)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_741])).
% 4.09/1.76  tff(c_751, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_745])).
% 4.09/1.76  tff(c_756, plain, (k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_128, c_751])).
% 4.09/1.76  tff(c_67, plain, (![A_28]: (m1_subset_1(k2_struct_0(A_28), k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.09/1.76  tff(c_70, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_59, c_67])).
% 4.09/1.76  tff(c_72, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_70])).
% 4.09/1.76  tff(c_75, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_72])).
% 4.09/1.76  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_75])).
% 4.09/1.76  tff(c_80, plain, (m1_subset_1(k2_struct_0('#skF_1'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_70])).
% 4.09/1.76  tff(c_195, plain, (![A_42, B_43]: (l1_pre_topc(k6_tmap_1(A_42, B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.09/1.76  tff(c_201, plain, (![B_43]: (l1_pre_topc(k6_tmap_1('#skF_1', B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_195])).
% 4.09/1.76  tff(c_204, plain, (![B_43]: (l1_pre_topc(k6_tmap_1('#skF_1', B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_201])).
% 4.09/1.76  tff(c_206, plain, (![B_44]: (l1_pre_topc(k6_tmap_1('#skF_1', B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_204])).
% 4.09/1.76  tff(c_213, plain, (l1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_80, c_206])).
% 4.09/1.76  tff(c_297, plain, (![A_46, B_47]: (v1_pre_topc(k6_tmap_1(A_46, B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.09/1.76  tff(c_309, plain, (![B_47]: (v1_pre_topc(k6_tmap_1('#skF_1', B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_297])).
% 4.09/1.76  tff(c_316, plain, (![B_47]: (v1_pre_topc(k6_tmap_1('#skF_1', B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_309])).
% 4.09/1.76  tff(c_318, plain, (![B_48]: (v1_pre_topc(k6_tmap_1('#skF_1', B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_316])).
% 4.09/1.76  tff(c_325, plain, (v1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_80, c_318])).
% 4.09/1.76  tff(c_48, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.09/1.76  tff(c_102, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_48])).
% 4.09/1.76  tff(c_103, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_102])).
% 4.09/1.76  tff(c_406, plain, (![A_57, B_58]: (u1_struct_0(k6_tmap_1(A_57, B_58))=u1_struct_0(A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.09/1.76  tff(c_418, plain, (![B_58]: (u1_struct_0(k6_tmap_1('#skF_1', B_58))=u1_struct_0('#skF_1') | ~m1_subset_1(B_58, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_406])).
% 4.09/1.76  tff(c_425, plain, (![B_58]: (u1_struct_0(k6_tmap_1('#skF_1', B_58))=k2_struct_0('#skF_1') | ~m1_subset_1(B_58, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_59, c_418])).
% 4.09/1.76  tff(c_427, plain, (![B_59]: (u1_struct_0(k6_tmap_1('#skF_1', B_59))=k2_struct_0('#skF_1') | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_425])).
% 4.09/1.76  tff(c_434, plain, (u1_struct_0(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_427])).
% 4.09/1.76  tff(c_14, plain, (![A_8]: (v3_pre_topc(k2_struct_0(A_8), A_8) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.09/1.76  tff(c_125, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_80, c_118])).
% 4.09/1.76  tff(c_129, plain, (~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_125])).
% 4.09/1.76  tff(c_130, plain, (![B_34, A_35]: (r2_hidden(B_34, u1_pre_topc(A_35)) | ~v3_pre_topc(B_34, A_35) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.09/1.76  tff(c_136, plain, (![B_34]: (r2_hidden(B_34, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_34, '#skF_1') | ~m1_subset_1(B_34, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_130])).
% 4.09/1.76  tff(c_140, plain, (![B_36]: (r2_hidden(B_36, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_36, '#skF_1') | ~m1_subset_1(B_36, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_136])).
% 4.09/1.76  tff(c_143, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_80, c_140])).
% 4.09/1.76  tff(c_149, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_129, c_143])).
% 4.09/1.76  tff(c_154, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_149])).
% 4.09/1.76  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_154])).
% 4.09/1.76  tff(c_160, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_125])).
% 4.09/1.76  tff(c_846, plain, (![A_71, B_72]: (k5_tmap_1(A_71, B_72)=u1_pre_topc(A_71) | ~r2_hidden(B_72, u1_pre_topc(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.09/1.76  tff(c_861, plain, (![B_72]: (k5_tmap_1('#skF_1', B_72)=u1_pre_topc('#skF_1') | ~r2_hidden(B_72, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_72, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_846])).
% 4.09/1.76  tff(c_868, plain, (![B_72]: (k5_tmap_1('#skF_1', B_72)=u1_pre_topc('#skF_1') | ~r2_hidden(B_72, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_72, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_861])).
% 4.09/1.76  tff(c_870, plain, (![B_73]: (k5_tmap_1('#skF_1', B_73)=u1_pre_topc('#skF_1') | ~r2_hidden(B_73, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_868])).
% 4.09/1.76  tff(c_873, plain, (k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))=u1_pre_topc('#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_80, c_870])).
% 4.09/1.76  tff(c_879, plain, (k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_873])).
% 4.09/1.76  tff(c_619, plain, (![A_60, B_61]: (u1_pre_topc(k6_tmap_1(A_60, B_61))=k5_tmap_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.09/1.76  tff(c_631, plain, (![B_61]: (u1_pre_topc(k6_tmap_1('#skF_1', B_61))=k5_tmap_1('#skF_1', B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_619])).
% 4.09/1.76  tff(c_638, plain, (![B_61]: (u1_pre_topc(k6_tmap_1('#skF_1', B_61))=k5_tmap_1('#skF_1', B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_631])).
% 4.09/1.76  tff(c_646, plain, (![B_62]: (u1_pre_topc(k6_tmap_1('#skF_1', B_62))=k5_tmap_1('#skF_1', B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_638])).
% 4.09/1.76  tff(c_653, plain, (u1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_80, c_646])).
% 4.09/1.76  tff(c_884, plain, (u1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_879, c_653])).
% 4.09/1.76  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.76  tff(c_900, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', k2_struct_0('#skF_1')) | ~v1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_884, c_2])).
% 4.09/1.76  tff(c_908, plain, (k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_213, c_325, c_103, c_434, c_900])).
% 4.09/1.76  tff(c_911, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_908, c_884])).
% 4.09/1.76  tff(c_654, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_646])).
% 4.09/1.76  tff(c_956, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_911, c_654])).
% 4.09/1.76  tff(c_958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_756, c_956])).
% 4.09/1.76  tff(c_959, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_65])).
% 4.09/1.76  tff(c_960, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_65])).
% 4.09/1.76  tff(c_1008, plain, (![B_79, A_80]: (r2_hidden(B_79, u1_pre_topc(A_80)) | ~v3_pre_topc(B_79, A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.09/1.76  tff(c_1014, plain, (![B_79]: (r2_hidden(B_79, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_79, '#skF_1') | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_1008])).
% 4.09/1.76  tff(c_1051, plain, (![B_83]: (r2_hidden(B_83, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_83, '#skF_1') | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1014])).
% 4.09/1.76  tff(c_1057, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_1051])).
% 4.09/1.76  tff(c_1063, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_960, c_1057])).
% 4.09/1.76  tff(c_1615, plain, (![A_111, B_112]: (k5_tmap_1(A_111, B_112)=u1_pre_topc(A_111) | ~r2_hidden(B_112, u1_pre_topc(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.09/1.76  tff(c_1627, plain, (![B_112]: (k5_tmap_1('#skF_1', B_112)=u1_pre_topc('#skF_1') | ~r2_hidden(B_112, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_1615])).
% 4.09/1.76  tff(c_1634, plain, (![B_112]: (k5_tmap_1('#skF_1', B_112)=u1_pre_topc('#skF_1') | ~r2_hidden(B_112, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1627])).
% 4.09/1.76  tff(c_1640, plain, (![B_113]: (k5_tmap_1('#skF_1', B_113)=u1_pre_topc('#skF_1') | ~r2_hidden(B_113, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_113, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_1634])).
% 4.09/1.76  tff(c_1646, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_1640])).
% 4.09/1.76  tff(c_1652, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1646])).
% 4.09/1.76  tff(c_1502, plain, (![A_105, B_106]: (u1_pre_topc(k6_tmap_1(A_105, B_106))=k5_tmap_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105) | ~v2_pre_topc(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.09/1.76  tff(c_1514, plain, (![B_106]: (u1_pre_topc(k6_tmap_1('#skF_1', B_106))=k5_tmap_1('#skF_1', B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_1502])).
% 4.09/1.76  tff(c_1521, plain, (![B_106]: (u1_pre_topc(k6_tmap_1('#skF_1', B_106))=k5_tmap_1('#skF_1', B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1514])).
% 4.09/1.76  tff(c_1525, plain, (![B_107]: (u1_pre_topc(k6_tmap_1('#skF_1', B_107))=k5_tmap_1('#skF_1', B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_1521])).
% 4.09/1.76  tff(c_1533, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_1525])).
% 4.09/1.76  tff(c_1097, plain, (![A_90, B_91]: (l1_pre_topc(k6_tmap_1(A_90, B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.09/1.76  tff(c_1103, plain, (![B_91]: (l1_pre_topc(k6_tmap_1('#skF_1', B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_1097])).
% 4.09/1.76  tff(c_1106, plain, (![B_91]: (l1_pre_topc(k6_tmap_1('#skF_1', B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1103])).
% 4.09/1.76  tff(c_1108, plain, (![B_92]: (l1_pre_topc(k6_tmap_1('#skF_1', B_92)) | ~m1_subset_1(B_92, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_1106])).
% 4.09/1.76  tff(c_1116, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_1108])).
% 4.09/1.76  tff(c_1064, plain, (![A_84, B_85]: (v1_pre_topc(k6_tmap_1(A_84, B_85)) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.09/1.76  tff(c_1070, plain, (![B_85]: (v1_pre_topc(k6_tmap_1('#skF_1', B_85)) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_1064])).
% 4.09/1.76  tff(c_1073, plain, (![B_85]: (v1_pre_topc(k6_tmap_1('#skF_1', B_85)) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1070])).
% 4.09/1.76  tff(c_1075, plain, (![B_86]: (v1_pre_topc(k6_tmap_1('#skF_1', B_86)) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_1073])).
% 4.09/1.76  tff(c_1083, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_1075])).
% 4.09/1.76  tff(c_1271, plain, (![A_102, B_103]: (u1_struct_0(k6_tmap_1(A_102, B_103))=u1_struct_0(A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.09/1.76  tff(c_1283, plain, (![B_103]: (u1_struct_0(k6_tmap_1('#skF_1', B_103))=u1_struct_0('#skF_1') | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_1271])).
% 4.09/1.76  tff(c_1290, plain, (![B_103]: (u1_struct_0(k6_tmap_1('#skF_1', B_103))=k2_struct_0('#skF_1') | ~m1_subset_1(B_103, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_59, c_1283])).
% 4.09/1.76  tff(c_1292, plain, (![B_104]: (u1_struct_0(k6_tmap_1('#skF_1', B_104))=k2_struct_0('#skF_1') | ~m1_subset_1(B_104, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_1290])).
% 4.09/1.76  tff(c_1300, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_1292])).
% 4.09/1.76  tff(c_1325, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1300, c_2])).
% 4.09/1.76  tff(c_1346, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_1083, c_1325])).
% 4.09/1.76  tff(c_1534, plain, (g1_pre_topc(k2_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1533, c_1346])).
% 4.09/1.76  tff(c_1653, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1652, c_1534])).
% 4.09/1.76  tff(c_1657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_959, c_1653])).
% 4.09/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.76  
% 4.09/1.76  Inference rules
% 4.09/1.76  ----------------------
% 4.09/1.76  #Ref     : 0
% 4.09/1.76  #Sup     : 335
% 4.09/1.76  #Fact    : 0
% 4.09/1.76  #Define  : 0
% 4.09/1.76  #Split   : 14
% 4.09/1.76  #Chain   : 0
% 4.09/1.76  #Close   : 0
% 4.09/1.76  
% 4.09/1.76  Ordering : KBO
% 4.09/1.76  
% 4.09/1.76  Simplification rules
% 4.09/1.76  ----------------------
% 4.09/1.76  #Subsume      : 5
% 4.09/1.76  #Demod        : 539
% 4.09/1.76  #Tautology    : 147
% 4.09/1.76  #SimpNegUnit  : 32
% 4.09/1.76  #BackRed      : 28
% 4.09/1.76  
% 4.09/1.76  #Partial instantiations: 0
% 4.09/1.76  #Strategies tried      : 1
% 4.09/1.76  
% 4.09/1.76  Timing (in seconds)
% 4.09/1.76  ----------------------
% 4.09/1.76  Preprocessing        : 0.33
% 4.09/1.76  Parsing              : 0.17
% 4.09/1.76  CNF conversion       : 0.02
% 4.09/1.76  Main loop            : 0.62
% 4.09/1.76  Inferencing          : 0.20
% 4.09/1.76  Reduction            : 0.22
% 4.09/1.76  Demodulation         : 0.16
% 4.09/1.76  BG Simplification    : 0.03
% 4.09/1.76  Subsumption          : 0.11
% 4.09/1.76  Abstraction          : 0.03
% 4.09/1.76  MUC search           : 0.00
% 4.09/1.76  Cooper               : 0.00
% 4.09/1.76  Total                : 1.01
% 4.09/1.76  Index Insertion      : 0.00
% 4.09/1.76  Index Deletion       : 0.00
% 4.09/1.76  Index Matching       : 0.00
% 4.09/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
