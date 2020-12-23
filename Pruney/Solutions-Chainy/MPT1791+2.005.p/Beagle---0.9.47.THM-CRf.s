%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:49 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 637 expanded)
%              Number of leaves         :   32 ( 232 expanded)
%              Depth                    :   14
%              Number of atoms          :  334 (1618 expanded)
%              Number of equality atoms :   68 ( 350 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_59,plain,(
    ! [A_22] :
      ( u1_struct_0(A_22) = k2_struct_0(A_22)
      | ~ l1_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_23] :
      ( u1_struct_0(A_23) = k2_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_14,c_59])).

tff(c_68,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_64])).

tff(c_40,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_69,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_70,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_32])).

tff(c_98,plain,(
    ! [B_26,A_27] :
      ( v3_pre_topc(B_26,A_27)
      | ~ r2_hidden(B_26,u1_pre_topc(A_27))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_101,plain,(
    ! [B_26] :
      ( v3_pre_topc(B_26,'#skF_1')
      | ~ r2_hidden(B_26,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_98])).

tff(c_109,plain,(
    ! [B_28] :
      ( v3_pre_topc(B_28,'#skF_1')
      | ~ r2_hidden(B_28,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_101])).

tff(c_112,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_109])).

tff(c_119,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_112])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_775,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(B_59,u1_pre_topc(A_60))
      | k5_tmap_1(A_60,B_59) != u1_pre_topc(A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_784,plain,(
    ! [B_59] :
      ( r2_hidden(B_59,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_59) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_775])).

tff(c_794,plain,(
    ! [B_59] :
      ( r2_hidden(B_59,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_59) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_784])).

tff(c_803,plain,(
    ! [B_61] :
      ( r2_hidden(B_61,u1_pre_topc('#skF_1'))
      | k5_tmap_1('#skF_1',B_61) != u1_pre_topc('#skF_1')
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_794])).

tff(c_806,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_803])).

tff(c_813,plain,(
    k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_806])).

tff(c_46,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_90,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46])).

tff(c_91,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_90])).

tff(c_16,plain,(
    ! [A_9] :
      ( v3_pre_topc(k2_struct_0(A_9),A_9)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_120,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_47,c_109])).

tff(c_121,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_128,plain,(
    ! [B_30,A_31] :
      ( r2_hidden(B_30,u1_pre_topc(A_31))
      | ~ v3_pre_topc(B_30,A_31)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_227,plain,(
    ! [A_35] :
      ( r2_hidden(u1_struct_0(A_35),u1_pre_topc(A_35))
      | ~ v3_pre_topc(u1_struct_0(A_35),A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_47,c_128])).

tff(c_239,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(u1_struct_0('#skF_1'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_227])).

tff(c_246,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_68,c_239])).

tff(c_247,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_246])).

tff(c_250,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_247])).

tff(c_254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_250])).

tff(c_256,plain,(
    r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_892,plain,(
    ! [A_63,B_64] :
      ( k5_tmap_1(A_63,B_64) = u1_pre_topc(A_63)
      | ~ r2_hidden(B_64,u1_pre_topc(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_904,plain,(
    ! [B_64] :
      ( k5_tmap_1('#skF_1',B_64) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_64,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_892])).

tff(c_914,plain,(
    ! [B_64] :
      ( k5_tmap_1('#skF_1',B_64) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_64,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_904])).

tff(c_921,plain,(
    ! [B_65] :
      ( k5_tmap_1('#skF_1',B_65) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_65,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_914])).

tff(c_928,plain,
    ( k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) = u1_pre_topc('#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_47,c_921])).

tff(c_933,plain,(
    k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_928])).

tff(c_326,plain,(
    ! [A_45,B_46] :
      ( l1_pre_topc(k6_tmap_1(A_45,B_46))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_329,plain,(
    ! [B_46] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_46))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_326])).

tff(c_335,plain,(
    ! [B_46] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_46))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_329])).

tff(c_350,plain,(
    ! [B_49] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_335])).

tff(c_359,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_47,c_350])).

tff(c_338,plain,(
    ! [A_47,B_48] :
      ( v1_pre_topc(k6_tmap_1(A_47,B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_341,plain,(
    ! [B_48] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_338])).

tff(c_347,plain,(
    ! [B_48] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_341])).

tff(c_368,plain,(
    ! [B_50] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_50))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_347])).

tff(c_377,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_47,c_368])).

tff(c_497,plain,(
    ! [A_52,B_53] :
      ( u1_struct_0(k6_tmap_1(A_52,B_53)) = u1_struct_0(A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_506,plain,(
    ! [B_53] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_53)) = u1_struct_0('#skF_1')
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_497])).

tff(c_516,plain,(
    ! [B_53] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_53)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_68,c_506])).

tff(c_536,plain,(
    ! [B_55] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_55)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_516])).

tff(c_545,plain,(
    u1_struct_0(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_47,c_536])).

tff(c_698,plain,(
    ! [A_56,B_57] :
      ( u1_pre_topc(k6_tmap_1(A_56,B_57)) = k5_tmap_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_707,plain,(
    ! [B_57] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_57)) = k5_tmap_1('#skF_1',B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_698])).

tff(c_717,plain,(
    ! [B_57] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_57)) = k5_tmap_1('#skF_1',B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_707])).

tff(c_722,plain,(
    ! [B_58] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_58)) = k5_tmap_1('#skF_1',B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_717])).

tff(c_731,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k5_tmap_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_47,c_722])).

tff(c_6,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_761,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))),k5_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))
    | ~ v1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_6])).

tff(c_769,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),k5_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = k6_tmap_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_377,c_545,c_761])).

tff(c_934,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_769])).

tff(c_937,plain,(
    k6_tmap_1('#skF_1',k2_struct_0('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_934])).

tff(c_936,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1',k2_struct_0('#skF_1'))) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_731])).

tff(c_962,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_937,c_936])).

tff(c_730,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_722])).

tff(c_981,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_962,c_730])).

tff(c_983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_813,c_981])).

tff(c_984,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_986,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_984])).

tff(c_985,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_987,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_32])).

tff(c_1020,plain,(
    ! [B_70,A_71] :
      ( r2_hidden(B_70,u1_pre_topc(A_71))
      | ~ v3_pre_topc(B_70,A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1023,plain,(
    ! [B_70] :
      ( r2_hidden(B_70,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_70,'#skF_1')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1020])).

tff(c_1093,plain,(
    ! [B_78] :
      ( r2_hidden(B_78,u1_pre_topc('#skF_1'))
      | ~ v3_pre_topc(B_78,'#skF_1')
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1023])).

tff(c_1096,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_987,c_1093])).

tff(c_1103,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_1096])).

tff(c_1578,plain,(
    ! [A_95,B_96] :
      ( k5_tmap_1(A_95,B_96) = u1_pre_topc(A_95)
      | ~ r2_hidden(B_96,u1_pre_topc(A_95))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1587,plain,(
    ! [B_96] :
      ( k5_tmap_1('#skF_1',B_96) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_96,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1578])).

tff(c_1597,plain,(
    ! [B_96] :
      ( k5_tmap_1('#skF_1',B_96) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_96,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1587])).

tff(c_1606,plain,(
    ! [B_97] :
      ( k5_tmap_1('#skF_1',B_97) = u1_pre_topc('#skF_1')
      | ~ r2_hidden(B_97,u1_pre_topc('#skF_1'))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1597])).

tff(c_1609,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_987,c_1606])).

tff(c_1616,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_1609])).

tff(c_1501,plain,(
    ! [A_92,B_93] :
      ( u1_pre_topc(k6_tmap_1(A_92,B_93)) = k5_tmap_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1510,plain,(
    ! [B_93] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_93)) = k5_tmap_1('#skF_1',B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1501])).

tff(c_1520,plain,(
    ! [B_93] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_93)) = k5_tmap_1('#skF_1',B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1510])).

tff(c_1525,plain,(
    ! [B_94] :
      ( u1_pre_topc(k6_tmap_1('#skF_1',B_94)) = k5_tmap_1('#skF_1',B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1520])).

tff(c_1533,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_987,c_1525])).

tff(c_1128,plain,(
    ! [A_81,B_82] :
      ( l1_pre_topc(k6_tmap_1(A_81,B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1131,plain,(
    ! [B_82] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1128])).

tff(c_1137,plain,(
    ! [B_82] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1131])).

tff(c_1140,plain,(
    ! [B_83] :
      ( l1_pre_topc(k6_tmap_1('#skF_1',B_83))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1137])).

tff(c_1148,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_987,c_1140])).

tff(c_1150,plain,(
    ! [A_84,B_85] :
      ( v1_pre_topc(k6_tmap_1(A_84,B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1153,plain,(
    ! [B_85] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1150])).

tff(c_1159,plain,(
    ! [B_85] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_85))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1153])).

tff(c_1219,plain,(
    ! [B_86] :
      ( v1_pre_topc(k6_tmap_1('#skF_1',B_86))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1159])).

tff(c_1227,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_987,c_1219])).

tff(c_1316,plain,(
    ! [A_89,B_90] :
      ( u1_struct_0(k6_tmap_1(A_89,B_90)) = u1_struct_0(A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1325,plain,(
    ! [B_90] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_90)) = u1_struct_0('#skF_1')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1316])).

tff(c_1335,plain,(
    ! [B_90] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_90)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_68,c_1325])).

tff(c_1338,plain,(
    ! [B_91] :
      ( u1_struct_0(k6_tmap_1('#skF_1',B_91)) = k2_struct_0('#skF_1')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1335])).

tff(c_1346,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_987,c_1338])).

tff(c_1385,plain,
    ( g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1346,c_6])).

tff(c_1411,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_1227,c_1385])).

tff(c_1535,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1533,c_1411])).

tff(c_1620,plain,(
    g1_pre_topc(k2_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_1535])).

tff(c_1624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_986,c_1620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.55  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.42/1.55  
% 3.42/1.55  %Foreground sorts:
% 3.42/1.55  
% 3.42/1.55  
% 3.42/1.55  %Background operators:
% 3.42/1.55  
% 3.42/1.55  
% 3.42/1.55  %Foreground operators:
% 3.42/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.42/1.55  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.42/1.55  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.55  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.42/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.42/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.55  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.42/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.55  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.42/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.42/1.55  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.42/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.42/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.42/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.42/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.55  
% 3.59/1.58  tff(f_116, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.59/1.58  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.59/1.58  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.59/1.58  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.59/1.58  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 3.59/1.58  tff(f_58, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.59/1.58  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.59/1.58  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.59/1.58  tff(f_73, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.59/1.58  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.59/1.58  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.59/1.58  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.59/1.58  tff(c_14, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.59/1.58  tff(c_59, plain, (![A_22]: (u1_struct_0(A_22)=k2_struct_0(A_22) | ~l1_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.59/1.58  tff(c_64, plain, (![A_23]: (u1_struct_0(A_23)=k2_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(resolution, [status(thm)], [c_14, c_59])).
% 3.59/1.58  tff(c_68, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_64])).
% 3.59/1.58  tff(c_40, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.59/1.58  tff(c_69, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 3.59/1.58  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.59/1.58  tff(c_70, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_32])).
% 3.59/1.58  tff(c_98, plain, (![B_26, A_27]: (v3_pre_topc(B_26, A_27) | ~r2_hidden(B_26, u1_pre_topc(A_27)) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.59/1.58  tff(c_101, plain, (![B_26]: (v3_pre_topc(B_26, '#skF_1') | ~r2_hidden(B_26, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_26, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_98])).
% 3.59/1.58  tff(c_109, plain, (![B_28]: (v3_pre_topc(B_28, '#skF_1') | ~r2_hidden(B_28, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_28, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_101])).
% 3.59/1.58  tff(c_112, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_109])).
% 3.59/1.58  tff(c_119, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_69, c_112])).
% 3.59/1.58  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.59/1.58  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.59/1.58  tff(c_775, plain, (![B_59, A_60]: (r2_hidden(B_59, u1_pre_topc(A_60)) | k5_tmap_1(A_60, B_59)!=u1_pre_topc(A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.59/1.58  tff(c_784, plain, (![B_59]: (r2_hidden(B_59, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_59)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_775])).
% 3.59/1.58  tff(c_794, plain, (![B_59]: (r2_hidden(B_59, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_59)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_59, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_784])).
% 3.59/1.58  tff(c_803, plain, (![B_61]: (r2_hidden(B_61, u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', B_61)!=u1_pre_topc('#skF_1') | ~m1_subset_1(B_61, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_794])).
% 3.59/1.58  tff(c_806, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_803])).
% 3.59/1.58  tff(c_813, plain, (k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_119, c_806])).
% 3.59/1.58  tff(c_46, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.59/1.58  tff(c_90, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46])).
% 3.59/1.58  tff(c_91, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_69, c_90])).
% 3.59/1.58  tff(c_16, plain, (![A_9]: (v3_pre_topc(k2_struct_0(A_9), A_9) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.59/1.58  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.59/1.58  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.59/1.58  tff(c_47, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.59/1.58  tff(c_120, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_47, c_109])).
% 3.59/1.58  tff(c_121, plain, (~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_120])).
% 3.59/1.58  tff(c_128, plain, (![B_30, A_31]: (r2_hidden(B_30, u1_pre_topc(A_31)) | ~v3_pre_topc(B_30, A_31) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.59/1.58  tff(c_227, plain, (![A_35]: (r2_hidden(u1_struct_0(A_35), u1_pre_topc(A_35)) | ~v3_pre_topc(u1_struct_0(A_35), A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_47, c_128])).
% 3.59/1.58  tff(c_239, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v3_pre_topc(u1_struct_0('#skF_1'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_68, c_227])).
% 3.59/1.58  tff(c_246, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_68, c_239])).
% 3.59/1.58  tff(c_247, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_121, c_246])).
% 3.59/1.58  tff(c_250, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_247])).
% 3.59/1.58  tff(c_254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_250])).
% 3.59/1.58  tff(c_256, plain, (r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_120])).
% 3.59/1.58  tff(c_892, plain, (![A_63, B_64]: (k5_tmap_1(A_63, B_64)=u1_pre_topc(A_63) | ~r2_hidden(B_64, u1_pre_topc(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.59/1.58  tff(c_904, plain, (![B_64]: (k5_tmap_1('#skF_1', B_64)=u1_pre_topc('#skF_1') | ~r2_hidden(B_64, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_892])).
% 3.59/1.58  tff(c_914, plain, (![B_64]: (k5_tmap_1('#skF_1', B_64)=u1_pre_topc('#skF_1') | ~r2_hidden(B_64, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_64, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_904])).
% 3.59/1.58  tff(c_921, plain, (![B_65]: (k5_tmap_1('#skF_1', B_65)=u1_pre_topc('#skF_1') | ~r2_hidden(B_65, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_65, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_914])).
% 3.59/1.58  tff(c_928, plain, (k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))=u1_pre_topc('#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_47, c_921])).
% 3.59/1.58  tff(c_933, plain, (k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_928])).
% 3.59/1.58  tff(c_326, plain, (![A_45, B_46]: (l1_pre_topc(k6_tmap_1(A_45, B_46)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.58  tff(c_329, plain, (![B_46]: (l1_pre_topc(k6_tmap_1('#skF_1', B_46)) | ~m1_subset_1(B_46, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_326])).
% 3.59/1.58  tff(c_335, plain, (![B_46]: (l1_pre_topc(k6_tmap_1('#skF_1', B_46)) | ~m1_subset_1(B_46, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_329])).
% 3.59/1.58  tff(c_350, plain, (![B_49]: (l1_pre_topc(k6_tmap_1('#skF_1', B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_335])).
% 3.59/1.58  tff(c_359, plain, (l1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_47, c_350])).
% 3.59/1.58  tff(c_338, plain, (![A_47, B_48]: (v1_pre_topc(k6_tmap_1(A_47, B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.58  tff(c_341, plain, (![B_48]: (v1_pre_topc(k6_tmap_1('#skF_1', B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_338])).
% 3.59/1.58  tff(c_347, plain, (![B_48]: (v1_pre_topc(k6_tmap_1('#skF_1', B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_341])).
% 3.59/1.58  tff(c_368, plain, (![B_50]: (v1_pre_topc(k6_tmap_1('#skF_1', B_50)) | ~m1_subset_1(B_50, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_347])).
% 3.59/1.58  tff(c_377, plain, (v1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_47, c_368])).
% 3.59/1.58  tff(c_497, plain, (![A_52, B_53]: (u1_struct_0(k6_tmap_1(A_52, B_53))=u1_struct_0(A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.59/1.58  tff(c_506, plain, (![B_53]: (u1_struct_0(k6_tmap_1('#skF_1', B_53))=u1_struct_0('#skF_1') | ~m1_subset_1(B_53, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_497])).
% 3.59/1.58  tff(c_516, plain, (![B_53]: (u1_struct_0(k6_tmap_1('#skF_1', B_53))=k2_struct_0('#skF_1') | ~m1_subset_1(B_53, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_68, c_506])).
% 3.59/1.58  tff(c_536, plain, (![B_55]: (u1_struct_0(k6_tmap_1('#skF_1', B_55))=k2_struct_0('#skF_1') | ~m1_subset_1(B_55, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_516])).
% 3.59/1.58  tff(c_545, plain, (u1_struct_0(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_47, c_536])).
% 3.59/1.58  tff(c_698, plain, (![A_56, B_57]: (u1_pre_topc(k6_tmap_1(A_56, B_57))=k5_tmap_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.59/1.58  tff(c_707, plain, (![B_57]: (u1_pre_topc(k6_tmap_1('#skF_1', B_57))=k5_tmap_1('#skF_1', B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_698])).
% 3.59/1.58  tff(c_717, plain, (![B_57]: (u1_pre_topc(k6_tmap_1('#skF_1', B_57))=k5_tmap_1('#skF_1', B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_707])).
% 3.59/1.58  tff(c_722, plain, (![B_58]: (u1_pre_topc(k6_tmap_1('#skF_1', B_58))=k5_tmap_1('#skF_1', B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_717])).
% 3.59/1.58  tff(c_731, plain, (u1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k5_tmap_1('#skF_1', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_47, c_722])).
% 3.59/1.58  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.59/1.58  tff(c_761, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))), k5_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k6_tmap_1('#skF_1', k2_struct_0('#skF_1')) | ~v1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))) | ~l1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_731, c_6])).
% 3.59/1.58  tff(c_769, plain, (g1_pre_topc(k2_struct_0('#skF_1'), k5_tmap_1('#skF_1', k2_struct_0('#skF_1')))=k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_359, c_377, c_545, c_761])).
% 3.59/1.58  tff(c_934, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_933, c_769])).
% 3.59/1.58  tff(c_937, plain, (k6_tmap_1('#skF_1', k2_struct_0('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_934])).
% 3.59/1.58  tff(c_936, plain, (u1_pre_topc(k6_tmap_1('#skF_1', k2_struct_0('#skF_1')))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_933, c_731])).
% 3.59/1.58  tff(c_962, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_937, c_936])).
% 3.59/1.58  tff(c_730, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_722])).
% 3.59/1.58  tff(c_981, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_962, c_730])).
% 3.59/1.58  tff(c_983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_813, c_981])).
% 3.59/1.58  tff(c_984, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 3.59/1.58  tff(c_986, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_984])).
% 3.59/1.58  tff(c_985, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 3.59/1.58  tff(c_987, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_32])).
% 3.59/1.58  tff(c_1020, plain, (![B_70, A_71]: (r2_hidden(B_70, u1_pre_topc(A_71)) | ~v3_pre_topc(B_70, A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.59/1.58  tff(c_1023, plain, (![B_70]: (r2_hidden(B_70, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_70, '#skF_1') | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1020])).
% 3.59/1.58  tff(c_1093, plain, (![B_78]: (r2_hidden(B_78, u1_pre_topc('#skF_1')) | ~v3_pre_topc(B_78, '#skF_1') | ~m1_subset_1(B_78, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1023])).
% 3.59/1.58  tff(c_1096, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_987, c_1093])).
% 3.59/1.58  tff(c_1103, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_1096])).
% 3.59/1.58  tff(c_1578, plain, (![A_95, B_96]: (k5_tmap_1(A_95, B_96)=u1_pre_topc(A_95) | ~r2_hidden(B_96, u1_pre_topc(A_95)) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.59/1.58  tff(c_1587, plain, (![B_96]: (k5_tmap_1('#skF_1', B_96)=u1_pre_topc('#skF_1') | ~r2_hidden(B_96, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1578])).
% 3.59/1.58  tff(c_1597, plain, (![B_96]: (k5_tmap_1('#skF_1', B_96)=u1_pre_topc('#skF_1') | ~r2_hidden(B_96, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_96, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1587])).
% 3.59/1.58  tff(c_1606, plain, (![B_97]: (k5_tmap_1('#skF_1', B_97)=u1_pre_topc('#skF_1') | ~r2_hidden(B_97, u1_pre_topc('#skF_1')) | ~m1_subset_1(B_97, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_1597])).
% 3.59/1.58  tff(c_1609, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_987, c_1606])).
% 3.59/1.58  tff(c_1616, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1103, c_1609])).
% 3.59/1.58  tff(c_1501, plain, (![A_92, B_93]: (u1_pre_topc(k6_tmap_1(A_92, B_93))=k5_tmap_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.59/1.58  tff(c_1510, plain, (![B_93]: (u1_pre_topc(k6_tmap_1('#skF_1', B_93))=k5_tmap_1('#skF_1', B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1501])).
% 3.59/1.58  tff(c_1520, plain, (![B_93]: (u1_pre_topc(k6_tmap_1('#skF_1', B_93))=k5_tmap_1('#skF_1', B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1510])).
% 3.59/1.58  tff(c_1525, plain, (![B_94]: (u1_pre_topc(k6_tmap_1('#skF_1', B_94))=k5_tmap_1('#skF_1', B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_1520])).
% 3.59/1.58  tff(c_1533, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_987, c_1525])).
% 3.59/1.58  tff(c_1128, plain, (![A_81, B_82]: (l1_pre_topc(k6_tmap_1(A_81, B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.58  tff(c_1131, plain, (![B_82]: (l1_pre_topc(k6_tmap_1('#skF_1', B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1128])).
% 3.59/1.58  tff(c_1137, plain, (![B_82]: (l1_pre_topc(k6_tmap_1('#skF_1', B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1131])).
% 3.59/1.58  tff(c_1140, plain, (![B_83]: (l1_pre_topc(k6_tmap_1('#skF_1', B_83)) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_1137])).
% 3.59/1.58  tff(c_1148, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_987, c_1140])).
% 3.59/1.58  tff(c_1150, plain, (![A_84, B_85]: (v1_pre_topc(k6_tmap_1(A_84, B_85)) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.59/1.58  tff(c_1153, plain, (![B_85]: (v1_pre_topc(k6_tmap_1('#skF_1', B_85)) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1150])).
% 3.59/1.58  tff(c_1159, plain, (![B_85]: (v1_pre_topc(k6_tmap_1('#skF_1', B_85)) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1153])).
% 3.59/1.58  tff(c_1219, plain, (![B_86]: (v1_pre_topc(k6_tmap_1('#skF_1', B_86)) | ~m1_subset_1(B_86, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_1159])).
% 3.59/1.58  tff(c_1227, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_987, c_1219])).
% 3.59/1.58  tff(c_1316, plain, (![A_89, B_90]: (u1_struct_0(k6_tmap_1(A_89, B_90))=u1_struct_0(A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.59/1.58  tff(c_1325, plain, (![B_90]: (u1_struct_0(k6_tmap_1('#skF_1', B_90))=u1_struct_0('#skF_1') | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1316])).
% 3.59/1.58  tff(c_1335, plain, (![B_90]: (u1_struct_0(k6_tmap_1('#skF_1', B_90))=k2_struct_0('#skF_1') | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_1'))) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_68, c_1325])).
% 3.59/1.58  tff(c_1338, plain, (![B_91]: (u1_struct_0(k6_tmap_1('#skF_1', B_91))=k2_struct_0('#skF_1') | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_1335])).
% 3.59/1.58  tff(c_1346, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_987, c_1338])).
% 3.59/1.58  tff(c_1385, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1346, c_6])).
% 3.59/1.58  tff(c_1411, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1148, c_1227, c_1385])).
% 3.59/1.58  tff(c_1535, plain, (g1_pre_topc(k2_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1533, c_1411])).
% 3.59/1.58  tff(c_1620, plain, (g1_pre_topc(k2_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_1535])).
% 3.59/1.58  tff(c_1624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_986, c_1620])).
% 3.59/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.58  
% 3.59/1.58  Inference rules
% 3.59/1.58  ----------------------
% 3.59/1.58  #Ref     : 0
% 3.59/1.58  #Sup     : 330
% 3.59/1.58  #Fact    : 0
% 3.59/1.58  #Define  : 0
% 3.59/1.58  #Split   : 8
% 3.59/1.58  #Chain   : 0
% 3.59/1.58  #Close   : 0
% 3.59/1.58  
% 3.59/1.58  Ordering : KBO
% 3.59/1.58  
% 3.59/1.58  Simplification rules
% 3.59/1.58  ----------------------
% 3.59/1.58  #Subsume      : 3
% 3.59/1.58  #Demod        : 459
% 3.59/1.58  #Tautology    : 118
% 3.59/1.58  #SimpNegUnit  : 30
% 3.59/1.58  #BackRed      : 24
% 3.59/1.58  
% 3.59/1.58  #Partial instantiations: 0
% 3.59/1.58  #Strategies tried      : 1
% 3.59/1.58  
% 3.59/1.58  Timing (in seconds)
% 3.59/1.58  ----------------------
% 3.59/1.58  Preprocessing        : 0.30
% 3.59/1.58  Parsing              : 0.16
% 3.59/1.58  CNF conversion       : 0.02
% 3.59/1.58  Main loop            : 0.48
% 3.59/1.58  Inferencing          : 0.16
% 3.59/1.58  Reduction            : 0.18
% 3.59/1.58  Demodulation         : 0.12
% 3.59/1.58  BG Simplification    : 0.02
% 3.59/1.58  Subsumption          : 0.08
% 3.59/1.58  Abstraction          : 0.03
% 3.59/1.58  MUC search           : 0.00
% 3.59/1.58  Cooper               : 0.00
% 3.59/1.58  Total                : 0.84
% 3.59/1.58  Index Insertion      : 0.00
% 3.59/1.58  Index Deletion       : 0.00
% 3.59/1.58  Index Matching       : 0.00
% 3.59/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
