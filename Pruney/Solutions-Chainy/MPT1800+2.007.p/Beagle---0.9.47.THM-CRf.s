%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:58 EST 2020

% Result     : Theorem 10.09s
% Output     : CNFRefutation 10.31s
% Verified   : 
% Statistics : Number of formulae       :  219 (1322 expanded)
%              Number of leaves         :   40 ( 474 expanded)
%              Depth                    :   26
%              Number of atoms          :  615 (3956 expanded)
%              Number of equality atoms :  103 ( 741 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
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

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_130,axiom,(
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

tff(f_72,axiom,(
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

tff(f_159,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_152,axiom,(
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

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

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

tff(c_76,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3242,plain,(
    ! [A_151] :
      ( u1_struct_0(A_151) = k2_struct_0(A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_3246,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_3242])).

tff(c_3299,plain,(
    ! [B_168,A_169] :
      ( v3_pre_topc(B_168,A_169)
      | ~ r2_hidden(B_168,u1_pre_topc(A_169))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3308,plain,(
    ! [B_168] :
      ( v3_pre_topc(B_168,'#skF_2')
      | ~ r2_hidden(B_168,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_3299])).

tff(c_3318,plain,(
    ! [B_170] :
      ( v3_pre_topc(B_170,'#skF_2')
      | ~ r2_hidden(B_170,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3308])).

tff(c_3327,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_3318])).

tff(c_3328,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3327])).

tff(c_3340,plain,(
    ! [B_173,A_174] :
      ( r2_hidden(B_173,u1_pre_topc(A_174))
      | ~ v3_pre_topc(B_173,A_174)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3373,plain,(
    ! [A_177] :
      ( r2_hidden(u1_struct_0(A_177),u1_pre_topc(A_177))
      | ~ v3_pre_topc(u1_struct_0(A_177),A_177)
      | ~ l1_pre_topc(A_177) ) ),
    inference(resolution,[status(thm)],[c_76,c_3340])).

tff(c_3383,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(u1_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_3373])).

tff(c_3389,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3246,c_3383])).

tff(c_3390,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3328,c_3389])).

tff(c_3393,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_3390])).

tff(c_3397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3393])).

tff(c_3399,plain,(
    r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3327])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_5338,plain,(
    ! [A_255,B_256] :
      ( k5_tmap_1(A_255,B_256) = u1_pre_topc(A_255)
      | ~ r2_hidden(B_256,u1_pre_topc(A_255))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5371,plain,(
    ! [B_256] :
      ( k5_tmap_1('#skF_2',B_256) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_256,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_5338])).

tff(c_5383,plain,(
    ! [B_256] :
      ( k5_tmap_1('#skF_2',B_256) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_256,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_5371])).

tff(c_5386,plain,(
    ! [B_257] :
      ( k5_tmap_1('#skF_2',B_257) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_257,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5383])).

tff(c_5399,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_5386])).

tff(c_5405,plain,(
    k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3399,c_5399])).

tff(c_3566,plain,(
    ! [A_197,B_198] :
      ( l1_pre_topc(k6_tmap_1(A_197,B_198))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3575,plain,(
    ! [B_198] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_198))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_3566])).

tff(c_3583,plain,(
    ! [B_198] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_198))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3575])).

tff(c_3586,plain,(
    ! [B_199] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_199))
      | ~ m1_subset_1(B_199,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3583])).

tff(c_3595,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_76,c_3586])).

tff(c_3813,plain,(
    ! [A_207,B_208] :
      ( v1_pre_topc(k6_tmap_1(A_207,B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3828,plain,(
    ! [B_208] :
      ( v1_pre_topc(k6_tmap_1('#skF_2',B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_3813])).

tff(c_3838,plain,(
    ! [B_208] :
      ( v1_pre_topc(k6_tmap_1('#skF_2',B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3828])).

tff(c_3841,plain,(
    ! [B_209] :
      ( v1_pre_topc(k6_tmap_1('#skF_2',B_209))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3838])).

tff(c_3850,plain,(
    v1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_76,c_3841])).

tff(c_3956,plain,(
    ! [A_222,B_223] :
      ( u1_struct_0(k6_tmap_1(A_222,B_223)) = u1_struct_0(A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3974,plain,(
    ! [B_223] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_223)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_3956])).

tff(c_3985,plain,(
    ! [B_223] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_223)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_3246,c_3974])).

tff(c_3988,plain,(
    ! [B_224] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_224)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_224,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3985])).

tff(c_4001,plain,(
    u1_struct_0(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_3988])).

tff(c_4859,plain,(
    ! [A_242,B_243] :
      ( u1_pre_topc(k6_tmap_1(A_242,B_243)) = k5_tmap_1(A_242,B_243)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242)
      | ~ v2_pre_topc(A_242)
      | v2_struct_0(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_4892,plain,(
    ! [B_243] :
      ( u1_pre_topc(k6_tmap_1('#skF_2',B_243)) = k5_tmap_1('#skF_2',B_243)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_4859])).

tff(c_4904,plain,(
    ! [B_243] :
      ( u1_pre_topc(k6_tmap_1('#skF_2',B_243)) = k5_tmap_1('#skF_2',B_243)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_4892])).

tff(c_4907,plain,(
    ! [B_244] :
      ( u1_pre_topc(k6_tmap_1('#skF_2',B_244)) = k5_tmap_1('#skF_2',B_244)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4904])).

tff(c_4924,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_4907])).

tff(c_6,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4948,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))),k5_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
    | ~ v1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4924,c_6])).

tff(c_4964,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),k5_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3595,c_3850,c_4001,c_4948])).

tff(c_5406,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5405,c_4964])).

tff(c_94,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_98,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_94])).

tff(c_72,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_93,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_104,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_93])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_62,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_75,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62])).

tff(c_124,plain,(
    ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_98,c_75])).

tff(c_148,plain,(
    ! [B_56,A_57] :
      ( u1_struct_0(B_56) = '#skF_1'(A_57,B_56)
      | v1_tsep_1(B_56,A_57)
      | ~ m1_pre_topc(B_56,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_151,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_148,c_124])).

tff(c_154,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_151])).

tff(c_126,plain,(
    ! [B_48,A_49] :
      ( m1_subset_1(u1_struct_0(B_48),k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_pre_topc(B_48,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_132,plain,(
    ! [B_48] :
      ( m1_subset_1(u1_struct_0(B_48),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_48,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_126])).

tff(c_134,plain,(
    ! [B_48] :
      ( m1_subset_1(u1_struct_0(B_48),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_48,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_132])).

tff(c_158,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_134])).

tff(c_174,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_158])).

tff(c_229,plain,(
    ! [B_66,A_67] :
      ( r2_hidden(B_66,u1_pre_topc(A_67))
      | ~ v3_pre_topc(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_244,plain,(
    ! [B_66] :
      ( r2_hidden(B_66,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_66,'#skF_2')
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_229])).

tff(c_308,plain,(
    ! [B_71] :
      ( r2_hidden(B_71,u1_pre_topc('#skF_2'))
      | ~ v3_pre_topc(B_71,'#skF_2')
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_244])).

tff(c_319,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_174,c_308])).

tff(c_387,plain,(
    ~ v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_193,plain,(
    ! [B_63,A_64] :
      ( v3_pre_topc(B_63,A_64)
      | ~ r2_hidden(B_63,u1_pre_topc(A_64))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_208,plain,(
    ! [B_63] :
      ( v3_pre_topc(B_63,'#skF_2')
      | ~ r2_hidden(B_63,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_193])).

tff(c_388,plain,(
    ! [B_77] :
      ( v3_pre_topc(B_77,'#skF_2')
      | ~ r2_hidden(B_77,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_208])).

tff(c_391,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_174,c_388])).

tff(c_401,plain,(
    ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_391])).

tff(c_2254,plain,(
    ! [B_134,A_135] :
      ( r2_hidden(B_134,u1_pre_topc(A_135))
      | k5_tmap_1(A_135,B_134) != u1_pre_topc(A_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2290,plain,(
    ! [B_134] :
      ( r2_hidden(B_134,u1_pre_topc('#skF_2'))
      | k5_tmap_1('#skF_2',B_134) != u1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2254])).

tff(c_2305,plain,(
    ! [B_134] :
      ( r2_hidden(B_134,u1_pre_topc('#skF_2'))
      | k5_tmap_1('#skF_2',B_134) != u1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2290])).

tff(c_2368,plain,(
    ! [B_139] :
      ( r2_hidden(B_139,u1_pre_topc('#skF_2'))
      | k5_tmap_1('#skF_2',B_139) != u1_pre_topc('#skF_2')
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2305])).

tff(c_2380,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc('#skF_2'))
    | k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != u1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_174,c_2368])).

tff(c_2393,plain,(
    k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_2380])).

tff(c_539,plain,(
    ! [A_89,B_90] :
      ( l1_pre_topc(k6_tmap_1(A_89,B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_554,plain,(
    ! [B_90] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_539])).

tff(c_564,plain,(
    ! [B_90] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_554])).

tff(c_567,plain,(
    ! [B_91] :
      ( l1_pre_topc(k6_tmap_1('#skF_2',B_91))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_564])).

tff(c_580,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_76,c_567])).

tff(c_406,plain,(
    ! [A_78,B_79] :
      ( v1_pre_topc(k6_tmap_1(A_78,B_79))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_421,plain,(
    ! [B_79] :
      ( v1_pre_topc(k6_tmap_1('#skF_2',B_79))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_406])).

tff(c_431,plain,(
    ! [B_79] :
      ( v1_pre_topc(k6_tmap_1('#skF_2',B_79))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_421])).

tff(c_434,plain,(
    ! [B_80] :
      ( v1_pre_topc(k6_tmap_1('#skF_2',B_80))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_431])).

tff(c_447,plain,(
    v1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_76,c_434])).

tff(c_1070,plain,(
    ! [A_110,B_111] :
      ( u1_struct_0(k6_tmap_1(A_110,B_111)) = u1_struct_0(A_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1097,plain,(
    ! [B_111] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_111)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_1070])).

tff(c_1113,plain,(
    ! [B_111] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_111)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_111,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_98,c_1097])).

tff(c_1116,plain,(
    ! [B_112] :
      ( u1_struct_0(k6_tmap_1('#skF_2',B_112)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1113])).

tff(c_1133,plain,(
    u1_struct_0(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1116])).

tff(c_219,plain,(
    ! [A_65] :
      ( v3_pre_topc(u1_struct_0(A_65),A_65)
      | ~ r2_hidden(u1_struct_0(A_65),u1_pre_topc(A_65))
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_76,c_193])).

tff(c_225,plain,
    ( v3_pre_topc(u1_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_219])).

tff(c_228,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_98,c_225])).

tff(c_255,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_256,plain,(
    ! [A_68] :
      ( r2_hidden(u1_struct_0(A_68),u1_pre_topc(A_68))
      | ~ v3_pre_topc(u1_struct_0(A_68),A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_76,c_229])).

tff(c_265,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(u1_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_256])).

tff(c_269,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_98,c_265])).

tff(c_270,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_269])).

tff(c_287,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_270])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_287])).

tff(c_293,plain,(
    r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_2426,plain,(
    ! [A_142,B_143] :
      ( k5_tmap_1(A_142,B_143) = u1_pre_topc(A_142)
      | ~ r2_hidden(B_143,u1_pre_topc(A_142))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2462,plain,(
    ! [B_143] :
      ( k5_tmap_1('#skF_2',B_143) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_143,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2426])).

tff(c_2477,plain,(
    ! [B_143] :
      ( k5_tmap_1('#skF_2',B_143) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_143,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2462])).

tff(c_2480,plain,(
    ! [B_144] :
      ( k5_tmap_1('#skF_2',B_144) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(B_144,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2477])).

tff(c_2499,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_2480])).

tff(c_2508,plain,(
    k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_2499])).

tff(c_2046,plain,(
    ! [A_130,B_131] :
      ( u1_pre_topc(k6_tmap_1(A_130,B_131)) = k5_tmap_1(A_130,B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2082,plain,(
    ! [B_131] :
      ( u1_pre_topc(k6_tmap_1('#skF_2',B_131)) = k5_tmap_1('#skF_2',B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2046])).

tff(c_2097,plain,(
    ! [B_131] :
      ( u1_pre_topc(k6_tmap_1('#skF_2',B_131)) = k5_tmap_1('#skF_2',B_131)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2082])).

tff(c_2100,plain,(
    ! [B_132] :
      ( u1_pre_topc(k6_tmap_1('#skF_2',B_132)) = k5_tmap_1('#skF_2',B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2097])).

tff(c_2121,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_2100])).

tff(c_2511,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2508,c_2121])).

tff(c_2539,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
    | ~ v1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2')))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2511,c_6])).

tff(c_2555,plain,(
    k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_447,c_104,c_1133,c_2539])).

tff(c_2712,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2555,c_2511])).

tff(c_2751,plain,(
    ! [A_146,B_147] :
      ( k5_tmap_1(A_146,u1_struct_0(B_147)) = u1_pre_topc(k8_tmap_1(A_146,B_147))
      | ~ m1_subset_1(u1_struct_0(B_147),k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ m1_pre_topc(B_147,A_146)
      | v2_struct_0(B_147)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2802,plain,(
    ! [B_147] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_147)) = u1_pre_topc(k8_tmap_1('#skF_2',B_147))
      | ~ m1_subset_1(u1_struct_0(B_147),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_147,'#skF_2')
      | v2_struct_0(B_147)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2751])).

tff(c_2817,plain,(
    ! [B_147] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_147)) = u1_pre_topc(k8_tmap_1('#skF_2',B_147))
      | ~ m1_subset_1(u1_struct_0(B_147),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_147,'#skF_2')
      | v2_struct_0(B_147)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_2802])).

tff(c_3183,plain,(
    ! [B_150] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_150)) = u1_pre_topc(k8_tmap_1('#skF_2',B_150))
      | ~ m1_subset_1(u1_struct_0(B_150),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_150,'#skF_2')
      | v2_struct_0(B_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2817])).

tff(c_3210,plain,
    ( k5_tmap_1('#skF_2',u1_struct_0('#skF_3')) = u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_3183])).

tff(c_3227,plain,
    ( k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) = u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_174,c_2712,c_154,c_3210])).

tff(c_3229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2393,c_3227])).

tff(c_3231,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_20,plain,(
    ! [A_10,B_16] :
      ( ~ v3_pre_topc('#skF_1'(A_10,B_16),A_10)
      | v1_tsep_1(B_16,A_10)
      | ~ m1_pre_topc(B_16,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3234,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3231,c_20])).

tff(c_3237,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_3234])).

tff(c_3239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_3237])).

tff(c_3241,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_3252,plain,(
    g1_pre_topc(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3246,c_3241])).

tff(c_5509,plain,(
    k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5406,c_3252])).

tff(c_3240,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( l1_pre_topc(k8_tmap_1(A_22,B_23))
      | ~ m1_pre_topc(B_23,A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( v1_pre_topc(k8_tmap_1(A_22,B_23))
      | ~ m1_pre_topc(B_23,A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_50,plain,(
    ! [B_39,A_37] :
      ( m1_subset_1(u1_struct_0(B_39),k1_zfmisc_1(u1_struct_0(A_37)))
      | ~ m1_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_5590,plain,(
    ! [A_261,B_262] :
      ( k5_tmap_1(A_261,u1_struct_0(B_262)) = u1_pre_topc(k8_tmap_1(A_261,B_262))
      | ~ m1_subset_1(u1_struct_0(B_262),k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ m1_pre_topc(B_262,A_261)
      | v2_struct_0(B_262)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_8299,plain,(
    ! [A_327,B_328] :
      ( k5_tmap_1(A_327,u1_struct_0(B_328)) = u1_pre_topc(k8_tmap_1(A_327,B_328))
      | v2_struct_0(B_328)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327)
      | ~ m1_pre_topc(B_328,A_327)
      | ~ l1_pre_topc(A_327) ) ),
    inference(resolution,[status(thm)],[c_50,c_5590])).

tff(c_4604,plain,(
    ! [B_235,A_236] :
      ( v3_pre_topc(u1_struct_0(B_235),A_236)
      | ~ m1_subset_1(u1_struct_0(B_235),k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ v1_tsep_1(B_235,A_236)
      | ~ m1_pre_topc(B_235,A_236)
      | ~ l1_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4651,plain,(
    ! [B_39,A_37] :
      ( v3_pre_topc(u1_struct_0(B_39),A_37)
      | ~ v1_tsep_1(B_39,A_37)
      | ~ m1_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_50,c_4604])).

tff(c_3419,plain,(
    ! [B_181,A_182] :
      ( r2_hidden(B_181,u1_pre_topc(A_182))
      | ~ v3_pre_topc(B_181,A_182)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3434,plain,(
    ! [B_39,A_37] :
      ( r2_hidden(u1_struct_0(B_39),u1_pre_topc(A_37))
      | ~ v3_pre_topc(u1_struct_0(B_39),A_37)
      | ~ m1_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_50,c_3419])).

tff(c_3270,plain,(
    ! [B_154,A_155] :
      ( m1_subset_1(u1_struct_0(B_154),k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ m1_pre_topc(B_154,A_155)
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_3276,plain,(
    ! [B_154] :
      ( m1_subset_1(u1_struct_0(B_154),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_154,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3246,c_3270])).

tff(c_3278,plain,(
    ! [B_154] :
      ( m1_subset_1(u1_struct_0(B_154),k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_154,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3276])).

tff(c_5453,plain,(
    ! [B_258] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_258)) = u1_pre_topc('#skF_2')
      | ~ r2_hidden(u1_struct_0(B_258),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc(B_258,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3278,c_5386])).

tff(c_5481,plain,(
    ! [B_39] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_39)) = u1_pre_topc('#skF_2')
      | ~ v3_pre_topc(u1_struct_0(B_39),'#skF_2')
      | ~ m1_pre_topc(B_39,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3434,c_5453])).

tff(c_5515,plain,(
    ! [B_259] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_259)) = u1_pre_topc('#skF_2')
      | ~ v3_pre_topc(u1_struct_0(B_259),'#skF_2')
      | ~ m1_pre_topc(B_259,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_5481])).

tff(c_5525,plain,(
    ! [B_39] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_39)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_39,'#skF_2')
      | ~ m1_pre_topc(B_39,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4651,c_5515])).

tff(c_5549,plain,(
    ! [B_39] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_39)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_39,'#skF_2')
      | ~ m1_pre_topc(B_39,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_5525])).

tff(c_8321,plain,(
    ! [B_328] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_328)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_328,'#skF_2')
      | ~ m1_pre_topc(B_328,'#skF_2')
      | v2_struct_0(B_328)
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_328,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8299,c_5549])).

tff(c_8383,plain,(
    ! [B_328] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_328)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_328,'#skF_2')
      | v2_struct_0(B_328)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_328,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_8321])).

tff(c_8384,plain,(
    ! [B_328] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_328)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_328,'#skF_2')
      | v2_struct_0(B_328)
      | ~ m1_pre_topc(B_328,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_8383])).

tff(c_4314,plain,(
    ! [A_229,B_230] :
      ( u1_struct_0(k8_tmap_1(A_229,B_230)) = u1_struct_0(A_229)
      | ~ m1_pre_topc(B_230,A_229)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_12642,plain,(
    ! [A_411,B_412] :
      ( g1_pre_topc(u1_struct_0(A_411),u1_pre_topc(k8_tmap_1(A_411,B_412))) = k8_tmap_1(A_411,B_412)
      | ~ v1_pre_topc(k8_tmap_1(A_411,B_412))
      | ~ l1_pre_topc(k8_tmap_1(A_411,B_412))
      | ~ m1_pre_topc(B_412,A_411)
      | v2_struct_0(B_412)
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4314,c_6])).

tff(c_12669,plain,(
    ! [B_328] :
      ( k8_tmap_1('#skF_2',B_328) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_328))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_328))
      | ~ m1_pre_topc(B_328,'#skF_2')
      | v2_struct_0(B_328)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_328,'#skF_2')
      | v2_struct_0(B_328)
      | ~ m1_pre_topc(B_328,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8384,c_12642])).

tff(c_12709,plain,(
    ! [B_328] :
      ( k8_tmap_1('#skF_2',B_328) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_328))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_328))
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_328,'#skF_2')
      | v2_struct_0(B_328)
      | ~ m1_pre_topc(B_328,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_5406,c_3246,c_12669])).

tff(c_13147,plain,(
    ! [B_442] :
      ( k8_tmap_1('#skF_2',B_442) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_442))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_442))
      | ~ v1_tsep_1(B_442,'#skF_2')
      | v2_struct_0(B_442)
      | ~ m1_pre_topc(B_442,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_12709])).

tff(c_13151,plain,(
    ! [B_23] :
      ( k8_tmap_1('#skF_2',B_23) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_23))
      | ~ v1_tsep_1(B_23,'#skF_2')
      | v2_struct_0(B_23)
      | ~ m1_pre_topc(B_23,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_13147])).

tff(c_13154,plain,(
    ! [B_23] :
      ( k8_tmap_1('#skF_2',B_23) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_23))
      | ~ v1_tsep_1(B_23,'#skF_2')
      | v2_struct_0(B_23)
      | ~ m1_pre_topc(B_23,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_13151])).

tff(c_13156,plain,(
    ! [B_443] :
      ( k8_tmap_1('#skF_2',B_443) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_443))
      | ~ v1_tsep_1(B_443,'#skF_2')
      | v2_struct_0(B_443)
      | ~ m1_pre_topc(B_443,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13154])).

tff(c_13160,plain,(
    ! [B_23] :
      ( k8_tmap_1('#skF_2',B_23) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ v1_tsep_1(B_23,'#skF_2')
      | v2_struct_0(B_23)
      | ~ m1_pre_topc(B_23,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_13156])).

tff(c_13163,plain,(
    ! [B_23] :
      ( k8_tmap_1('#skF_2',B_23) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ v1_tsep_1(B_23,'#skF_2')
      | v2_struct_0(B_23)
      | ~ m1_pre_topc(B_23,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_13160])).

tff(c_13165,plain,(
    ! [B_444] :
      ( k8_tmap_1('#skF_2',B_444) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ v1_tsep_1(B_444,'#skF_2')
      | v2_struct_0(B_444)
      | ~ m1_pre_topc(B_444,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13163])).

tff(c_13170,plain,
    ( k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3240,c_13165])).

tff(c_13176,plain,
    ( k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_13170])).

tff(c_13178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5509,c_13176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.09/3.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.09/3.61  
% 10.09/3.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.09/3.61  %$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 10.09/3.61  
% 10.09/3.61  %Foreground sorts:
% 10.09/3.61  
% 10.09/3.61  
% 10.09/3.61  %Background operators:
% 10.09/3.61  
% 10.09/3.61  
% 10.09/3.61  %Foreground operators:
% 10.09/3.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.09/3.61  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 10.09/3.61  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.09/3.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.09/3.61  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 10.09/3.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.09/3.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.09/3.61  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 10.09/3.61  tff('#skF_2', type, '#skF_2': $i).
% 10.09/3.61  tff('#skF_3', type, '#skF_3': $i).
% 10.09/3.61  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.09/3.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.09/3.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.09/3.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.09/3.61  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 10.09/3.61  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 10.09/3.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.09/3.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 10.09/3.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.09/3.61  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 10.09/3.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.09/3.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.09/3.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 10.09/3.61  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 10.09/3.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.09/3.61  
% 10.31/3.64  tff(f_179, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k8_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_tmap_1)).
% 10.31/3.64  tff(f_58, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 10.31/3.64  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 10.31/3.64  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 10.31/3.64  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.31/3.64  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 10.31/3.64  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 10.31/3.64  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 10.31/3.64  tff(f_87, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 10.31/3.64  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 10.31/3.64  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 10.31/3.64  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tsep_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tsep_1)).
% 10.31/3.64  tff(f_159, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 10.31/3.64  tff(f_152, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 10.31/3.64  tff(f_102, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 10.31/3.64  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 10.31/3.64  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 10.31/3.64  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 10.31/3.64  tff(c_16, plain, (![A_9]: (v3_pre_topc(k2_struct_0(A_9), A_9) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.31/3.64  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.31/3.64  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.31/3.64  tff(c_76, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 10.31/3.64  tff(c_14, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.31/3.64  tff(c_88, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.31/3.64  tff(c_3242, plain, (![A_151]: (u1_struct_0(A_151)=k2_struct_0(A_151) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_14, c_88])).
% 10.31/3.64  tff(c_3246, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_3242])).
% 10.31/3.64  tff(c_3299, plain, (![B_168, A_169]: (v3_pre_topc(B_168, A_169) | ~r2_hidden(B_168, u1_pre_topc(A_169)) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.31/3.64  tff(c_3308, plain, (![B_168]: (v3_pre_topc(B_168, '#skF_2') | ~r2_hidden(B_168, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_168, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3246, c_3299])).
% 10.31/3.64  tff(c_3318, plain, (![B_170]: (v3_pre_topc(B_170, '#skF_2') | ~r2_hidden(B_170, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_170, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3308])).
% 10.31/3.64  tff(c_3327, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_3318])).
% 10.31/3.64  tff(c_3328, plain, (~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_3327])).
% 10.31/3.64  tff(c_3340, plain, (![B_173, A_174]: (r2_hidden(B_173, u1_pre_topc(A_174)) | ~v3_pre_topc(B_173, A_174) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.31/3.64  tff(c_3373, plain, (![A_177]: (r2_hidden(u1_struct_0(A_177), u1_pre_topc(A_177)) | ~v3_pre_topc(u1_struct_0(A_177), A_177) | ~l1_pre_topc(A_177))), inference(resolution, [status(thm)], [c_76, c_3340])).
% 10.31/3.64  tff(c_3383, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(u1_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3246, c_3373])).
% 10.31/3.64  tff(c_3389, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3246, c_3383])).
% 10.31/3.64  tff(c_3390, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3328, c_3389])).
% 10.31/3.64  tff(c_3393, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_3390])).
% 10.31/3.64  tff(c_3397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3393])).
% 10.31/3.64  tff(c_3399, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_3327])).
% 10.31/3.64  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 10.31/3.64  tff(c_5338, plain, (![A_255, B_256]: (k5_tmap_1(A_255, B_256)=u1_pre_topc(A_255) | ~r2_hidden(B_256, u1_pre_topc(A_255)) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.31/3.64  tff(c_5371, plain, (![B_256]: (k5_tmap_1('#skF_2', B_256)=u1_pre_topc('#skF_2') | ~r2_hidden(B_256, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_256, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3246, c_5338])).
% 10.31/3.64  tff(c_5383, plain, (![B_256]: (k5_tmap_1('#skF_2', B_256)=u1_pre_topc('#skF_2') | ~r2_hidden(B_256, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_256, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_5371])).
% 10.31/3.64  tff(c_5386, plain, (![B_257]: (k5_tmap_1('#skF_2', B_257)=u1_pre_topc('#skF_2') | ~r2_hidden(B_257, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_257, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_5383])).
% 10.31/3.64  tff(c_5399, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_5386])).
% 10.31/3.64  tff(c_5405, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3399, c_5399])).
% 10.31/3.64  tff(c_3566, plain, (![A_197, B_198]: (l1_pre_topc(k6_tmap_1(A_197, B_198)) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.31/3.64  tff(c_3575, plain, (![B_198]: (l1_pre_topc(k6_tmap_1('#skF_2', B_198)) | ~m1_subset_1(B_198, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3246, c_3566])).
% 10.31/3.64  tff(c_3583, plain, (![B_198]: (l1_pre_topc(k6_tmap_1('#skF_2', B_198)) | ~m1_subset_1(B_198, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3575])).
% 10.31/3.64  tff(c_3586, plain, (![B_199]: (l1_pre_topc(k6_tmap_1('#skF_2', B_199)) | ~m1_subset_1(B_199, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_3583])).
% 10.31/3.64  tff(c_3595, plain, (l1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_76, c_3586])).
% 10.31/3.64  tff(c_3813, plain, (![A_207, B_208]: (v1_pre_topc(k6_tmap_1(A_207, B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207) | v2_struct_0(A_207))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.31/3.64  tff(c_3828, plain, (![B_208]: (v1_pre_topc(k6_tmap_1('#skF_2', B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3246, c_3813])).
% 10.31/3.64  tff(c_3838, plain, (![B_208]: (v1_pre_topc(k6_tmap_1('#skF_2', B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3828])).
% 10.31/3.64  tff(c_3841, plain, (![B_209]: (v1_pre_topc(k6_tmap_1('#skF_2', B_209)) | ~m1_subset_1(B_209, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_3838])).
% 10.31/3.64  tff(c_3850, plain, (v1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_76, c_3841])).
% 10.31/3.64  tff(c_3956, plain, (![A_222, B_223]: (u1_struct_0(k6_tmap_1(A_222, B_223))=u1_struct_0(A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.31/3.64  tff(c_3974, plain, (![B_223]: (u1_struct_0(k6_tmap_1('#skF_2', B_223))=u1_struct_0('#skF_2') | ~m1_subset_1(B_223, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3246, c_3956])).
% 10.31/3.64  tff(c_3985, plain, (![B_223]: (u1_struct_0(k6_tmap_1('#skF_2', B_223))=k2_struct_0('#skF_2') | ~m1_subset_1(B_223, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_3246, c_3974])).
% 10.31/3.64  tff(c_3988, plain, (![B_224]: (u1_struct_0(k6_tmap_1('#skF_2', B_224))=k2_struct_0('#skF_2') | ~m1_subset_1(B_224, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_3985])).
% 10.31/3.64  tff(c_4001, plain, (u1_struct_0(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_3988])).
% 10.31/3.64  tff(c_4859, plain, (![A_242, B_243]: (u1_pre_topc(k6_tmap_1(A_242, B_243))=k5_tmap_1(A_242, B_243) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242) | ~v2_pre_topc(A_242) | v2_struct_0(A_242))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.31/3.64  tff(c_4892, plain, (![B_243]: (u1_pre_topc(k6_tmap_1('#skF_2', B_243))=k5_tmap_1('#skF_2', B_243) | ~m1_subset_1(B_243, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3246, c_4859])).
% 10.31/3.64  tff(c_4904, plain, (![B_243]: (u1_pre_topc(k6_tmap_1('#skF_2', B_243))=k5_tmap_1('#skF_2', B_243) | ~m1_subset_1(B_243, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_4892])).
% 10.31/3.64  tff(c_4907, plain, (![B_244]: (u1_pre_topc(k6_tmap_1('#skF_2', B_244))=k5_tmap_1('#skF_2', B_244) | ~m1_subset_1(B_244, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_4904])).
% 10.31/3.64  tff(c_4924, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))=k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_4907])).
% 10.31/3.64  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.31/3.64  tff(c_4948, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))), k5_tmap_1('#skF_2', k2_struct_0('#skF_2')))=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))) | ~l1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4924, c_6])).
% 10.31/3.64  tff(c_4964, plain, (g1_pre_topc(k2_struct_0('#skF_2'), k5_tmap_1('#skF_2', k2_struct_0('#skF_2')))=k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3595, c_3850, c_4001, c_4948])).
% 10.31/3.64  tff(c_5406, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5405, c_4964])).
% 10.31/3.64  tff(c_94, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_14, c_88])).
% 10.31/3.64  tff(c_98, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_94])).
% 10.31/3.64  tff(c_72, plain, (v1_tsep_1('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 10.31/3.64  tff(c_93, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_72])).
% 10.31/3.64  tff(c_104, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_93])).
% 10.31/3.64  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 10.31/3.64  tff(c_62, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_179])).
% 10.31/3.64  tff(c_75, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62])).
% 10.31/3.64  tff(c_124, plain, (~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_98, c_75])).
% 10.31/3.64  tff(c_148, plain, (![B_56, A_57]: (u1_struct_0(B_56)='#skF_1'(A_57, B_56) | v1_tsep_1(B_56, A_57) | ~m1_pre_topc(B_56, A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.31/3.64  tff(c_151, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_148, c_124])).
% 10.31/3.64  tff(c_154, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_151])).
% 10.31/3.64  tff(c_126, plain, (![B_48, A_49]: (m1_subset_1(u1_struct_0(B_48), k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_pre_topc(B_48, A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.31/3.64  tff(c_132, plain, (![B_48]: (m1_subset_1(u1_struct_0(B_48), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_48, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_126])).
% 10.31/3.64  tff(c_134, plain, (![B_48]: (m1_subset_1(u1_struct_0(B_48), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_48, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_132])).
% 10.31/3.64  tff(c_158, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_154, c_134])).
% 10.31/3.64  tff(c_174, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_158])).
% 10.31/3.64  tff(c_229, plain, (![B_66, A_67]: (r2_hidden(B_66, u1_pre_topc(A_67)) | ~v3_pre_topc(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.31/3.64  tff(c_244, plain, (![B_66]: (r2_hidden(B_66, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_66, '#skF_2') | ~m1_subset_1(B_66, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_229])).
% 10.31/3.64  tff(c_308, plain, (![B_71]: (r2_hidden(B_71, u1_pre_topc('#skF_2')) | ~v3_pre_topc(B_71, '#skF_2') | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_244])).
% 10.31/3.64  tff(c_319, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2')) | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_174, c_308])).
% 10.31/3.64  tff(c_387, plain, (~v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_319])).
% 10.31/3.64  tff(c_193, plain, (![B_63, A_64]: (v3_pre_topc(B_63, A_64) | ~r2_hidden(B_63, u1_pre_topc(A_64)) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.31/3.64  tff(c_208, plain, (![B_63]: (v3_pre_topc(B_63, '#skF_2') | ~r2_hidden(B_63, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_63, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_193])).
% 10.31/3.64  tff(c_388, plain, (![B_77]: (v3_pre_topc(B_77, '#skF_2') | ~r2_hidden(B_77, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_208])).
% 10.31/3.64  tff(c_391, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_174, c_388])).
% 10.31/3.64  tff(c_401, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_387, c_391])).
% 10.31/3.64  tff(c_2254, plain, (![B_134, A_135]: (r2_hidden(B_134, u1_pre_topc(A_135)) | k5_tmap_1(A_135, B_134)!=u1_pre_topc(A_135) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.31/3.64  tff(c_2290, plain, (![B_134]: (r2_hidden(B_134, u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', B_134)!=u1_pre_topc('#skF_2') | ~m1_subset_1(B_134, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_2254])).
% 10.31/3.64  tff(c_2305, plain, (![B_134]: (r2_hidden(B_134, u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', B_134)!=u1_pre_topc('#skF_2') | ~m1_subset_1(B_134, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2290])).
% 10.31/3.64  tff(c_2368, plain, (![B_139]: (r2_hidden(B_139, u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', B_139)!=u1_pre_topc('#skF_2') | ~m1_subset_1(B_139, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_2305])).
% 10.31/3.64  tff(c_2380, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc('#skF_2')) | k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_174, c_2368])).
% 10.31/3.64  tff(c_2393, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_401, c_2380])).
% 10.31/3.64  tff(c_539, plain, (![A_89, B_90]: (l1_pre_topc(k6_tmap_1(A_89, B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.31/3.64  tff(c_554, plain, (![B_90]: (l1_pre_topc(k6_tmap_1('#skF_2', B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_539])).
% 10.31/3.64  tff(c_564, plain, (![B_90]: (l1_pre_topc(k6_tmap_1('#skF_2', B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_554])).
% 10.31/3.64  tff(c_567, plain, (![B_91]: (l1_pre_topc(k6_tmap_1('#skF_2', B_91)) | ~m1_subset_1(B_91, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_564])).
% 10.31/3.64  tff(c_580, plain, (l1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_76, c_567])).
% 10.31/3.64  tff(c_406, plain, (![A_78, B_79]: (v1_pre_topc(k6_tmap_1(A_78, B_79)) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.31/3.64  tff(c_421, plain, (![B_79]: (v1_pre_topc(k6_tmap_1('#skF_2', B_79)) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_406])).
% 10.31/3.64  tff(c_431, plain, (![B_79]: (v1_pre_topc(k6_tmap_1('#skF_2', B_79)) | ~m1_subset_1(B_79, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_421])).
% 10.31/3.64  tff(c_434, plain, (![B_80]: (v1_pre_topc(k6_tmap_1('#skF_2', B_80)) | ~m1_subset_1(B_80, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_431])).
% 10.31/3.64  tff(c_447, plain, (v1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_76, c_434])).
% 10.31/3.64  tff(c_1070, plain, (![A_110, B_111]: (u1_struct_0(k6_tmap_1(A_110, B_111))=u1_struct_0(A_110) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.31/3.64  tff(c_1097, plain, (![B_111]: (u1_struct_0(k6_tmap_1('#skF_2', B_111))=u1_struct_0('#skF_2') | ~m1_subset_1(B_111, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_1070])).
% 10.31/3.64  tff(c_1113, plain, (![B_111]: (u1_struct_0(k6_tmap_1('#skF_2', B_111))=k2_struct_0('#skF_2') | ~m1_subset_1(B_111, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_98, c_1097])).
% 10.31/3.64  tff(c_1116, plain, (![B_112]: (u1_struct_0(k6_tmap_1('#skF_2', B_112))=k2_struct_0('#skF_2') | ~m1_subset_1(B_112, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_1113])).
% 10.31/3.64  tff(c_1133, plain, (u1_struct_0(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_1116])).
% 10.31/3.64  tff(c_219, plain, (![A_65]: (v3_pre_topc(u1_struct_0(A_65), A_65) | ~r2_hidden(u1_struct_0(A_65), u1_pre_topc(A_65)) | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_76, c_193])).
% 10.31/3.64  tff(c_225, plain, (v3_pre_topc(u1_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_98, c_219])).
% 10.31/3.64  tff(c_228, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_98, c_225])).
% 10.31/3.64  tff(c_255, plain, (~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_228])).
% 10.31/3.64  tff(c_256, plain, (![A_68]: (r2_hidden(u1_struct_0(A_68), u1_pre_topc(A_68)) | ~v3_pre_topc(u1_struct_0(A_68), A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_76, c_229])).
% 10.31/3.64  tff(c_265, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(u1_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_98, c_256])).
% 10.31/3.64  tff(c_269, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_98, c_265])).
% 10.31/3.64  tff(c_270, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_255, c_269])).
% 10.31/3.64  tff(c_287, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_270])).
% 10.31/3.64  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_287])).
% 10.31/3.64  tff(c_293, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_228])).
% 10.31/3.64  tff(c_2426, plain, (![A_142, B_143]: (k5_tmap_1(A_142, B_143)=u1_pre_topc(A_142) | ~r2_hidden(B_143, u1_pre_topc(A_142)) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.31/3.64  tff(c_2462, plain, (![B_143]: (k5_tmap_1('#skF_2', B_143)=u1_pre_topc('#skF_2') | ~r2_hidden(B_143, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_143, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_2426])).
% 10.31/3.64  tff(c_2477, plain, (![B_143]: (k5_tmap_1('#skF_2', B_143)=u1_pre_topc('#skF_2') | ~r2_hidden(B_143, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_143, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2462])).
% 10.31/3.64  tff(c_2480, plain, (![B_144]: (k5_tmap_1('#skF_2', B_144)=u1_pre_topc('#skF_2') | ~r2_hidden(B_144, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_144, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_2477])).
% 10.31/3.64  tff(c_2499, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_2480])).
% 10.31/3.64  tff(c_2508, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_2499])).
% 10.31/3.64  tff(c_2046, plain, (![A_130, B_131]: (u1_pre_topc(k6_tmap_1(A_130, B_131))=k5_tmap_1(A_130, B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.31/3.64  tff(c_2082, plain, (![B_131]: (u1_pre_topc(k6_tmap_1('#skF_2', B_131))=k5_tmap_1('#skF_2', B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_2046])).
% 10.31/3.64  tff(c_2097, plain, (![B_131]: (u1_pre_topc(k6_tmap_1('#skF_2', B_131))=k5_tmap_1('#skF_2', B_131) | ~m1_subset_1(B_131, k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2082])).
% 10.31/3.64  tff(c_2100, plain, (![B_132]: (u1_pre_topc(k6_tmap_1('#skF_2', B_132))=k5_tmap_1('#skF_2', B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_2097])).
% 10.31/3.64  tff(c_2121, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))=k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_2100])).
% 10.31/3.64  tff(c_2511, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2508, c_2121])).
% 10.31/3.64  tff(c_2539, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))) | ~l1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2511, c_6])).
% 10.31/3.64  tff(c_2555, plain, (k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_447, c_104, c_1133, c_2539])).
% 10.31/3.64  tff(c_2712, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2555, c_2511])).
% 10.31/3.64  tff(c_2751, plain, (![A_146, B_147]: (k5_tmap_1(A_146, u1_struct_0(B_147))=u1_pre_topc(k8_tmap_1(A_146, B_147)) | ~m1_subset_1(u1_struct_0(B_147), k1_zfmisc_1(u1_struct_0(A_146))) | ~m1_pre_topc(B_147, A_146) | v2_struct_0(B_147) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.31/3.64  tff(c_2802, plain, (![B_147]: (k5_tmap_1('#skF_2', u1_struct_0(B_147))=u1_pre_topc(k8_tmap_1('#skF_2', B_147)) | ~m1_subset_1(u1_struct_0(B_147), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_147, '#skF_2') | v2_struct_0(B_147) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_2751])).
% 10.31/3.64  tff(c_2817, plain, (![B_147]: (k5_tmap_1('#skF_2', u1_struct_0(B_147))=u1_pre_topc(k8_tmap_1('#skF_2', B_147)) | ~m1_subset_1(u1_struct_0(B_147), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_147, '#skF_2') | v2_struct_0(B_147) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_2802])).
% 10.31/3.64  tff(c_3183, plain, (![B_150]: (k5_tmap_1('#skF_2', u1_struct_0(B_150))=u1_pre_topc(k8_tmap_1('#skF_2', B_150)) | ~m1_subset_1(u1_struct_0(B_150), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_150, '#skF_2') | v2_struct_0(B_150))), inference(negUnitSimplification, [status(thm)], [c_60, c_2817])).
% 10.31/3.64  tff(c_3210, plain, (k5_tmap_1('#skF_2', u1_struct_0('#skF_3'))=u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_154, c_3183])).
% 10.31/3.64  tff(c_3227, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_174, c_2712, c_154, c_3210])).
% 10.31/3.64  tff(c_3229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2393, c_3227])).
% 10.31/3.64  tff(c_3231, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_319])).
% 10.31/3.64  tff(c_20, plain, (![A_10, B_16]: (~v3_pre_topc('#skF_1'(A_10, B_16), A_10) | v1_tsep_1(B_16, A_10) | ~m1_pre_topc(B_16, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.31/3.64  tff(c_3234, plain, (v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_3231, c_20])).
% 10.31/3.64  tff(c_3237, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_3234])).
% 10.31/3.64  tff(c_3239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_3237])).
% 10.31/3.64  tff(c_3241, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_72])).
% 10.31/3.64  tff(c_3252, plain, (g1_pre_topc(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3246, c_3241])).
% 10.31/3.64  tff(c_5509, plain, (k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5406, c_3252])).
% 10.31/3.64  tff(c_3240, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_72])).
% 10.31/3.64  tff(c_32, plain, (![A_22, B_23]: (l1_pre_topc(k8_tmap_1(A_22, B_23)) | ~m1_pre_topc(B_23, A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.31/3.64  tff(c_36, plain, (![A_22, B_23]: (v1_pre_topc(k8_tmap_1(A_22, B_23)) | ~m1_pre_topc(B_23, A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.31/3.64  tff(c_50, plain, (![B_39, A_37]: (m1_subset_1(u1_struct_0(B_39), k1_zfmisc_1(u1_struct_0(A_37))) | ~m1_pre_topc(B_39, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.31/3.64  tff(c_5590, plain, (![A_261, B_262]: (k5_tmap_1(A_261, u1_struct_0(B_262))=u1_pre_topc(k8_tmap_1(A_261, B_262)) | ~m1_subset_1(u1_struct_0(B_262), k1_zfmisc_1(u1_struct_0(A_261))) | ~m1_pre_topc(B_262, A_261) | v2_struct_0(B_262) | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.31/3.64  tff(c_8299, plain, (![A_327, B_328]: (k5_tmap_1(A_327, u1_struct_0(B_328))=u1_pre_topc(k8_tmap_1(A_327, B_328)) | v2_struct_0(B_328) | ~v2_pre_topc(A_327) | v2_struct_0(A_327) | ~m1_pre_topc(B_328, A_327) | ~l1_pre_topc(A_327))), inference(resolution, [status(thm)], [c_50, c_5590])).
% 10.31/3.64  tff(c_4604, plain, (![B_235, A_236]: (v3_pre_topc(u1_struct_0(B_235), A_236) | ~m1_subset_1(u1_struct_0(B_235), k1_zfmisc_1(u1_struct_0(A_236))) | ~v1_tsep_1(B_235, A_236) | ~m1_pre_topc(B_235, A_236) | ~l1_pre_topc(A_236))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.31/3.64  tff(c_4651, plain, (![B_39, A_37]: (v3_pre_topc(u1_struct_0(B_39), A_37) | ~v1_tsep_1(B_39, A_37) | ~m1_pre_topc(B_39, A_37) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_50, c_4604])).
% 10.31/3.64  tff(c_3419, plain, (![B_181, A_182]: (r2_hidden(B_181, u1_pre_topc(A_182)) | ~v3_pre_topc(B_181, A_182) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.31/3.64  tff(c_3434, plain, (![B_39, A_37]: (r2_hidden(u1_struct_0(B_39), u1_pre_topc(A_37)) | ~v3_pre_topc(u1_struct_0(B_39), A_37) | ~m1_pre_topc(B_39, A_37) | ~l1_pre_topc(A_37))), inference(resolution, [status(thm)], [c_50, c_3419])).
% 10.31/3.64  tff(c_3270, plain, (![B_154, A_155]: (m1_subset_1(u1_struct_0(B_154), k1_zfmisc_1(u1_struct_0(A_155))) | ~m1_pre_topc(B_154, A_155) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_159])).
% 10.31/3.64  tff(c_3276, plain, (![B_154]: (m1_subset_1(u1_struct_0(B_154), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_154, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3246, c_3270])).
% 10.31/3.64  tff(c_3278, plain, (![B_154]: (m1_subset_1(u1_struct_0(B_154), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_pre_topc(B_154, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3276])).
% 10.31/3.64  tff(c_5453, plain, (![B_258]: (k5_tmap_1('#skF_2', u1_struct_0(B_258))=u1_pre_topc('#skF_2') | ~r2_hidden(u1_struct_0(B_258), u1_pre_topc('#skF_2')) | ~m1_pre_topc(B_258, '#skF_2'))), inference(resolution, [status(thm)], [c_3278, c_5386])).
% 10.31/3.64  tff(c_5481, plain, (![B_39]: (k5_tmap_1('#skF_2', u1_struct_0(B_39))=u1_pre_topc('#skF_2') | ~v3_pre_topc(u1_struct_0(B_39), '#skF_2') | ~m1_pre_topc(B_39, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_3434, c_5453])).
% 10.31/3.64  tff(c_5515, plain, (![B_259]: (k5_tmap_1('#skF_2', u1_struct_0(B_259))=u1_pre_topc('#skF_2') | ~v3_pre_topc(u1_struct_0(B_259), '#skF_2') | ~m1_pre_topc(B_259, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_5481])).
% 10.31/3.64  tff(c_5525, plain, (![B_39]: (k5_tmap_1('#skF_2', u1_struct_0(B_39))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_39, '#skF_2') | ~m1_pre_topc(B_39, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_4651, c_5515])).
% 10.31/3.64  tff(c_5549, plain, (![B_39]: (k5_tmap_1('#skF_2', u1_struct_0(B_39))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_39, '#skF_2') | ~m1_pre_topc(B_39, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_5525])).
% 10.31/3.64  tff(c_8321, plain, (![B_328]: (u1_pre_topc(k8_tmap_1('#skF_2', B_328))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_328, '#skF_2') | ~m1_pre_topc(B_328, '#skF_2') | v2_struct_0(B_328) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_328, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8299, c_5549])).
% 10.31/3.64  tff(c_8383, plain, (![B_328]: (u1_pre_topc(k8_tmap_1('#skF_2', B_328))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_328, '#skF_2') | v2_struct_0(B_328) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_328, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_8321])).
% 10.31/3.64  tff(c_8384, plain, (![B_328]: (u1_pre_topc(k8_tmap_1('#skF_2', B_328))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_328, '#skF_2') | v2_struct_0(B_328) | ~m1_pre_topc(B_328, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_8383])).
% 10.31/3.64  tff(c_4314, plain, (![A_229, B_230]: (u1_struct_0(k8_tmap_1(A_229, B_230))=u1_struct_0(A_229) | ~m1_pre_topc(B_230, A_229) | v2_struct_0(B_230) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.31/3.64  tff(c_12642, plain, (![A_411, B_412]: (g1_pre_topc(u1_struct_0(A_411), u1_pre_topc(k8_tmap_1(A_411, B_412)))=k8_tmap_1(A_411, B_412) | ~v1_pre_topc(k8_tmap_1(A_411, B_412)) | ~l1_pre_topc(k8_tmap_1(A_411, B_412)) | ~m1_pre_topc(B_412, A_411) | v2_struct_0(B_412) | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(superposition, [status(thm), theory('equality')], [c_4314, c_6])).
% 10.31/3.64  tff(c_12669, plain, (![B_328]: (k8_tmap_1('#skF_2', B_328)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_328)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_328)) | ~m1_pre_topc(B_328, '#skF_2') | v2_struct_0(B_328) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_328, '#skF_2') | v2_struct_0(B_328) | ~m1_pre_topc(B_328, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8384, c_12642])).
% 10.31/3.64  tff(c_12709, plain, (![B_328]: (k8_tmap_1('#skF_2', B_328)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_328)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_328)) | v2_struct_0('#skF_2') | ~v1_tsep_1(B_328, '#skF_2') | v2_struct_0(B_328) | ~m1_pre_topc(B_328, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_5406, c_3246, c_12669])).
% 10.31/3.64  tff(c_13147, plain, (![B_442]: (k8_tmap_1('#skF_2', B_442)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_442)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_442)) | ~v1_tsep_1(B_442, '#skF_2') | v2_struct_0(B_442) | ~m1_pre_topc(B_442, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_12709])).
% 10.31/3.64  tff(c_13151, plain, (![B_23]: (k8_tmap_1('#skF_2', B_23)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_23)) | ~v1_tsep_1(B_23, '#skF_2') | v2_struct_0(B_23) | ~m1_pre_topc(B_23, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_13147])).
% 10.31/3.64  tff(c_13154, plain, (![B_23]: (k8_tmap_1('#skF_2', B_23)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_23)) | ~v1_tsep_1(B_23, '#skF_2') | v2_struct_0(B_23) | ~m1_pre_topc(B_23, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_13151])).
% 10.31/3.64  tff(c_13156, plain, (![B_443]: (k8_tmap_1('#skF_2', B_443)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_443)) | ~v1_tsep_1(B_443, '#skF_2') | v2_struct_0(B_443) | ~m1_pre_topc(B_443, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_13154])).
% 10.31/3.64  tff(c_13160, plain, (![B_23]: (k8_tmap_1('#skF_2', B_23)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_tsep_1(B_23, '#skF_2') | v2_struct_0(B_23) | ~m1_pre_topc(B_23, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_13156])).
% 10.31/3.64  tff(c_13163, plain, (![B_23]: (k8_tmap_1('#skF_2', B_23)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_tsep_1(B_23, '#skF_2') | v2_struct_0(B_23) | ~m1_pre_topc(B_23, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_13160])).
% 10.31/3.64  tff(c_13165, plain, (![B_444]: (k8_tmap_1('#skF_2', B_444)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_tsep_1(B_444, '#skF_2') | v2_struct_0(B_444) | ~m1_pre_topc(B_444, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_13163])).
% 10.31/3.64  tff(c_13170, plain, (k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3240, c_13165])).
% 10.31/3.64  tff(c_13176, plain, (k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_13170])).
% 10.31/3.64  tff(c_13178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5509, c_13176])).
% 10.31/3.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.31/3.64  
% 10.31/3.64  Inference rules
% 10.31/3.64  ----------------------
% 10.31/3.64  #Ref     : 0
% 10.31/3.64  #Sup     : 3436
% 10.31/3.64  #Fact    : 0
% 10.31/3.64  #Define  : 0
% 10.31/3.64  #Split   : 11
% 10.31/3.64  #Chain   : 0
% 10.31/3.64  #Close   : 0
% 10.31/3.64  
% 10.31/3.64  Ordering : KBO
% 10.31/3.64  
% 10.31/3.64  Simplification rules
% 10.31/3.64  ----------------------
% 10.31/3.64  #Subsume      : 321
% 10.31/3.64  #Demod        : 2201
% 10.31/3.64  #Tautology    : 713
% 10.31/3.64  #SimpNegUnit  : 222
% 10.31/3.64  #BackRed      : 26
% 10.31/3.64  
% 10.31/3.64  #Partial instantiations: 0
% 10.31/3.64  #Strategies tried      : 1
% 10.31/3.64  
% 10.31/3.64  Timing (in seconds)
% 10.31/3.64  ----------------------
% 10.31/3.64  Preprocessing        : 0.36
% 10.31/3.64  Parsing              : 0.18
% 10.31/3.65  CNF conversion       : 0.02
% 10.31/3.65  Main loop            : 2.48
% 10.31/3.65  Inferencing          : 0.68
% 10.31/3.65  Reduction            : 0.78
% 10.31/3.65  Demodulation         : 0.54
% 10.31/3.65  BG Simplification    : 0.10
% 10.31/3.65  Subsumption          : 0.75
% 10.31/3.65  Abstraction          : 0.10
% 10.31/3.65  MUC search           : 0.00
% 10.31/3.65  Cooper               : 0.00
% 10.31/3.65  Total                : 2.90
% 10.31/3.65  Index Insertion      : 0.00
% 10.31/3.65  Index Deletion       : 0.00
% 10.31/3.65  Index Matching       : 0.00
% 10.31/3.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
