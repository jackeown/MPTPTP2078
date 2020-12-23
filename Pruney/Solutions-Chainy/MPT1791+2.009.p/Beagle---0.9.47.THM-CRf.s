%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:50 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 277 expanded)
%              Number of leaves         :   26 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          :  225 ( 852 expanded)
%              Number of equality atoms :   53 ( 183 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_53,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_70,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_36])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_97,plain,(
    ! [B_31,A_32] :
      ( v3_pre_topc(B_31,A_32)
      | ~ r2_hidden(B_31,u1_pre_topc(A_32))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_100,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_97])).

tff(c_103,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_100])).

tff(c_104,plain,(
    ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_103])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_157,plain,(
    ! [A_42,B_43] :
      ( v1_pre_topc(k6_tmap_1(A_42,B_43))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_160,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_157])).

tff(c_163,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_160])).

tff(c_164,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_163])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5] :
      ( m1_subset_1(u1_pre_topc(A_5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_5))))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_88,plain,(
    ! [C_27,A_28,D_29,B_30] :
      ( C_27 = A_28
      | g1_pre_topc(C_27,D_29) != g1_pre_topc(A_28,B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_92,plain,(
    ! [C_27,D_29] :
      ( u1_struct_0('#skF_1') = C_27
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_27,D_29)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_88])).

tff(c_122,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_125,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_122])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_125])).

tff(c_146,plain,(
    ! [C_39,D_40] :
      ( u1_struct_0('#skF_1') = C_39
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_39,D_40) ) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_152,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_1')
      | k6_tmap_1('#skF_1','#skF_2') != A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_168,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_164,c_152])).

tff(c_169,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_187,plain,(
    ! [A_47,B_48] :
      ( l1_pre_topc(k6_tmap_1(A_47,B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_190,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_187])).

tff(c_193,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_190])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_169,c_193])).

tff(c_197,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_196,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_210,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_2])).

tff(c_223,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_164,c_210])).

tff(c_131,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_75,plain,(
    ! [D_23,B_24,C_25,A_26] :
      ( D_23 = B_24
      | g1_pre_topc(C_25,D_23) != g1_pre_topc(A_26,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_79,plain,(
    ! [D_23,C_25] :
      ( u1_pre_topc('#skF_1') = D_23
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_25,D_23)
      | ~ m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_75])).

tff(c_267,plain,(
    ! [D_51,C_52] :
      ( u1_pre_topc('#skF_1') = D_51
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_52,D_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_79])).

tff(c_277,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = u1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_267])).

tff(c_377,plain,(
    ! [A_66,B_67] :
      ( u1_pre_topc(k6_tmap_1(A_66,B_67)) = k5_tmap_1(A_66,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_383,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_377])).

tff(c_388,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_277,c_383])).

tff(c_389,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_388])).

tff(c_456,plain,(
    ! [B_80,A_81] :
      ( r2_hidden(B_80,u1_pre_topc(A_81))
      | k5_tmap_1(A_81,B_80) != u1_pre_topc(A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_462,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | k5_tmap_1('#skF_1','#skF_2') != u1_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_456])).

tff(c_467,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_389,c_462])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_104,c_467])).

tff(c_471,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) != k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_470,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_505,plain,(
    ! [B_92,A_93] :
      ( r2_hidden(B_92,u1_pre_topc(A_93))
      | ~ v3_pre_topc(B_92,A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_508,plain,
    ( r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_505])).

tff(c_511,plain,(
    r2_hidden('#skF_2',u1_pre_topc('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_470,c_508])).

tff(c_685,plain,(
    ! [A_115,B_116] :
      ( k5_tmap_1(A_115,B_116) = u1_pre_topc(A_115)
      | ~ r2_hidden(B_116,u1_pre_topc(A_115))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_691,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | ~ r2_hidden('#skF_2',u1_pre_topc('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_685])).

tff(c_696,plain,
    ( k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_511,c_691])).

tff(c_697,plain,(
    k5_tmap_1('#skF_1','#skF_2') = u1_pre_topc('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_696])).

tff(c_512,plain,(
    ! [A_94,B_95] :
      ( l1_pre_topc(k6_tmap_1(A_94,B_95))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_515,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_512])).

tff(c_518,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_515])).

tff(c_519,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_518])).

tff(c_520,plain,(
    ! [A_96,B_97] :
      ( v1_pre_topc(k6_tmap_1(A_96,B_97))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_523,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_520])).

tff(c_526,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_523])).

tff(c_527,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_526])).

tff(c_554,plain,(
    ! [A_106,B_107] :
      ( u1_struct_0(k6_tmap_1(A_106,B_107)) = u1_struct_0(A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_557,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_554])).

tff(c_560,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_557])).

tff(c_561,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_560])).

tff(c_562,plain,(
    ! [A_108,B_109] :
      ( u1_pre_topc(k6_tmap_1(A_108,B_109)) = k5_tmap_1(A_108,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_565,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_562])).

tff(c_568,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_565])).

tff(c_569,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_568])).

tff(c_622,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1','#skF_2')),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_2])).

tff(c_629,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_527,c_561,c_622])).

tff(c_699,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_629])).

tff(c_703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_471,c_699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.93  
% 3.58/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.93  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.58/1.93  
% 3.58/1.93  %Foreground sorts:
% 3.58/1.93  
% 3.58/1.93  
% 3.58/1.93  %Background operators:
% 3.58/1.93  
% 3.58/1.93  
% 3.58/1.93  %Foreground operators:
% 3.58/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.58/1.93  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.58/1.93  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.58/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.93  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.58/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.58/1.93  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.93  tff('#skF_1', type, '#skF_1': $i).
% 3.58/1.93  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.58/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.93  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.58/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.58/1.93  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 3.58/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.93  
% 3.58/1.96  tff(f_111, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.58/1.96  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.58/1.96  tff(f_68, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.58/1.96  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.58/1.96  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.58/1.96  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.58/1.96  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.58/1.96  tff(f_82, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 3.58/1.96  tff(c_34, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.58/1.96  tff(c_42, plain, (v3_pre_topc('#skF_2', '#skF_1') | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.58/1.96  tff(c_53, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 3.58/1.96  tff(c_36, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.58/1.96  tff(c_70, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_36])).
% 3.58/1.96  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.58/1.96  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.58/1.96  tff(c_97, plain, (![B_31, A_32]: (v3_pre_topc(B_31, A_32) | ~r2_hidden(B_31, u1_pre_topc(A_32)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.58/1.96  tff(c_100, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_97])).
% 3.58/1.96  tff(c_103, plain, (v3_pre_topc('#skF_2', '#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_100])).
% 3.58/1.96  tff(c_104, plain, (~r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_70, c_103])).
% 3.58/1.96  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.58/1.96  tff(c_157, plain, (![A_42, B_43]: (v1_pre_topc(k6_tmap_1(A_42, B_43)) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.96  tff(c_160, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_157])).
% 3.58/1.96  tff(c_163, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_160])).
% 3.58/1.96  tff(c_164, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_163])).
% 3.58/1.96  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.58/1.96  tff(c_8, plain, (![A_5]: (m1_subset_1(u1_pre_topc(A_5), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_5)))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.58/1.96  tff(c_88, plain, (![C_27, A_28, D_29, B_30]: (C_27=A_28 | g1_pre_topc(C_27, D_29)!=g1_pre_topc(A_28, B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_28))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.58/1.96  tff(c_92, plain, (![C_27, D_29]: (u1_struct_0('#skF_1')=C_27 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_27, D_29) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_53, c_88])).
% 3.58/1.96  tff(c_122, plain, (~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_92])).
% 3.58/1.96  tff(c_125, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_8, c_122])).
% 3.58/1.96  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_125])).
% 3.58/1.96  tff(c_146, plain, (![C_39, D_40]: (u1_struct_0('#skF_1')=C_39 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_39, D_40))), inference(splitRight, [status(thm)], [c_92])).
% 3.58/1.96  tff(c_152, plain, (![A_1]: (u1_struct_0(A_1)=u1_struct_0('#skF_1') | k6_tmap_1('#skF_1', '#skF_2')!=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_146])).
% 3.58/1.96  tff(c_168, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_164, c_152])).
% 3.58/1.96  tff(c_169, plain, (~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_168])).
% 3.58/1.96  tff(c_187, plain, (![A_47, B_48]: (l1_pre_topc(k6_tmap_1(A_47, B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.96  tff(c_190, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_187])).
% 3.58/1.96  tff(c_193, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_190])).
% 3.58/1.96  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_169, c_193])).
% 3.58/1.96  tff(c_197, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_168])).
% 3.58/1.96  tff(c_196, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_168])).
% 3.58/1.96  tff(c_210, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_2])).
% 3.58/1.96  tff(c_223, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_164, c_210])).
% 3.58/1.96  tff(c_131, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_92])).
% 3.58/1.96  tff(c_75, plain, (![D_23, B_24, C_25, A_26]: (D_23=B_24 | g1_pre_topc(C_25, D_23)!=g1_pre_topc(A_26, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.58/1.96  tff(c_79, plain, (![D_23, C_25]: (u1_pre_topc('#skF_1')=D_23 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_25, D_23) | ~m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_53, c_75])).
% 3.58/1.96  tff(c_267, plain, (![D_51, C_52]: (u1_pre_topc('#skF_1')=D_51 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_52, D_51))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_79])).
% 3.58/1.96  tff(c_277, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=u1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_223, c_267])).
% 3.58/1.96  tff(c_377, plain, (![A_66, B_67]: (u1_pre_topc(k6_tmap_1(A_66, B_67))=k5_tmap_1(A_66, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.58/1.96  tff(c_383, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_377])).
% 3.58/1.96  tff(c_388, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_277, c_383])).
% 3.58/1.96  tff(c_389, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_388])).
% 3.58/1.96  tff(c_456, plain, (![B_80, A_81]: (r2_hidden(B_80, u1_pre_topc(A_81)) | k5_tmap_1(A_81, B_80)!=u1_pre_topc(A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.58/1.96  tff(c_462, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | k5_tmap_1('#skF_1', '#skF_2')!=u1_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_456])).
% 3.58/1.96  tff(c_467, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_389, c_462])).
% 3.58/1.96  tff(c_469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_104, c_467])).
% 3.58/1.96  tff(c_471, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))!=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 3.58/1.96  tff(c_470, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 3.58/1.96  tff(c_505, plain, (![B_92, A_93]: (r2_hidden(B_92, u1_pre_topc(A_93)) | ~v3_pre_topc(B_92, A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.58/1.96  tff(c_508, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_505])).
% 3.58/1.96  tff(c_511, plain, (r2_hidden('#skF_2', u1_pre_topc('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_470, c_508])).
% 3.58/1.96  tff(c_685, plain, (![A_115, B_116]: (k5_tmap_1(A_115, B_116)=u1_pre_topc(A_115) | ~r2_hidden(B_116, u1_pre_topc(A_115)) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.58/1.96  tff(c_691, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | ~r2_hidden('#skF_2', u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_685])).
% 3.58/1.96  tff(c_696, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_511, c_691])).
% 3.58/1.96  tff(c_697, plain, (k5_tmap_1('#skF_1', '#skF_2')=u1_pre_topc('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_696])).
% 3.58/1.96  tff(c_512, plain, (![A_94, B_95]: (l1_pre_topc(k6_tmap_1(A_94, B_95)) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.96  tff(c_515, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_512])).
% 3.58/1.96  tff(c_518, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_515])).
% 3.58/1.96  tff(c_519, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_518])).
% 3.58/1.96  tff(c_520, plain, (![A_96, B_97]: (v1_pre_topc(k6_tmap_1(A_96, B_97)) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.58/1.96  tff(c_523, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_520])).
% 3.58/1.96  tff(c_526, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_523])).
% 3.58/1.96  tff(c_527, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_526])).
% 3.58/1.96  tff(c_554, plain, (![A_106, B_107]: (u1_struct_0(k6_tmap_1(A_106, B_107))=u1_struct_0(A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.58/1.96  tff(c_557, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_554])).
% 3.58/1.96  tff(c_560, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_557])).
% 3.58/1.96  tff(c_561, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_560])).
% 3.58/1.96  tff(c_562, plain, (![A_108, B_109]: (u1_pre_topc(k6_tmap_1(A_108, B_109))=k5_tmap_1(A_108, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.58/1.96  tff(c_565, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_562])).
% 3.58/1.96  tff(c_568, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_565])).
% 3.58/1.96  tff(c_569, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_568])).
% 3.58/1.96  tff(c_622, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_1', '#skF_2')), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_569, c_2])).
% 3.58/1.96  tff(c_629, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_527, c_561, c_622])).
% 3.58/1.96  tff(c_699, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))=k6_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_697, c_629])).
% 3.58/1.96  tff(c_703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_471, c_699])).
% 3.58/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.96  
% 3.58/1.96  Inference rules
% 3.58/1.96  ----------------------
% 3.58/1.96  #Ref     : 10
% 3.58/1.96  #Sup     : 124
% 3.58/1.96  #Fact    : 0
% 3.58/1.96  #Define  : 0
% 3.58/1.96  #Split   : 6
% 3.58/1.96  #Chain   : 0
% 3.58/1.96  #Close   : 0
% 3.58/1.96  
% 3.58/1.96  Ordering : KBO
% 3.58/1.96  
% 3.58/1.96  Simplification rules
% 3.58/1.96  ----------------------
% 3.58/1.96  #Subsume      : 20
% 3.58/1.96  #Demod        : 155
% 3.58/1.96  #Tautology    : 58
% 3.58/1.96  #SimpNegUnit  : 17
% 3.58/1.96  #BackRed      : 6
% 3.58/1.96  
% 3.58/1.96  #Partial instantiations: 0
% 3.58/1.96  #Strategies tried      : 1
% 3.58/1.96  
% 3.58/1.96  Timing (in seconds)
% 3.58/1.96  ----------------------
% 3.58/1.96  Preprocessing        : 0.52
% 3.58/1.96  Parsing              : 0.27
% 3.58/1.96  CNF conversion       : 0.04
% 3.58/1.97  Main loop            : 0.55
% 3.58/1.97  Inferencing          : 0.19
% 3.58/1.97  Reduction            : 0.17
% 3.58/1.97  Demodulation         : 0.12
% 3.58/1.97  BG Simplification    : 0.03
% 3.58/1.97  Subsumption          : 0.10
% 3.58/1.97  Abstraction          : 0.03
% 3.58/1.97  MUC search           : 0.00
% 3.58/1.97  Cooper               : 0.00
% 3.58/1.97  Total                : 1.13
% 3.58/1.97  Index Insertion      : 0.00
% 3.58/1.97  Index Deletion       : 0.00
% 3.58/1.97  Index Matching       : 0.00
% 3.58/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
