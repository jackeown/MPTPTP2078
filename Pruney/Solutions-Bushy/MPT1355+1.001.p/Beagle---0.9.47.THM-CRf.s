%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1355+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:51 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 980 expanded)
%              Number of leaves         :   26 ( 342 expanded)
%              Depth                    :   16
%              Number of atoms          :  411 (2353 expanded)
%              Number of equality atoms :    7 ( 276 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_compts_1 > v1_tops_2 > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_finset_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ( v1_compts_1(A)
        <=> v2_compts_1(k2_struct_0(A),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_compts_1(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & v1_tops_2(B,A)
                & ! [C] :
                    ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                   => ~ ( r1_tarski(C,B)
                        & m1_setfam_1(C,u1_struct_0(A))
                        & v1_finset_1(C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_compts_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_compts_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( m1_setfam_1(C,B)
                    & v1_tops_2(C,A)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                       => ~ ( r1_tarski(D,C)
                            & m1_setfam_1(D,B)
                            & v1_finset_1(D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_compts_1)).

tff(c_42,plain,
    ( ~ v2_compts_1(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_50,plain,(
    ~ v1_compts_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    ! [A_39] :
      ( l1_struct_0(A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_57,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(resolution,[status(thm)],[c_38,c_52])).

tff(c_61,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_67,plain,(
    ! [A_44] :
      ( m1_subset_1(k2_struct_0(A_44),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_70,plain,
    ( m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_67])).

tff(c_71,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_74,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_74])).

tff(c_80,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_48,plain,
    ( v1_compts_1('#skF_5')
    | v2_compts_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_51,plain,(
    v2_compts_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_48])).

tff(c_86,plain,(
    ! [A_45] :
      ( m1_setfam_1('#skF_2'(A_45),u1_struct_0(A_45))
      | v1_compts_1(A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_89,plain,
    ( m1_setfam_1('#skF_2'('#skF_5'),k2_struct_0('#skF_5'))
    | v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_86])).

tff(c_91,plain,
    ( m1_setfam_1('#skF_2'('#skF_5'),k2_struct_0('#skF_5'))
    | v1_compts_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_89])).

tff(c_92,plain,(
    m1_setfam_1('#skF_2'('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_91])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_tops_2('#skF_2'(A_1),A_1)
      | v1_compts_1(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,(
    ! [A_46] :
      ( m1_subset_1('#skF_2'(A_46),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_46))))
      | v1_compts_1(A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_96,plain,
    ( m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
    | v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_93])).

tff(c_98,plain,
    ( m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
    | v1_compts_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_96])).

tff(c_99,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_98])).

tff(c_222,plain,(
    ! [A_74,B_75,C_76] :
      ( v1_finset_1('#skF_3'(A_74,B_75,C_76))
      | ~ v1_tops_2(C_76,A_74)
      | ~ m1_setfam_1(C_76,B_75)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_74))))
      | ~ v2_compts_1(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_230,plain,(
    ! [B_75,C_76] :
      ( v1_finset_1('#skF_3'('#skF_5',B_75,C_76))
      | ~ v1_tops_2(C_76,'#skF_5')
      | ~ m1_setfam_1(C_76,B_75)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v2_compts_1(B_75,'#skF_5')
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_222])).

tff(c_236,plain,(
    ! [B_77,C_78] :
      ( v1_finset_1('#skF_3'('#skF_5',B_77,C_78))
      | ~ v1_tops_2(C_78,'#skF_5')
      | ~ m1_setfam_1(C_78,B_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v2_compts_1(B_77,'#skF_5')
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_61,c_230])).

tff(c_242,plain,(
    ! [B_77] :
      ( v1_finset_1('#skF_3'('#skF_5',B_77,'#skF_2'('#skF_5')))
      | ~ v1_tops_2('#skF_2'('#skF_5'),'#skF_5')
      | ~ m1_setfam_1('#skF_2'('#skF_5'),B_77)
      | ~ v2_compts_1(B_77,'#skF_5')
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_99,c_236])).

tff(c_243,plain,(
    ~ v1_tops_2('#skF_2'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_246,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_243])).

tff(c_249,plain,(
    v1_compts_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_246])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_249])).

tff(c_253,plain,(
    v1_tops_2('#skF_2'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_79,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_254,plain,(
    ! [B_79] :
      ( v1_finset_1('#skF_3'('#skF_5',B_79,'#skF_2'('#skF_5')))
      | ~ m1_setfam_1('#skF_2'('#skF_5'),B_79)
      | ~ v2_compts_1(B_79,'#skF_5')
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_257,plain,
    ( v1_finset_1('#skF_3'('#skF_5',k2_struct_0('#skF_5'),'#skF_2'('#skF_5')))
    | ~ m1_setfam_1('#skF_2'('#skF_5'),k2_struct_0('#skF_5'))
    | ~ v2_compts_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_79,c_254])).

tff(c_260,plain,(
    v1_finset_1('#skF_3'('#skF_5',k2_struct_0('#skF_5'),'#skF_2'('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_92,c_257])).

tff(c_36,plain,(
    ! [A_38] :
      ( m1_subset_1(k2_struct_0(A_38),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_2'(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | v1_compts_1(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_270,plain,(
    ! [A_82,B_83,C_84] :
      ( m1_setfam_1('#skF_3'(A_82,B_83,C_84),B_83)
      | ~ v1_tops_2(C_84,A_82)
      | ~ m1_setfam_1(C_84,B_83)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_82))))
      | ~ v2_compts_1(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_306,plain,(
    ! [A_91,B_92] :
      ( m1_setfam_1('#skF_3'(A_91,B_92,'#skF_2'(A_91)),B_92)
      | ~ v1_tops_2('#skF_2'(A_91),A_91)
      | ~ m1_setfam_1('#skF_2'(A_91),B_92)
      | ~ v2_compts_1(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | v1_compts_1(A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_8,c_270])).

tff(c_311,plain,(
    ! [A_38] :
      ( m1_setfam_1('#skF_3'(A_38,k2_struct_0(A_38),'#skF_2'(A_38)),k2_struct_0(A_38))
      | ~ v1_tops_2('#skF_2'(A_38),A_38)
      | ~ m1_setfam_1('#skF_2'(A_38),k2_struct_0(A_38))
      | ~ v2_compts_1(k2_struct_0(A_38),A_38)
      | v1_compts_1(A_38)
      | ~ l1_pre_topc(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_36,c_306])).

tff(c_316,plain,(
    ! [A_94,B_95,C_96] :
      ( r1_tarski('#skF_3'(A_94,B_95,C_96),C_96)
      | ~ v1_tops_2(C_96,A_94)
      | ~ m1_setfam_1(C_96,B_95)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_94))))
      | ~ v2_compts_1(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_327,plain,(
    ! [A_1,B_95] :
      ( r1_tarski('#skF_3'(A_1,B_95,'#skF_2'(A_1)),'#skF_2'(A_1))
      | ~ v1_tops_2('#skF_2'(A_1),A_1)
      | ~ m1_setfam_1('#skF_2'(A_1),B_95)
      | ~ v2_compts_1(B_95,A_1)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_1)))
      | v1_compts_1(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_8,c_316])).

tff(c_339,plain,(
    ! [A_99,B_100,C_101] :
      ( m1_subset_1('#skF_3'(A_99,B_100,C_101),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_99))))
      | ~ v1_tops_2(C_101,A_99)
      | ~ m1_setfam_1(C_101,B_100)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_99))))
      | ~ v2_compts_1(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_358,plain,(
    ! [B_100,C_101] :
      ( m1_subset_1('#skF_3'('#skF_5',B_100,C_101),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v1_tops_2(C_101,'#skF_5')
      | ~ m1_setfam_1(C_101,B_100)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
      | ~ v2_compts_1(B_100,'#skF_5')
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_339])).

tff(c_371,plain,(
    ! [B_107,C_108] :
      ( m1_subset_1('#skF_3'('#skF_5',B_107,C_108),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v1_tops_2(C_108,'#skF_5')
      | ~ m1_setfam_1(C_108,B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v2_compts_1(B_107,'#skF_5')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_61,c_61,c_358])).

tff(c_135,plain,(
    ! [C_57,A_58] :
      ( ~ v1_finset_1(C_57)
      | ~ m1_setfam_1(C_57,u1_struct_0(A_58))
      | ~ r1_tarski(C_57,'#skF_2'(A_58))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_58))))
      | v1_compts_1(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_144,plain,(
    ! [C_57] :
      ( ~ v1_finset_1(C_57)
      | ~ m1_setfam_1(C_57,u1_struct_0('#skF_5'))
      | ~ r1_tarski(C_57,'#skF_2'('#skF_5'))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_135])).

tff(c_148,plain,(
    ! [C_57] :
      ( ~ v1_finset_1(C_57)
      | ~ m1_setfam_1(C_57,k2_struct_0('#skF_5'))
      | ~ r1_tarski(C_57,'#skF_2'('#skF_5'))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | v1_compts_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_61,c_144])).

tff(c_149,plain,(
    ! [C_57] :
      ( ~ v1_finset_1(C_57)
      | ~ m1_setfam_1(C_57,k2_struct_0('#skF_5'))
      | ~ r1_tarski(C_57,'#skF_2'('#skF_5'))
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_148])).

tff(c_425,plain,(
    ! [B_126,C_127] :
      ( ~ v1_finset_1('#skF_3'('#skF_5',B_126,C_127))
      | ~ m1_setfam_1('#skF_3'('#skF_5',B_126,C_127),k2_struct_0('#skF_5'))
      | ~ r1_tarski('#skF_3'('#skF_5',B_126,C_127),'#skF_2'('#skF_5'))
      | ~ v1_tops_2(C_127,'#skF_5')
      | ~ m1_setfam_1(C_127,B_126)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v2_compts_1(B_126,'#skF_5')
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_371,c_149])).

tff(c_428,plain,(
    ! [B_95] :
      ( ~ v1_finset_1('#skF_3'('#skF_5',B_95,'#skF_2'('#skF_5')))
      | ~ m1_setfam_1('#skF_3'('#skF_5',B_95,'#skF_2'('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ v1_tops_2('#skF_2'('#skF_5'),'#skF_5')
      | ~ m1_setfam_1('#skF_2'('#skF_5'),B_95)
      | ~ v2_compts_1(B_95,'#skF_5')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_327,c_425])).

tff(c_433,plain,(
    ! [B_95] :
      ( ~ v1_finset_1('#skF_3'('#skF_5',B_95,'#skF_2'('#skF_5')))
      | ~ m1_setfam_1('#skF_3'('#skF_5',B_95,'#skF_2'('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_setfam_1('#skF_2'('#skF_5'),B_95)
      | ~ v2_compts_1(B_95,'#skF_5')
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v1_compts_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_61,c_253,c_99,c_428])).

tff(c_438,plain,(
    ! [B_128] :
      ( ~ v1_finset_1('#skF_3'('#skF_5',B_128,'#skF_2'('#skF_5')))
      | ~ m1_setfam_1('#skF_3'('#skF_5',B_128,'#skF_2'('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_setfam_1('#skF_2'('#skF_5'),B_128)
      | ~ v2_compts_1(B_128,'#skF_5')
      | ~ m1_subset_1(B_128,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_433])).

tff(c_442,plain,
    ( ~ v1_finset_1('#skF_3'('#skF_5',k2_struct_0('#skF_5'),'#skF_2'('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ v1_tops_2('#skF_2'('#skF_5'),'#skF_5')
    | ~ m1_setfam_1('#skF_2'('#skF_5'),k2_struct_0('#skF_5'))
    | ~ v2_compts_1(k2_struct_0('#skF_5'),'#skF_5')
    | v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_311,c_438])).

tff(c_448,plain,(
    v1_compts_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_40,c_51,c_92,c_253,c_79,c_260,c_442])).

tff(c_450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_448])).

tff(c_451,plain,(
    ~ v2_compts_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_455,plain,(
    ! [A_129] :
      ( u1_struct_0(A_129) = k2_struct_0(A_129)
      | ~ l1_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_461,plain,(
    ! [A_131] :
      ( u1_struct_0(A_131) = k2_struct_0(A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_38,c_455])).

tff(c_465,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_461])).

tff(c_470,plain,(
    ! [A_132] :
      ( m1_subset_1(k2_struct_0(A_132),k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_473,plain,
    ( m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_470])).

tff(c_474,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_477,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_474])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_477])).

tff(c_482,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_532,plain,(
    ! [A_143,B_144] :
      ( m1_subset_1('#skF_4'(A_143,B_144),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143))))
      | v2_compts_1(B_144,A_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_535,plain,(
    ! [B_144] :
      ( m1_subset_1('#skF_4'('#skF_5',B_144),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | v2_compts_1(B_144,'#skF_5')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_532])).

tff(c_537,plain,(
    ! [B_144] :
      ( m1_subset_1('#skF_4'('#skF_5',B_144),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | v2_compts_1(B_144,'#skF_5')
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_465,c_535])).

tff(c_501,plain,(
    ! [A_135,B_136] :
      ( m1_setfam_1('#skF_4'(A_135,B_136),B_136)
      | v2_compts_1(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_505,plain,(
    ! [B_136] :
      ( m1_setfam_1('#skF_4'('#skF_5',B_136),B_136)
      | v2_compts_1(B_136,'#skF_5')
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_501])).

tff(c_509,plain,(
    ! [B_137] :
      ( m1_setfam_1('#skF_4'('#skF_5',B_137),B_137)
      | v2_compts_1(B_137,'#skF_5')
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_505])).

tff(c_511,plain,
    ( m1_setfam_1('#skF_4'('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | v2_compts_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_482,c_509])).

tff(c_514,plain,(
    m1_setfam_1('#skF_4'('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_511])).

tff(c_515,plain,(
    ! [A_138,B_139] :
      ( v1_tops_2('#skF_4'(A_138,B_139),A_138)
      | v2_compts_1(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_519,plain,(
    ! [B_139] :
      ( v1_tops_2('#skF_4'('#skF_5',B_139),'#skF_5')
      | v2_compts_1(B_139,'#skF_5')
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_515])).

tff(c_523,plain,(
    ! [B_140] :
      ( v1_tops_2('#skF_4'('#skF_5',B_140),'#skF_5')
      | v2_compts_1(B_140,'#skF_5')
      | ~ m1_subset_1(B_140,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_519])).

tff(c_526,plain,
    ( v1_tops_2('#skF_4'('#skF_5',k2_struct_0('#skF_5')),'#skF_5')
    | v2_compts_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_482,c_523])).

tff(c_529,plain,(
    v1_tops_2('#skF_4'('#skF_5',k2_struct_0('#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_526])).

tff(c_452,plain,(
    v1_compts_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_612,plain,(
    ! [A_159,B_160] :
      ( m1_subset_1('#skF_1'(A_159,B_160),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_159))))
      | ~ v1_tops_2(B_160,A_159)
      | ~ m1_setfam_1(B_160,u1_struct_0(A_159))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_159))))
      | ~ v1_compts_1(A_159)
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_625,plain,(
    ! [B_160] :
      ( m1_subset_1('#skF_1'('#skF_5',B_160),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v1_tops_2(B_160,'#skF_5')
      | ~ m1_setfam_1(B_160,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_612])).

tff(c_631,plain,(
    ! [B_160] :
      ( m1_subset_1('#skF_1'('#skF_5',B_160),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v1_tops_2(B_160,'#skF_5')
      | ~ m1_setfam_1(B_160,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_452,c_465,c_465,c_625])).

tff(c_554,plain,(
    ! [A_149,B_150] :
      ( v1_finset_1('#skF_1'(A_149,B_150))
      | ~ v1_tops_2(B_150,A_149)
      | ~ m1_setfam_1(B_150,u1_struct_0(A_149))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_149))))
      | ~ v1_compts_1(A_149)
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_563,plain,(
    ! [B_150] :
      ( v1_finset_1('#skF_1'('#skF_5',B_150))
      | ~ v1_tops_2(B_150,'#skF_5')
      | ~ m1_setfam_1(B_150,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_554])).

tff(c_568,plain,(
    ! [B_151] :
      ( v1_finset_1('#skF_1'('#skF_5',B_151))
      | ~ v1_tops_2(B_151,'#skF_5')
      | ~ m1_setfam_1(B_151,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_452,c_465,c_563])).

tff(c_573,plain,(
    ! [B_152] :
      ( v1_finset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',B_152)))
      | ~ v1_tops_2('#skF_4'('#skF_5',B_152),'#skF_5')
      | ~ m1_setfam_1('#skF_4'('#skF_5',B_152),k2_struct_0('#skF_5'))
      | v2_compts_1(B_152,'#skF_5')
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_537,c_568])).

tff(c_576,plain,
    ( v1_finset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',k2_struct_0('#skF_5'))))
    | ~ v1_tops_2('#skF_4'('#skF_5',k2_struct_0('#skF_5')),'#skF_5')
    | ~ m1_setfam_1('#skF_4'('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | v2_compts_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_482,c_573])).

tff(c_579,plain,
    ( v1_finset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',k2_struct_0('#skF_5'))))
    | v2_compts_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_529,c_576])).

tff(c_580,plain,(
    v1_finset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',k2_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_579])).

tff(c_26,plain,(
    ! [A_13,B_27] :
      ( m1_subset_1('#skF_4'(A_13,B_27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | v2_compts_1(B_27,A_13)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_596,plain,(
    ! [A_156,B_157] :
      ( m1_setfam_1('#skF_1'(A_156,B_157),u1_struct_0(A_156))
      | ~ v1_tops_2(B_157,A_156)
      | ~ m1_setfam_1(B_157,u1_struct_0(A_156))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156))))
      | ~ v1_compts_1(A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_603,plain,(
    ! [A_13,B_27] :
      ( m1_setfam_1('#skF_1'(A_13,'#skF_4'(A_13,B_27)),u1_struct_0(A_13))
      | ~ v1_tops_2('#skF_4'(A_13,B_27),A_13)
      | ~ m1_setfam_1('#skF_4'(A_13,B_27),u1_struct_0(A_13))
      | ~ v1_compts_1(A_13)
      | v2_compts_1(B_27,A_13)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_26,c_596])).

tff(c_581,plain,(
    ! [A_153,B_154] :
      ( r1_tarski('#skF_1'(A_153,B_154),B_154)
      | ~ v1_tops_2(B_154,A_153)
      | ~ m1_setfam_1(B_154,u1_struct_0(A_153))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_153))))
      | ~ v1_compts_1(A_153)
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_587,plain,(
    ! [B_154] :
      ( r1_tarski('#skF_1'('#skF_5',B_154),B_154)
      | ~ v1_tops_2(B_154,'#skF_5')
      | ~ m1_setfam_1(B_154,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_581])).

tff(c_592,plain,(
    ! [B_155] :
      ( r1_tarski('#skF_1'('#skF_5',B_155),B_155)
      | ~ v1_tops_2(B_155,'#skF_5')
      | ~ m1_setfam_1(B_155,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_452,c_465,c_587])).

tff(c_727,plain,(
    ! [B_188] :
      ( r1_tarski('#skF_1'('#skF_5','#skF_4'('#skF_5',B_188)),'#skF_4'('#skF_5',B_188))
      | ~ v1_tops_2('#skF_4'('#skF_5',B_188),'#skF_5')
      | ~ m1_setfam_1('#skF_4'('#skF_5',B_188),k2_struct_0('#skF_5'))
      | v2_compts_1(B_188,'#skF_5')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_537,c_592])).

tff(c_20,plain,(
    ! [D_37,B_27,A_13] :
      ( ~ v1_finset_1(D_37)
      | ~ m1_setfam_1(D_37,B_27)
      | ~ r1_tarski(D_37,'#skF_4'(A_13,B_27))
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | v2_compts_1(B_27,A_13)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_729,plain,(
    ! [B_188] :
      ( ~ v1_finset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',B_188)))
      | ~ m1_setfam_1('#skF_1'('#skF_5','#skF_4'('#skF_5',B_188)),B_188)
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',B_188)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v1_tops_2('#skF_4'('#skF_5',B_188),'#skF_5')
      | ~ m1_setfam_1('#skF_4'('#skF_5',B_188),k2_struct_0('#skF_5'))
      | v2_compts_1(B_188,'#skF_5')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_727,c_20])).

tff(c_946,plain,(
    ! [B_246] :
      ( ~ v1_finset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',B_246)))
      | ~ m1_setfam_1('#skF_1'('#skF_5','#skF_4'('#skF_5',B_246)),B_246)
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',B_246)),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
      | ~ v1_tops_2('#skF_4'('#skF_5',B_246),'#skF_5')
      | ~ m1_setfam_1('#skF_4'('#skF_5',B_246),k2_struct_0('#skF_5'))
      | v2_compts_1(B_246,'#skF_5')
      | ~ m1_subset_1(B_246,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_465,c_465,c_729])).

tff(c_949,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',u1_struct_0('#skF_5'))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
    | ~ m1_setfam_1('#skF_4'('#skF_5',u1_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ v1_tops_2('#skF_4'('#skF_5',u1_struct_0('#skF_5')),'#skF_5')
    | ~ m1_setfam_1('#skF_4'('#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
    | ~ v1_compts_1('#skF_5')
    | v2_compts_1(u1_struct_0('#skF_5'),'#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_603,c_946])).

tff(c_955,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',k2_struct_0('#skF_5'))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5'))))
    | v2_compts_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_482,c_465,c_465,c_465,c_452,c_514,c_465,c_465,c_529,c_465,c_482,c_465,c_514,c_465,c_465,c_580,c_465,c_949])).

tff(c_956,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_4'('#skF_5',k2_struct_0('#skF_5'))),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_955])).

tff(c_963,plain,
    ( ~ v1_tops_2('#skF_4'('#skF_5',k2_struct_0('#skF_5')),'#skF_5')
    | ~ m1_setfam_1('#skF_4'('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_4'('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_631,c_956])).

tff(c_966,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5',k2_struct_0('#skF_5')),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_529,c_963])).

tff(c_969,plain,
    ( v2_compts_1(k2_struct_0('#skF_5'),'#skF_5')
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_537,c_966])).

tff(c_972,plain,(
    v2_compts_1(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_969])).

tff(c_974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_972])).

%------------------------------------------------------------------------------
