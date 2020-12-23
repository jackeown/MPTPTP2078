%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:22 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 247 expanded)
%              Number of leaves         :   21 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          :  193 ( 839 expanded)
%              Number of equality atoms :   66 ( 212 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                 => ( m1_pre_topc(B,A)
                  <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

tff(c_28,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_35,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_18,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    ! [A_30] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_30),u1_pre_topc(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,
    ( v1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_42])).

tff(c_47,plain,(
    v1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_45])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_subset_1(u1_pre_topc(A_2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2))))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [C_33,A_34,D_35,B_36] :
      ( C_33 = A_34
      | g1_pre_topc(C_33,D_35) != g1_pre_topc(A_34,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_92,plain,(
    ! [C_33,D_35] :
      ( u1_struct_0('#skF_3') = C_33
      | g1_pre_topc(C_33,D_35) != '#skF_2'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_84])).

tff(c_98,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_101,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_101])).

tff(c_108,plain,(
    ! [C_39,D_40] :
      ( u1_struct_0('#skF_3') = C_39
      | g1_pre_topc(C_39,D_40) != '#skF_2' ) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_118,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = u1_struct_0('#skF_3')
      | A_41 != '#skF_2'
      | ~ v1_pre_topc(A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_108])).

tff(c_121,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_118])).

tff(c_127,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_121])).

tff(c_132,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_2'
    | ~ v1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_2])).

tff(c_145,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_47,c_132])).

tff(c_107,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_157,plain,(
    ! [D_42,B_43,C_44,A_45] :
      ( D_42 = B_43
      | g1_pre_topc(C_44,D_42) != g1_pre_topc(A_45,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_165,plain,(
    ! [D_42,C_44] :
      ( u1_pre_topc('#skF_3') = D_42
      | g1_pre_topc(C_44,D_42) != '#skF_2'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_157])).

tff(c_199,plain,(
    ! [D_48,C_49] :
      ( u1_pre_topc('#skF_3') = D_48
      | g1_pre_topc(C_49,D_48) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_165])).

tff(c_209,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_199])).

tff(c_34,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_34])).

tff(c_251,plain,(
    ! [D_51,B_52,C_53,A_54] :
      ( m1_pre_topc(D_51,B_52)
      | ~ m1_pre_topc(C_53,A_54)
      | g1_pre_topc(u1_struct_0(D_51),u1_pre_topc(D_51)) != g1_pre_topc(u1_struct_0(C_53),u1_pre_topc(C_53))
      | g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52)) != g1_pre_topc(u1_struct_0(A_54),u1_pre_topc(A_54))
      | ~ l1_pre_topc(D_51)
      | ~ l1_pre_topc(C_53)
      | ~ l1_pre_topc(B_52)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_253,plain,(
    ! [D_51,B_52] :
      ( m1_pre_topc(D_51,B_52)
      | g1_pre_topc(u1_struct_0(D_51),u1_pre_topc(D_51)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_51)
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_52)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_251])).

tff(c_260,plain,(
    ! [D_55,B_56] :
      ( m1_pre_topc(D_55,B_56)
      | g1_pre_topc(u1_struct_0(D_55),u1_pre_topc(D_55)) != '#skF_2'
      | g1_pre_topc(u1_struct_0(B_56),u1_pre_topc(B_56)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_55)
      | ~ l1_pre_topc(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_18,c_16,c_253])).

tff(c_264,plain,(
    ! [B_56] :
      ( m1_pre_topc('#skF_2',B_56)
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) != '#skF_2'
      | g1_pre_topc(u1_struct_0(B_56),u1_pre_topc(B_56)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_260])).

tff(c_272,plain,(
    ! [B_56] :
      ( m1_pre_topc('#skF_2',B_56)
      | g1_pre_topc(u1_struct_0(B_56),u1_pre_topc(B_56)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_209,c_264])).

tff(c_337,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_272])).

tff(c_339,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_337])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_339])).

tff(c_342,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_351,plain,(
    ! [A_63] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_63),u1_pre_topc(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_354,plain,
    ( v1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_351])).

tff(c_356,plain,(
    v1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_354])).

tff(c_393,plain,(
    ! [D_66,B_67,C_68,A_69] :
      ( D_66 = B_67
      | g1_pre_topc(C_68,D_66) != g1_pre_topc(A_69,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_401,plain,(
    ! [D_66,C_68] :
      ( u1_pre_topc('#skF_3') = D_66
      | g1_pre_topc(C_68,D_66) != '#skF_2'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_393])).

tff(c_447,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_450,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_447])).

tff(c_454,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_450])).

tff(c_457,plain,(
    ! [D_80,C_81] :
      ( u1_pre_topc('#skF_3') = D_80
      | g1_pre_topc(C_81,D_80) != '#skF_2' ) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_474,plain,(
    ! [A_82] :
      ( u1_pre_topc(A_82) = u1_pre_topc('#skF_3')
      | A_82 != '#skF_2'
      | ~ v1_pre_topc(A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_457])).

tff(c_477,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_356,c_474])).

tff(c_483,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_477])).

tff(c_491,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = '#skF_2'
    | ~ v1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_2])).

tff(c_506,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_356,c_491])).

tff(c_456,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_411,plain,(
    ! [C_72,A_73,D_74,B_75] :
      ( C_72 = A_73
      | g1_pre_topc(C_72,D_74) != g1_pre_topc(A_73,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_419,plain,(
    ! [C_72,D_74] :
      ( u1_struct_0('#skF_3') = C_72
      | g1_pre_topc(C_72,D_74) != '#skF_2'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_411])).

tff(c_541,plain,(
    ! [C_87,D_88] :
      ( u1_struct_0('#skF_3') = C_87
      | g1_pre_topc(C_87,D_88) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_419])).

tff(c_551,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_541])).

tff(c_343,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_514,plain,(
    ! [D_83,B_84,C_85,A_86] :
      ( m1_pre_topc(D_83,B_84)
      | ~ m1_pre_topc(C_85,A_86)
      | g1_pre_topc(u1_struct_0(D_83),u1_pre_topc(D_83)) != g1_pre_topc(u1_struct_0(C_85),u1_pre_topc(C_85))
      | g1_pre_topc(u1_struct_0(B_84),u1_pre_topc(B_84)) != g1_pre_topc(u1_struct_0(A_86),u1_pre_topc(A_86))
      | ~ l1_pre_topc(D_83)
      | ~ l1_pre_topc(C_85)
      | ~ l1_pre_topc(B_84)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_516,plain,(
    ! [D_83,B_84] :
      ( m1_pre_topc(D_83,B_84)
      | g1_pre_topc(u1_struct_0(D_83),u1_pre_topc(D_83)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | g1_pre_topc(u1_struct_0(B_84),u1_pre_topc(B_84)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_83)
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(B_84)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_343,c_514])).

tff(c_519,plain,(
    ! [D_83,B_84] :
      ( m1_pre_topc(D_83,B_84)
      | g1_pre_topc(u1_struct_0(D_83),u1_pre_topc(D_83)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3'))
      | g1_pre_topc(u1_struct_0(B_84),u1_pre_topc(B_84)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_83)
      | ~ l1_pre_topc(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_483,c_516])).

tff(c_612,plain,(
    ! [D_93,B_94] :
      ( m1_pre_topc(D_93,B_94)
      | g1_pre_topc(u1_struct_0(D_93),u1_pre_topc(D_93)) != '#skF_2'
      | g1_pre_topc(u1_struct_0(B_94),u1_pre_topc(B_94)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(D_93)
      | ~ l1_pre_topc(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_551,c_519])).

tff(c_620,plain,(
    ! [B_94] :
      ( m1_pre_topc('#skF_3',B_94)
      | g1_pre_topc(u1_struct_0(B_94),u1_pre_topc(B_94)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_612])).

tff(c_627,plain,(
    ! [B_94] :
      ( m1_pre_topc('#skF_3',B_94)
      | g1_pre_topc(u1_struct_0(B_94),u1_pre_topc(B_94)) != g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_620])).

tff(c_679,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_627])).

tff(c_681,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_679])).

tff(c_683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.34  
% 2.71/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.35  %$ m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.71/1.35  
% 2.71/1.35  %Foreground sorts:
% 2.71/1.35  
% 2.71/1.35  
% 2.71/1.35  %Background operators:
% 2.71/1.35  
% 2.71/1.35  
% 2.71/1.35  %Foreground operators:
% 2.71/1.35  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.71/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.35  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.71/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.71/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.35  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.71/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.71/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.71/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.71/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.35  
% 2.71/1.36  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 2.71/1.36  tff(f_43, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 2.71/1.36  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.71/1.36  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.71/1.36  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.71/1.36  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 2.71/1.36  tff(c_28, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.36  tff(c_35, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 2.71/1.36  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.36  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.36  tff(c_16, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.36  tff(c_20, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.36  tff(c_18, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.36  tff(c_42, plain, (![A_30]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_30), u1_pre_topc(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.36  tff(c_45, plain, (v1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_42])).
% 2.71/1.36  tff(c_47, plain, (v1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_45])).
% 2.71/1.36  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.36  tff(c_4, plain, (![A_2]: (m1_subset_1(u1_pre_topc(A_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2)))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.36  tff(c_84, plain, (![C_33, A_34, D_35, B_36]: (C_33=A_34 | g1_pre_topc(C_33, D_35)!=g1_pre_topc(A_34, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.36  tff(c_92, plain, (![C_33, D_35]: (u1_struct_0('#skF_3')=C_33 | g1_pre_topc(C_33, D_35)!='#skF_2' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_84])).
% 2.71/1.36  tff(c_98, plain, (~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_92])).
% 2.71/1.36  tff(c_101, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_98])).
% 2.71/1.36  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_101])).
% 2.71/1.36  tff(c_108, plain, (![C_39, D_40]: (u1_struct_0('#skF_3')=C_39 | g1_pre_topc(C_39, D_40)!='#skF_2')), inference(splitRight, [status(thm)], [c_92])).
% 2.71/1.36  tff(c_118, plain, (![A_41]: (u1_struct_0(A_41)=u1_struct_0('#skF_3') | A_41!='#skF_2' | ~v1_pre_topc(A_41) | ~l1_pre_topc(A_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_108])).
% 2.71/1.36  tff(c_121, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_47, c_118])).
% 2.71/1.36  tff(c_127, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_121])).
% 2.71/1.36  tff(c_132, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_2' | ~v1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_127, c_2])).
% 2.71/1.36  tff(c_145, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_47, c_132])).
% 2.71/1.36  tff(c_107, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_92])).
% 2.71/1.36  tff(c_157, plain, (![D_42, B_43, C_44, A_45]: (D_42=B_43 | g1_pre_topc(C_44, D_42)!=g1_pre_topc(A_45, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.36  tff(c_165, plain, (![D_42, C_44]: (u1_pre_topc('#skF_3')=D_42 | g1_pre_topc(C_44, D_42)!='#skF_2' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_157])).
% 2.71/1.36  tff(c_199, plain, (![D_48, C_49]: (u1_pre_topc('#skF_3')=D_48 | g1_pre_topc(C_49, D_48)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_165])).
% 2.71/1.36  tff(c_209, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_199])).
% 2.71/1.36  tff(c_34, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.71/1.36  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_35, c_34])).
% 2.71/1.36  tff(c_251, plain, (![D_51, B_52, C_53, A_54]: (m1_pre_topc(D_51, B_52) | ~m1_pre_topc(C_53, A_54) | g1_pre_topc(u1_struct_0(D_51), u1_pre_topc(D_51))!=g1_pre_topc(u1_struct_0(C_53), u1_pre_topc(C_53)) | g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52))!=g1_pre_topc(u1_struct_0(A_54), u1_pre_topc(A_54)) | ~l1_pre_topc(D_51) | ~l1_pre_topc(C_53) | ~l1_pre_topc(B_52) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.71/1.36  tff(c_253, plain, (![D_51, B_52]: (m1_pre_topc(D_51, B_52) | g1_pre_topc(u1_struct_0(D_51), u1_pre_topc(D_51))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_51) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(B_52) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_251])).
% 2.71/1.36  tff(c_260, plain, (![D_55, B_56]: (m1_pre_topc(D_55, B_56) | g1_pre_topc(u1_struct_0(D_55), u1_pre_topc(D_55))!='#skF_2' | g1_pre_topc(u1_struct_0(B_56), u1_pre_topc(B_56))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_55) | ~l1_pre_topc(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_18, c_16, c_253])).
% 2.71/1.36  tff(c_264, plain, (![B_56]: (m1_pre_topc('#skF_2', B_56) | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))!='#skF_2' | g1_pre_topc(u1_struct_0(B_56), u1_pre_topc(B_56))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(B_56))), inference(superposition, [status(thm), theory('equality')], [c_127, c_260])).
% 2.71/1.36  tff(c_272, plain, (![B_56]: (m1_pre_topc('#skF_2', B_56) | g1_pre_topc(u1_struct_0(B_56), u1_pre_topc(B_56))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_209, c_264])).
% 2.71/1.36  tff(c_337, plain, (m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_272])).
% 2.71/1.36  tff(c_339, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_337])).
% 2.71/1.36  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_339])).
% 2.71/1.36  tff(c_342, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 2.71/1.36  tff(c_351, plain, (![A_63]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_63), u1_pre_topc(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.71/1.36  tff(c_354, plain, (v1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_351])).
% 2.71/1.36  tff(c_356, plain, (v1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_354])).
% 2.71/1.36  tff(c_393, plain, (![D_66, B_67, C_68, A_69]: (D_66=B_67 | g1_pre_topc(C_68, D_66)!=g1_pre_topc(A_69, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.36  tff(c_401, plain, (![D_66, C_68]: (u1_pre_topc('#skF_3')=D_66 | g1_pre_topc(C_68, D_66)!='#skF_2' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_393])).
% 2.71/1.36  tff(c_447, plain, (~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_401])).
% 2.71/1.36  tff(c_450, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4, c_447])).
% 2.71/1.36  tff(c_454, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_450])).
% 2.71/1.36  tff(c_457, plain, (![D_80, C_81]: (u1_pre_topc('#skF_3')=D_80 | g1_pre_topc(C_81, D_80)!='#skF_2')), inference(splitRight, [status(thm)], [c_401])).
% 2.71/1.36  tff(c_474, plain, (![A_82]: (u1_pre_topc(A_82)=u1_pre_topc('#skF_3') | A_82!='#skF_2' | ~v1_pre_topc(A_82) | ~l1_pre_topc(A_82))), inference(superposition, [status(thm), theory('equality')], [c_2, c_457])).
% 2.71/1.36  tff(c_477, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_356, c_474])).
% 2.71/1.36  tff(c_483, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_477])).
% 2.71/1.36  tff(c_491, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3'))='#skF_2' | ~v1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_483, c_2])).
% 2.71/1.36  tff(c_506, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_356, c_491])).
% 2.71/1.36  tff(c_456, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_401])).
% 2.71/1.36  tff(c_411, plain, (![C_72, A_73, D_74, B_75]: (C_72=A_73 | g1_pre_topc(C_72, D_74)!=g1_pre_topc(A_73, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.36  tff(c_419, plain, (![C_72, D_74]: (u1_struct_0('#skF_3')=C_72 | g1_pre_topc(C_72, D_74)!='#skF_2' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_411])).
% 2.71/1.36  tff(c_541, plain, (![C_87, D_88]: (u1_struct_0('#skF_3')=C_87 | g1_pre_topc(C_87, D_88)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_419])).
% 2.71/1.36  tff(c_551, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_506, c_541])).
% 2.71/1.36  tff(c_343, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 2.71/1.36  tff(c_514, plain, (![D_83, B_84, C_85, A_86]: (m1_pre_topc(D_83, B_84) | ~m1_pre_topc(C_85, A_86) | g1_pre_topc(u1_struct_0(D_83), u1_pre_topc(D_83))!=g1_pre_topc(u1_struct_0(C_85), u1_pre_topc(C_85)) | g1_pre_topc(u1_struct_0(B_84), u1_pre_topc(B_84))!=g1_pre_topc(u1_struct_0(A_86), u1_pre_topc(A_86)) | ~l1_pre_topc(D_83) | ~l1_pre_topc(C_85) | ~l1_pre_topc(B_84) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.71/1.36  tff(c_516, plain, (![D_83, B_84]: (m1_pre_topc(D_83, B_84) | g1_pre_topc(u1_struct_0(D_83), u1_pre_topc(D_83))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | g1_pre_topc(u1_struct_0(B_84), u1_pre_topc(B_84))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_83) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(B_84) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_343, c_514])).
% 2.71/1.36  tff(c_519, plain, (![D_83, B_84]: (m1_pre_topc(D_83, B_84) | g1_pre_topc(u1_struct_0(D_83), u1_pre_topc(D_83))!=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_3')) | g1_pre_topc(u1_struct_0(B_84), u1_pre_topc(B_84))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_83) | ~l1_pre_topc(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_483, c_516])).
% 2.71/1.36  tff(c_612, plain, (![D_93, B_94]: (m1_pre_topc(D_93, B_94) | g1_pre_topc(u1_struct_0(D_93), u1_pre_topc(D_93))!='#skF_2' | g1_pre_topc(u1_struct_0(B_94), u1_pre_topc(B_94))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(D_93) | ~l1_pre_topc(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_551, c_519])).
% 2.71/1.36  tff(c_620, plain, (![B_94]: (m1_pre_topc('#skF_3', B_94) | g1_pre_topc(u1_struct_0(B_94), u1_pre_topc(B_94))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(B_94))), inference(superposition, [status(thm), theory('equality')], [c_16, c_612])).
% 2.71/1.36  tff(c_627, plain, (![B_94]: (m1_pre_topc('#skF_3', B_94) | g1_pre_topc(u1_struct_0(B_94), u1_pre_topc(B_94))!=g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')) | ~l1_pre_topc(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_620])).
% 2.71/1.36  tff(c_679, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(reflexivity, [status(thm), theory('equality')], [c_627])).
% 2.71/1.36  tff(c_681, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_679])).
% 2.71/1.36  tff(c_683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_681])).
% 2.71/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.36  
% 2.71/1.36  Inference rules
% 2.71/1.36  ----------------------
% 2.71/1.36  #Ref     : 12
% 2.71/1.36  #Sup     : 134
% 2.71/1.36  #Fact    : 0
% 2.71/1.36  #Define  : 0
% 2.71/1.36  #Split   : 9
% 2.71/1.36  #Chain   : 0
% 2.71/1.36  #Close   : 0
% 2.71/1.36  
% 2.71/1.37  Ordering : KBO
% 2.71/1.37  
% 2.71/1.37  Simplification rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Subsume      : 30
% 2.71/1.37  #Demod        : 155
% 2.71/1.37  #Tautology    : 67
% 2.71/1.37  #SimpNegUnit  : 4
% 2.71/1.37  #BackRed      : 2
% 2.71/1.37  
% 2.71/1.37  #Partial instantiations: 0
% 2.71/1.37  #Strategies tried      : 1
% 2.71/1.37  
% 2.71/1.37  Timing (in seconds)
% 2.71/1.37  ----------------------
% 2.71/1.37  Preprocessing        : 0.28
% 2.71/1.37  Parsing              : 0.16
% 2.71/1.37  CNF conversion       : 0.02
% 2.71/1.37  Main loop            : 0.32
% 2.71/1.37  Inferencing          : 0.11
% 2.71/1.37  Reduction            : 0.10
% 2.71/1.37  Demodulation         : 0.06
% 2.71/1.37  BG Simplification    : 0.02
% 2.71/1.37  Subsumption          : 0.07
% 2.71/1.37  Abstraction          : 0.02
% 2.71/1.37  MUC search           : 0.00
% 2.71/1.37  Cooper               : 0.00
% 2.71/1.37  Total                : 0.64
% 2.71/1.37  Index Insertion      : 0.00
% 2.71/1.37  Index Deletion       : 0.00
% 2.71/1.37  Index Matching       : 0.00
% 2.71/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
