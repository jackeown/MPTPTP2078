%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:57 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 551 expanded)
%              Number of leaves         :   22 ( 192 expanded)
%              Depth                    :   16
%              Number of atoms          :  243 (1970 expanded)
%              Number of equality atoms :   52 ( 549 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                        & C = D
                        & v3_tex_2(C,A) )
                     => v3_tex_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & C = D
                      & v2_tex_2(C,A) )
                   => v2_tex_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tex_2)).

tff(c_26,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22,plain,(
    ~ v3_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_37,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_89,plain,(
    ! [A_59,B_60] :
      ( '#skF_1'(A_59,B_60) != B_60
      | v3_tex_2(B_60,A_59)
      | ~ v2_tex_2(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_95,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_89])).

tff(c_101,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_95])).

tff(c_102,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_101])).

tff(c_103,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24,plain,(
    v3_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_57,plain,(
    ! [B_49,A_50] :
      ( v2_tex_2(B_49,A_50)
      | ~ v3_tex_2(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,
    ( v2_tex_2('#skF_4','#skF_2')
    | ~ v3_tex_2('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_66,plain,(
    v2_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_24,c_60])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    ! [D_45,B_46,C_47,A_48] :
      ( D_45 = B_46
      | g1_pre_topc(C_47,D_45) != g1_pre_topc(A_48,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,(
    ! [B_55,A_56] :
      ( u1_pre_topc('#skF_2') = B_55
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_56,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_52])).

tff(c_83,plain,(
    ! [A_1] :
      ( u1_pre_topc(A_1) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_106,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_83])).

tff(c_108,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_106])).

tff(c_74,plain,(
    ! [C_51,A_52,D_53,B_54] :
      ( C_51 = A_52
      | g1_pre_topc(C_51,D_53) != g1_pre_topc(A_52,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    ! [C_51,D_53] :
      ( u1_struct_0('#skF_2') = C_51
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_51,D_53)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_117,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_130,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_117])).

tff(c_124,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_2])).

tff(c_128,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_124])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_128])).

tff(c_132,plain,(
    ! [C_51,D_53] :
      ( u1_struct_0('#skF_2') = C_51
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_51,D_53) ) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_183,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_132])).

tff(c_455,plain,(
    ! [D_90,B_91,A_92] :
      ( v2_tex_2(D_90,B_91)
      | ~ v2_tex_2(D_90,A_92)
      | g1_pre_topc(u1_struct_0(B_91),u1_pre_topc(B_91)) != g1_pre_topc(u1_struct_0(A_92),u1_pre_topc(A_92))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(B_91)))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(B_91)
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_459,plain,(
    ! [D_90,B_91] :
      ( v2_tex_2(D_90,B_91)
      | ~ v2_tex_2(D_90,'#skF_2')
      | g1_pre_topc(u1_struct_0(B_91),u1_pre_topc(B_91)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(B_91)))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc(B_91)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_455])).

tff(c_467,plain,(
    ! [D_90,B_91] :
      ( v2_tex_2(D_90,B_91)
      | ~ v2_tex_2(D_90,'#skF_2')
      | g1_pre_topc(u1_struct_0(B_91),u1_pre_topc(B_91)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(B_91)))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_183,c_108,c_459])).

tff(c_523,plain,(
    ! [D_90] :
      ( v2_tex_2(D_90,'#skF_3')
      | ~ v2_tex_2(D_90,'#skF_2')
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_467])).

tff(c_535,plain,(
    ! [D_101] :
      ( v2_tex_2(D_101,'#skF_3')
      | ~ v2_tex_2(D_101,'#skF_2')
      | ~ m1_subset_1(D_101,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_523])).

tff(c_545,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_37,c_535])).

tff(c_552,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_545])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_552])).

tff(c_556,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_14,plain,(
    ! [A_8,B_14] :
      ( m1_subset_1('#skF_1'(A_8,B_14),k1_zfmisc_1(u1_struct_0(A_8)))
      | v3_tex_2(B_14,A_8)
      | ~ v2_tex_2(B_14,A_8)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_84,plain,(
    ! [A_57,B_58] :
      ( u1_struct_0('#skF_2') = A_57
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_88,plain,(
    ! [A_1] :
      ( u1_struct_0(A_1) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_84])).

tff(c_559,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_88])).

tff(c_561,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_559])).

tff(c_555,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_594,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(B_103,'#skF_1'(A_104,B_103))
      | v3_tex_2(B_103,A_104)
      | ~ v2_tex_2(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_598,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_594])).

tff(c_603,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_556,c_598])).

tff(c_604,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_603])).

tff(c_828,plain,(
    ! [C_122,B_123,A_124] :
      ( C_122 = B_123
      | ~ r1_tarski(B_123,C_122)
      | ~ v2_tex_2(C_122,A_124)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ v3_tex_2(B_123,A_124)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_830,plain,(
    ! [A_124] :
      ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
      | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),A_124)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ v3_tex_2('#skF_4',A_124)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_604,c_828])).

tff(c_834,plain,(
    ! [A_125] :
      ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),A_125)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ v3_tex_2('#skF_4',A_125)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_830])).

tff(c_841,plain,
    ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_834])).

tff(c_847,plain,
    ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_37,c_561,c_24,c_841])).

tff(c_848,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_847])).

tff(c_851,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_848])).

tff(c_854,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_37,c_556,c_851])).

tff(c_856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_854])).

tff(c_857,plain,(
    ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_847])).

tff(c_659,plain,(
    ! [A_109,B_110] :
      ( v2_tex_2('#skF_1'(A_109,B_110),A_109)
      | v3_tex_2(B_110,A_109)
      | ~ v2_tex_2(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_663,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_659])).

tff(c_668,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_556,c_663])).

tff(c_669,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_668])).

tff(c_858,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_847])).

tff(c_584,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_2])).

tff(c_592,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_584])).

tff(c_572,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_561,c_28])).

tff(c_4,plain,(
    ! [D_7,B_3,C_6,A_2] :
      ( D_7 = B_3
      | g1_pre_topc(C_6,D_7) != g1_pre_topc(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_618,plain,(
    ! [D_7,C_6] :
      ( u1_pre_topc('#skF_2') = D_7
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_6,D_7)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_4])).

tff(c_624,plain,(
    ! [D_7,C_6] :
      ( u1_pre_topc('#skF_2') = D_7
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_6,D_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_618])).

tff(c_639,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_624])).

tff(c_862,plain,(
    ! [D_126,B_127,A_128] :
      ( v2_tex_2(D_126,B_127)
      | ~ v2_tex_2(D_126,A_128)
      | g1_pre_topc(u1_struct_0(B_127),u1_pre_topc(B_127)) != g1_pre_topc(u1_struct_0(A_128),u1_pre_topc(A_128))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(B_127)))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(B_127)
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_868,plain,(
    ! [D_126,A_128] :
      ( v2_tex_2(D_126,'#skF_2')
      | ~ v2_tex_2(D_126,A_128)
      | g1_pre_topc(u1_struct_0(A_128),u1_pre_topc(A_128)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_862])).

tff(c_876,plain,(
    ! [D_126,A_128] :
      ( v2_tex_2(D_126,'#skF_2')
      | ~ v2_tex_2(D_126,A_128)
      | g1_pre_topc(u1_struct_0(A_128),u1_pre_topc(A_128)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_561,c_639,c_868])).

tff(c_1030,plain,(
    ! [D_126] :
      ( v2_tex_2(D_126,'#skF_2')
      | ~ v2_tex_2(D_126,'#skF_3')
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_876])).

tff(c_1042,plain,(
    ! [D_139] :
      ( v2_tex_2(D_139,'#skF_2')
      | ~ v2_tex_2(D_139,'#skF_3')
      | ~ m1_subset_1(D_139,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1030])).

tff(c_1045,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_858,c_1042])).

tff(c_1058,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_1045])).

tff(c_1060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_857,c_1058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.77  
% 3.02/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.77  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.02/1.77  
% 3.02/1.77  %Foreground sorts:
% 3.02/1.77  
% 3.02/1.77  
% 3.02/1.77  %Background operators:
% 3.02/1.77  
% 3.02/1.77  
% 3.02/1.77  %Foreground operators:
% 3.02/1.77  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.02/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.77  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.02/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.02/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.77  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.77  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.02/1.77  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.02/1.77  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.77  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.02/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.77  
% 3.02/1.79  tff(f_95, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v3_tex_2(C, A)) => v3_tex_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tex_2)).
% 3.02/1.79  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.02/1.79  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.02/1.79  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.02/1.79  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tex_2(C, A)) => v2_tex_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tex_2)).
% 3.02/1.79  tff(c_26, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.02/1.79  tff(c_22, plain, (~v3_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.02/1.79  tff(c_38, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22])).
% 3.02/1.79  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.02/1.79  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.02/1.79  tff(c_37, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 3.02/1.79  tff(c_89, plain, (![A_59, B_60]: ('#skF_1'(A_59, B_60)!=B_60 | v3_tex_2(B_60, A_59) | ~v2_tex_2(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.79  tff(c_95, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_37, c_89])).
% 3.02/1.79  tff(c_101, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_95])).
% 3.02/1.79  tff(c_102, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_101])).
% 3.02/1.79  tff(c_103, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_102])).
% 3.02/1.79  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.02/1.79  tff(c_24, plain, (v3_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.02/1.79  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.02/1.79  tff(c_57, plain, (![B_49, A_50]: (v2_tex_2(B_49, A_50) | ~v3_tex_2(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.79  tff(c_60, plain, (v2_tex_2('#skF_4', '#skF_2') | ~v3_tex_2('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_57])).
% 3.02/1.79  tff(c_66, plain, (v2_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_24, c_60])).
% 3.02/1.79  tff(c_2, plain, (![A_1]: (m1_subset_1(u1_pre_topc(A_1), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1)))) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.79  tff(c_28, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.02/1.79  tff(c_52, plain, (![D_45, B_46, C_47, A_48]: (D_45=B_46 | g1_pre_topc(C_47, D_45)!=g1_pre_topc(A_48, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.02/1.79  tff(c_79, plain, (![B_55, A_56]: (u1_pre_topc('#skF_2')=B_55 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_56, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_52])).
% 3.02/1.79  tff(c_83, plain, (![A_1]: (u1_pre_topc(A_1)=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_79])).
% 3.02/1.79  tff(c_106, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_83])).
% 3.02/1.79  tff(c_108, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_106])).
% 3.02/1.79  tff(c_74, plain, (![C_51, A_52, D_53, B_54]: (C_51=A_52 | g1_pre_topc(C_51, D_53)!=g1_pre_topc(A_52, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.02/1.79  tff(c_78, plain, (![C_51, D_53]: (u1_struct_0('#skF_2')=C_51 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_51, D_53) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_74])).
% 3.02/1.79  tff(c_117, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_78])).
% 3.02/1.79  tff(c_130, plain, (~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_117])).
% 3.02/1.79  tff(c_124, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_108, c_2])).
% 3.02/1.79  tff(c_128, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_124])).
% 3.02/1.79  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_128])).
% 3.02/1.79  tff(c_132, plain, (![C_51, D_53]: (u1_struct_0('#skF_2')=C_51 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_51, D_53))), inference(splitRight, [status(thm)], [c_78])).
% 3.02/1.79  tff(c_183, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_132])).
% 3.02/1.79  tff(c_455, plain, (![D_90, B_91, A_92]: (v2_tex_2(D_90, B_91) | ~v2_tex_2(D_90, A_92) | g1_pre_topc(u1_struct_0(B_91), u1_pre_topc(B_91))!=g1_pre_topc(u1_struct_0(A_92), u1_pre_topc(A_92)) | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0(B_91))) | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(B_91) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.02/1.79  tff(c_459, plain, (![D_90, B_91]: (v2_tex_2(D_90, B_91) | ~v2_tex_2(D_90, '#skF_2') | g1_pre_topc(u1_struct_0(B_91), u1_pre_topc(B_91))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')) | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0(B_91))) | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc(B_91) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_455])).
% 3.02/1.79  tff(c_467, plain, (![D_90, B_91]: (v2_tex_2(D_90, B_91) | ~v2_tex_2(D_90, '#skF_2') | g1_pre_topc(u1_struct_0(B_91), u1_pre_topc(B_91))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0(B_91))) | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_183, c_108, c_459])).
% 3.02/1.79  tff(c_523, plain, (![D_90]: (v2_tex_2(D_90, '#skF_3') | ~v2_tex_2(D_90, '#skF_2') | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_90, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_467])).
% 3.02/1.79  tff(c_535, plain, (![D_101]: (v2_tex_2(D_101, '#skF_3') | ~v2_tex_2(D_101, '#skF_2') | ~m1_subset_1(D_101, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_523])).
% 3.02/1.79  tff(c_545, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_37, c_535])).
% 3.02/1.79  tff(c_552, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_545])).
% 3.02/1.79  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_552])).
% 3.02/1.79  tff(c_556, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_102])).
% 3.02/1.79  tff(c_14, plain, (![A_8, B_14]: (m1_subset_1('#skF_1'(A_8, B_14), k1_zfmisc_1(u1_struct_0(A_8))) | v3_tex_2(B_14, A_8) | ~v2_tex_2(B_14, A_8) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.79  tff(c_84, plain, (![A_57, B_58]: (u1_struct_0('#skF_2')=A_57 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(superposition, [status(thm), theory('equality')], [c_28, c_74])).
% 3.02/1.79  tff(c_88, plain, (![A_1]: (u1_struct_0(A_1)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~l1_pre_topc(A_1))), inference(resolution, [status(thm)], [c_2, c_84])).
% 3.02/1.79  tff(c_559, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_88])).
% 3.02/1.79  tff(c_561, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_559])).
% 3.02/1.79  tff(c_555, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_102])).
% 3.02/1.79  tff(c_594, plain, (![B_103, A_104]: (r1_tarski(B_103, '#skF_1'(A_104, B_103)) | v3_tex_2(B_103, A_104) | ~v2_tex_2(B_103, A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.79  tff(c_598, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_37, c_594])).
% 3.02/1.79  tff(c_603, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_556, c_598])).
% 3.02/1.79  tff(c_604, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_603])).
% 3.02/1.79  tff(c_828, plain, (![C_122, B_123, A_124]: (C_122=B_123 | ~r1_tarski(B_123, C_122) | ~v2_tex_2(C_122, A_124) | ~m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0(A_124))) | ~v3_tex_2(B_123, A_124) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.79  tff(c_830, plain, (![A_124]: ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), A_124) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_124))) | ~v3_tex_2('#skF_4', A_124) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(resolution, [status(thm)], [c_604, c_828])).
% 3.02/1.79  tff(c_834, plain, (![A_125]: (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), A_125) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_125))) | ~v3_tex_2('#skF_4', A_125) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(negUnitSimplification, [status(thm)], [c_555, c_830])).
% 3.02/1.79  tff(c_841, plain, (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_561, c_834])).
% 3.02/1.79  tff(c_847, plain, (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_37, c_561, c_24, c_841])).
% 3.02/1.79  tff(c_848, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_847])).
% 3.02/1.79  tff(c_851, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_848])).
% 3.02/1.79  tff(c_854, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_37, c_556, c_851])).
% 3.02/1.79  tff(c_856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_854])).
% 3.02/1.79  tff(c_857, plain, (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_847])).
% 3.02/1.79  tff(c_659, plain, (![A_109, B_110]: (v2_tex_2('#skF_1'(A_109, B_110), A_109) | v3_tex_2(B_110, A_109) | ~v2_tex_2(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.79  tff(c_663, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_37, c_659])).
% 3.02/1.79  tff(c_668, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_556, c_663])).
% 3.02/1.79  tff(c_669, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_668])).
% 3.02/1.79  tff(c_858, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_847])).
% 3.02/1.79  tff(c_584, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_561, c_2])).
% 3.02/1.79  tff(c_592, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_584])).
% 3.02/1.79  tff(c_572, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_561, c_28])).
% 3.02/1.79  tff(c_4, plain, (![D_7, B_3, C_6, A_2]: (D_7=B_3 | g1_pre_topc(C_6, D_7)!=g1_pre_topc(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.02/1.79  tff(c_618, plain, (![D_7, C_6]: (u1_pre_topc('#skF_2')=D_7 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_6, D_7) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_572, c_4])).
% 3.02/1.79  tff(c_624, plain, (![D_7, C_6]: (u1_pre_topc('#skF_2')=D_7 | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=g1_pre_topc(C_6, D_7))), inference(demodulation, [status(thm), theory('equality')], [c_592, c_618])).
% 3.02/1.79  tff(c_639, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_624])).
% 3.02/1.79  tff(c_862, plain, (![D_126, B_127, A_128]: (v2_tex_2(D_126, B_127) | ~v2_tex_2(D_126, A_128) | g1_pre_topc(u1_struct_0(B_127), u1_pre_topc(B_127))!=g1_pre_topc(u1_struct_0(A_128), u1_pre_topc(A_128)) | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0(B_127))) | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(B_127) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.02/1.79  tff(c_868, plain, (![D_126, A_128]: (v2_tex_2(D_126, '#skF_2') | ~v2_tex_2(D_126, A_128) | g1_pre_topc(u1_struct_0(A_128), u1_pre_topc(A_128))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')) | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_128))), inference(superposition, [status(thm), theory('equality')], [c_561, c_862])).
% 3.02/1.79  tff(c_876, plain, (![D_126, A_128]: (v2_tex_2(D_126, '#skF_2') | ~v2_tex_2(D_126, A_128) | g1_pre_topc(u1_struct_0(A_128), u1_pre_topc(A_128))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_561, c_639, c_868])).
% 3.02/1.79  tff(c_1030, plain, (![D_126]: (v2_tex_2(D_126, '#skF_2') | ~v2_tex_2(D_126, '#skF_3') | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_126, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_876])).
% 3.02/1.79  tff(c_1042, plain, (![D_139]: (v2_tex_2(D_139, '#skF_2') | ~v2_tex_2(D_139, '#skF_3') | ~m1_subset_1(D_139, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1030])).
% 3.02/1.79  tff(c_1045, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_858, c_1042])).
% 3.02/1.79  tff(c_1058, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_669, c_1045])).
% 3.02/1.79  tff(c_1060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_857, c_1058])).
% 3.02/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.79  
% 3.02/1.79  Inference rules
% 3.02/1.79  ----------------------
% 3.02/1.79  #Ref     : 16
% 3.02/1.79  #Sup     : 181
% 3.02/1.79  #Fact    : 0
% 3.02/1.79  #Define  : 0
% 3.02/1.79  #Split   : 5
% 3.02/1.79  #Chain   : 0
% 3.02/1.79  #Close   : 0
% 3.02/1.79  
% 3.02/1.79  Ordering : KBO
% 3.02/1.79  
% 3.02/1.79  Simplification rules
% 3.02/1.79  ----------------------
% 3.02/1.79  #Subsume      : 41
% 3.02/1.79  #Demod        : 226
% 3.02/1.79  #Tautology    : 68
% 3.02/1.79  #SimpNegUnit  : 22
% 3.02/1.79  #BackRed      : 15
% 3.02/1.79  
% 3.02/1.79  #Partial instantiations: 0
% 3.02/1.79  #Strategies tried      : 1
% 3.02/1.79  
% 3.02/1.79  Timing (in seconds)
% 3.02/1.79  ----------------------
% 3.02/1.80  Preprocessing        : 0.31
% 3.02/1.80  Parsing              : 0.15
% 3.02/1.80  CNF conversion       : 0.02
% 3.02/1.80  Main loop            : 0.40
% 3.02/1.80  Inferencing          : 0.14
% 3.02/1.80  Reduction            : 0.13
% 3.02/1.80  Demodulation         : 0.09
% 3.02/1.80  BG Simplification    : 0.02
% 3.02/1.80  Subsumption          : 0.08
% 3.02/1.80  Abstraction          : 0.02
% 3.02/1.80  MUC search           : 0.00
% 3.02/1.80  Cooper               : 0.00
% 3.02/1.80  Total                : 0.76
% 3.02/1.80  Index Insertion      : 0.00
% 3.02/1.80  Index Deletion       : 0.00
% 3.02/1.80  Index Matching       : 0.00
% 3.02/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
