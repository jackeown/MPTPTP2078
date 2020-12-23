%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1877+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:36 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 738 expanded)
%              Number of leaves         :   22 ( 250 expanded)
%              Depth                    :   16
%              Number of atoms          :  243 (2525 expanded)
%              Number of equality atoms :   52 ( 776 expanded)
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

tff(f_94,negated_conjecture,(
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

tff(f_42,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_74,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    ~ v3_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

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
    inference(cnfTransformation,[status(thm)],[f_42])).

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
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    v3_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_57,plain,(
    ! [B_49,A_50] :
      ( v2_tex_2(B_49,A_50)
      | ~ v3_tex_2(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,
    ( v2_tex_2('#skF_4','#skF_2')
    | ~ v3_tex_2('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_66,plain,(
    v2_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_24,c_60])).

tff(c_14,plain,(
    ! [A_11] :
      ( m1_subset_1(u1_pre_topc(A_11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    ! [C_45,A_46,D_47,B_48] :
      ( C_45 = A_46
      | g1_pre_topc(C_45,D_47) != g1_pre_topc(A_46,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_79,plain,(
    ! [A_55,B_56] :
      ( u1_struct_0('#skF_2') = A_55
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_52])).

tff(c_83,plain,(
    ! [A_11] :
      ( u1_struct_0(A_11) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_11),u1_pre_topc(A_11)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_106,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_83])).

tff(c_108,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_106])).

tff(c_74,plain,(
    ! [D_51,B_52,C_53,A_54] :
      ( D_51 = B_52
      | g1_pre_topc(C_53,D_51) != g1_pre_topc(A_54,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    ! [D_51,C_53] :
      ( u1_pre_topc('#skF_2') = D_51
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_53,D_51)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_117,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_142,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_117])).

tff(c_132,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_14])).

tff(c_140,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_132])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_140])).

tff(c_144,plain,(
    ! [D_51,C_53] :
      ( u1_pre_topc('#skF_2') = D_51
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_53,D_51) ) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_206,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_144])).

tff(c_462,plain,(
    ! [D_90,B_91,A_92] :
      ( v2_tex_2(D_90,B_91)
      | ~ v2_tex_2(D_90,A_92)
      | g1_pre_topc(u1_struct_0(B_91),u1_pre_topc(B_91)) != g1_pre_topc(u1_struct_0(A_92),u1_pre_topc(A_92))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(B_91)))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(B_91)
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_466,plain,(
    ! [D_90,B_91] :
      ( v2_tex_2(D_90,B_91)
      | ~ v2_tex_2(D_90,'#skF_2')
      | g1_pre_topc(u1_struct_0(B_91),u1_pre_topc(B_91)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(B_91)))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc(B_91)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_462])).

tff(c_474,plain,(
    ! [D_90,B_91] :
      ( v2_tex_2(D_90,B_91)
      | ~ v2_tex_2(D_90,'#skF_2')
      | g1_pre_topc(u1_struct_0(B_91),u1_pre_topc(B_91)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0(B_91)))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_108,c_108,c_466])).

tff(c_530,plain,(
    ! [D_90] :
      ( v2_tex_2(D_90,'#skF_3')
      | ~ v2_tex_2(D_90,'#skF_2')
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_474])).

tff(c_542,plain,(
    ! [D_101] :
      ( v2_tex_2(D_101,'#skF_3')
      | ~ v2_tex_2(D_101,'#skF_2')
      | ~ m1_subset_1(D_101,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_530])).

tff(c_552,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_37,c_542])).

tff(c_559,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_552])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_559])).

tff(c_563,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_8,plain,(
    ! [A_1,B_7] :
      ( m1_subset_1('#skF_1'(A_1,B_7),k1_zfmisc_1(u1_struct_0(A_1)))
      | v3_tex_2(B_7,A_1)
      | ~ v2_tex_2(B_7,A_1)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_84,plain,(
    ! [B_57,A_58] :
      ( u1_pre_topc('#skF_2') = B_57
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(A_58,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_74])).

tff(c_88,plain,(
    ! [A_11] :
      ( u1_pre_topc(A_11) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0(A_11),u1_pre_topc(A_11)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_84])).

tff(c_566,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_88])).

tff(c_568,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_566])).

tff(c_583,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_14])).

tff(c_587,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_583])).

tff(c_579,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_28])).

tff(c_18,plain,(
    ! [C_16,A_12,D_17,B_13] :
      ( C_16 = A_12
      | g1_pre_topc(C_16,D_17) != g1_pre_topc(A_12,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_614,plain,(
    ! [C_16,D_17] :
      ( u1_struct_0('#skF_2') = C_16
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_16,D_17)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_18])).

tff(c_620,plain,(
    ! [C_16,D_17] :
      ( u1_struct_0('#skF_2') = C_16
      | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != g1_pre_topc(C_16,D_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_614])).

tff(c_635,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_620])).

tff(c_562,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_589,plain,(
    ! [B_103,A_104] :
      ( r1_tarski(B_103,'#skF_1'(A_104,B_103))
      | v3_tex_2(B_103,A_104)
      | ~ v2_tex_2(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_593,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_589])).

tff(c_599,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_563,c_593])).

tff(c_600,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_599])).

tff(c_840,plain,(
    ! [C_122,B_123,A_124] :
      ( C_122 = B_123
      | ~ r1_tarski(B_123,C_122)
      | ~ v2_tex_2(C_122,A_124)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ v3_tex_2(B_123,A_124)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_842,plain,(
    ! [A_124] :
      ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
      | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),A_124)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ v3_tex_2('#skF_4',A_124)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(resolution,[status(thm)],[c_600,c_840])).

tff(c_846,plain,(
    ! [A_125] :
      ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),A_125)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ v3_tex_2('#skF_4',A_125)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_562,c_842])).

tff(c_853,plain,
    ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_846])).

tff(c_859,plain,
    ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_37,c_635,c_24,c_853])).

tff(c_860,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_863,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_860])).

tff(c_866,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_37,c_563,c_863])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_866])).

tff(c_869,plain,(
    ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_671,plain,(
    ! [A_109,B_110] :
      ( v2_tex_2('#skF_1'(A_109,B_110),A_109)
      | v3_tex_2(B_110,A_109)
      | ~ v2_tex_2(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_675,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_671])).

tff(c_680,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_563,c_675])).

tff(c_681,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_680])).

tff(c_870,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_874,plain,(
    ! [D_126,B_127,A_128] :
      ( v2_tex_2(D_126,B_127)
      | ~ v2_tex_2(D_126,A_128)
      | g1_pre_topc(u1_struct_0(B_127),u1_pre_topc(B_127)) != g1_pre_topc(u1_struct_0(A_128),u1_pre_topc(A_128))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(B_127)))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(B_127)
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_880,plain,(
    ! [D_126,A_128] :
      ( v2_tex_2(D_126,'#skF_2')
      | ~ v2_tex_2(D_126,A_128)
      | g1_pre_topc(u1_struct_0(A_128),u1_pre_topc(A_128)) != g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_874])).

tff(c_888,plain,(
    ! [D_126,A_128] :
      ( v2_tex_2(D_126,'#skF_2')
      | ~ v2_tex_2(D_126,A_128)
      | g1_pre_topc(u1_struct_0(A_128),u1_pre_topc(A_128)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_635,c_635,c_880])).

tff(c_1041,plain,(
    ! [D_126] :
      ( v2_tex_2(D_126,'#skF_2')
      | ~ v2_tex_2(D_126,'#skF_3')
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_126,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_888])).

tff(c_1053,plain,(
    ! [D_138] :
      ( v2_tex_2(D_138,'#skF_2')
      | ~ v2_tex_2(D_138,'#skF_3')
      | ~ m1_subset_1(D_138,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1041])).

tff(c_1056,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_870,c_1053])).

tff(c_1069,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_1056])).

tff(c_1071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_869,c_1069])).

%------------------------------------------------------------------------------
