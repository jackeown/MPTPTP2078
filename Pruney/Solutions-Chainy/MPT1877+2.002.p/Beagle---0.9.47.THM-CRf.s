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
% DateTime   : Thu Dec  3 10:29:57 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 898 expanded)
%              Number of leaves         :   26 ( 315 expanded)
%              Depth                    :   17
%              Number of atoms          :  282 (3257 expanded)
%              Number of equality atoms :   30 ( 595 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
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

tff(f_76,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
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

tff(c_36,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_32,plain,(
    ~ v3_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_47,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_40])).

tff(c_175,plain,(
    ! [A_69,B_70] :
      ( '#skF_1'(A_69,B_70) != B_70
      | v3_tex_2(B_70,A_69)
      | ~ v2_tex_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_178,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_175])).

tff(c_184,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_178])).

tff(c_185,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_184])).

tff(c_189,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_34,plain,(
    v3_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_88,plain,(
    ! [B_58,A_59] :
      ( v2_tex_2(B_58,A_59)
      | ~ v3_tex_2(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_94,plain,
    ( v2_tex_2('#skF_4','#skF_2')
    | ~ v3_tex_2('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_100,plain,(
    v2_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_34,c_94])).

tff(c_14,plain,(
    ! [A_9] :
      ( m1_pre_topc(A_9,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,(
    ! [A_60,B_61] :
      ( m1_pre_topc(A_60,g1_pre_topc(u1_struct_0(B_61),u1_pre_topc(B_61)))
      | ~ m1_pre_topc(A_60,B_61)
      | ~ l1_pre_topc(B_61)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_71,plain,(
    ! [B_55,A_56] :
      ( m1_pre_topc(B_55,A_56)
      | ~ m1_pre_topc(B_55,g1_pre_topc(u1_struct_0(A_56),u1_pre_topc(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_74,plain,(
    ! [B_55] :
      ( m1_pre_topc(B_55,'#skF_2')
      | ~ m1_pre_topc(B_55,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_71])).

tff(c_80,plain,(
    ! [B_55] :
      ( m1_pre_topc(B_55,'#skF_2')
      | ~ m1_pre_topc(B_55,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_74])).

tff(c_105,plain,(
    ! [A_60] :
      ( m1_pre_topc(A_60,'#skF_2')
      | ~ m1_pre_topc(A_60,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_101,c_80])).

tff(c_114,plain,(
    ! [A_60] :
      ( m1_pre_topc(A_60,'#skF_2')
      | ~ m1_pre_topc(A_60,'#skF_3')
      | ~ l1_pre_topc(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_105])).

tff(c_111,plain,(
    ! [A_60] :
      ( m1_pre_topc(A_60,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_60,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_101])).

tff(c_119,plain,(
    ! [A_63] :
      ( m1_pre_topc(A_63,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_63,'#skF_2')
      | ~ l1_pre_topc(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_111])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( m1_pre_topc(B_5,A_3)
      | ~ m1_pre_topc(B_5,g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_125,plain,(
    ! [A_63] :
      ( m1_pre_topc(A_63,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_63,'#skF_2')
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_131,plain,(
    ! [A_64] :
      ( m1_pre_topc(A_64,'#skF_3')
      | ~ m1_pre_topc(A_64,'#skF_2')
      | ~ l1_pre_topc(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_125])).

tff(c_138,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_131])).

tff(c_142,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_138])).

tff(c_16,plain,(
    ! [B_12,A_10] :
      ( r1_tarski(u1_struct_0(B_12),u1_struct_0(A_10))
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_67,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(u1_struct_0(B_53),u1_struct_0(A_54))
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [B_65,A_66] :
      ( u1_struct_0(B_65) = u1_struct_0(A_66)
      | ~ r1_tarski(u1_struct_0(A_66),u1_struct_0(B_65))
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_67,c_2])).

tff(c_154,plain,(
    ! [B_67,A_68] :
      ( u1_struct_0(B_67) = u1_struct_0(A_68)
      | ~ m1_pre_topc(A_68,B_67)
      | ~ l1_pre_topc(B_67)
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_16,c_143])).

tff(c_156,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_142,c_154])).

tff(c_167,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_156])).

tff(c_190,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_225,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_190])).

tff(c_228,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_225])).

tff(c_231,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_228])).

tff(c_235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_231])).

tff(c_236,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_255,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_38])).

tff(c_738,plain,(
    ! [D_100,B_101,A_102] :
      ( v2_tex_2(D_100,B_101)
      | ~ v2_tex_2(D_100,A_102)
      | g1_pre_topc(u1_struct_0(B_101),u1_pre_topc(B_101)) != g1_pre_topc(u1_struct_0(A_102),u1_pre_topc(A_102))
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0(B_101)))
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(B_101)
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_742,plain,(
    ! [D_100,B_101] :
      ( v2_tex_2(D_100,B_101)
      | ~ v2_tex_2(D_100,'#skF_2')
      | g1_pre_topc(u1_struct_0(B_101),u1_pre_topc(B_101)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0(B_101)))
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc(B_101)
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_738])).

tff(c_746,plain,(
    ! [D_100,B_101] :
      ( v2_tex_2(D_100,B_101)
      | ~ v2_tex_2(D_100,'#skF_2')
      | g1_pre_topc(u1_struct_0(B_101),u1_pre_topc(B_101)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0(B_101)))
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_236,c_255,c_742])).

tff(c_856,plain,(
    ! [D_100] :
      ( v2_tex_2(D_100,'#skF_3')
      | ~ v2_tex_2(D_100,'#skF_2')
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_100,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_746])).

tff(c_864,plain,(
    ! [D_113] :
      ( v2_tex_2(D_113,'#skF_3')
      | ~ v2_tex_2(D_113,'#skF_2')
      | ~ m1_subset_1(D_113,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_856])).

tff(c_874,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_864])).

tff(c_881,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_874])).

tff(c_883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_881])).

tff(c_885,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_24,plain,(
    ! [A_13,B_19] :
      ( m1_subset_1('#skF_1'(A_13,B_19),k1_zfmisc_1(u1_struct_0(A_13)))
      | v3_tex_2(B_19,A_13)
      | ~ v2_tex_2(B_19,A_13)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_898,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_933,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_898])).

tff(c_936,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_933])).

tff(c_939,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_936])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_939])).

tff(c_944,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_884,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_1011,plain,(
    ! [B_117,A_118] :
      ( r1_tarski(B_117,'#skF_1'(A_118,B_117))
      | v3_tex_2(B_117,A_118)
      | ~ v2_tex_2(B_117,A_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1015,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_1011])).

tff(c_1020,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_885,c_1015])).

tff(c_1021,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1020])).

tff(c_1233,plain,(
    ! [C_130,B_131,A_132] :
      ( C_130 = B_131
      | ~ r1_tarski(B_131,C_130)
      | ~ v2_tex_2(C_130,A_132)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ v3_tex_2(B_131,A_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1239,plain,(
    ! [A_132] :
      ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
      | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),A_132)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ v3_tex_2('#skF_4',A_132)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_1021,c_1233])).

tff(c_1330,plain,(
    ! [A_135] :
      ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),A_135)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ v3_tex_2('#skF_4',A_135)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_884,c_1239])).

tff(c_1337,plain,
    ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_tex_2('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_1330])).

tff(c_1343,plain,
    ( ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_47,c_944,c_34,c_1337])).

tff(c_1344,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1343])).

tff(c_1347,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1344])).

tff(c_1350,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_47,c_885,c_1347])).

tff(c_1352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1350])).

tff(c_1353,plain,(
    ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1343])).

tff(c_886,plain,(
    ! [A_114,B_115] :
      ( v2_tex_2('#skF_1'(A_114,B_115),A_114)
      | v3_tex_2(B_115,A_114)
      | ~ v2_tex_2(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_888,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_886])).

tff(c_893,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_885,c_888])).

tff(c_894,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_893])).

tff(c_1354,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1343])).

tff(c_963,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_38])).

tff(c_1392,plain,(
    ! [D_136,B_137,A_138] :
      ( v2_tex_2(D_136,B_137)
      | ~ v2_tex_2(D_136,A_138)
      | g1_pre_topc(u1_struct_0(B_137),u1_pre_topc(B_137)) != g1_pre_topc(u1_struct_0(A_138),u1_pre_topc(A_138))
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0(B_137)))
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(B_137)
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1394,plain,(
    ! [D_136,A_138] :
      ( v2_tex_2(D_136,'#skF_2')
      | ~ v2_tex_2(D_136,A_138)
      | g1_pre_topc(u1_struct_0(A_138),u1_pre_topc(A_138)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_944,c_1392])).

tff(c_1398,plain,(
    ! [D_136,A_138] :
      ( v2_tex_2(D_136,'#skF_2')
      | ~ v2_tex_2(D_136,A_138)
      | g1_pre_topc(u1_struct_0(A_138),u1_pre_topc(A_138)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_944,c_963,c_1394])).

tff(c_1578,plain,(
    ! [D_136] :
      ( v2_tex_2(D_136,'#skF_2')
      | ~ v2_tex_2(D_136,'#skF_3')
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1398])).

tff(c_1586,plain,(
    ! [D_151] :
      ( v2_tex_2(D_151,'#skF_2')
      | ~ v2_tex_2(D_151,'#skF_3')
      | ~ m1_subset_1(D_151,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1578])).

tff(c_1592,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1354,c_1586])).

tff(c_1603,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_894,c_1592])).

tff(c_1605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1353,c_1603])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:52:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.64  
% 3.77/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.64  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.77/1.64  
% 3.77/1.64  %Foreground sorts:
% 3.77/1.64  
% 3.77/1.64  
% 3.77/1.64  %Background operators:
% 3.77/1.64  
% 3.77/1.64  
% 3.77/1.64  %Foreground operators:
% 3.77/1.64  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.77/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.64  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.77/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.77/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.64  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.77/1.64  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.77/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.77/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.77/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.77/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.64  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.77/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.77/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.77/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.77/1.64  
% 3.77/1.66  tff(f_115, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v3_tex_2(C, A)) => v3_tex_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tex_2)).
% 3.77/1.66  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.77/1.66  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.77/1.66  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.77/1.66  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.77/1.66  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.77/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.77/1.66  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tex_2(C, A)) => v2_tex_2(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tex_2)).
% 3.77/1.66  tff(c_36, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.77/1.66  tff(c_32, plain, (~v3_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.77/1.66  tff(c_48, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32])).
% 3.77/1.66  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.77/1.66  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.77/1.66  tff(c_47, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_40])).
% 3.77/1.66  tff(c_175, plain, (![A_69, B_70]: ('#skF_1'(A_69, B_70)!=B_70 | v3_tex_2(B_70, A_69) | ~v2_tex_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.77/1.66  tff(c_178, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_47, c_175])).
% 3.77/1.66  tff(c_184, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_178])).
% 3.77/1.66  tff(c_185, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_184])).
% 3.77/1.66  tff(c_189, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_185])).
% 3.77/1.66  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.77/1.66  tff(c_34, plain, (v3_tex_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.77/1.66  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.77/1.66  tff(c_88, plain, (![B_58, A_59]: (v2_tex_2(B_58, A_59) | ~v3_tex_2(B_58, A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.77/1.66  tff(c_94, plain, (v2_tex_2('#skF_4', '#skF_2') | ~v3_tex_2('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_88])).
% 3.77/1.66  tff(c_100, plain, (v2_tex_2('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_34, c_94])).
% 3.77/1.66  tff(c_14, plain, (![A_9]: (m1_pre_topc(A_9, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.77/1.66  tff(c_101, plain, (![A_60, B_61]: (m1_pre_topc(A_60, g1_pre_topc(u1_struct_0(B_61), u1_pre_topc(B_61))) | ~m1_pre_topc(A_60, B_61) | ~l1_pre_topc(B_61) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.77/1.66  tff(c_38, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.77/1.66  tff(c_71, plain, (![B_55, A_56]: (m1_pre_topc(B_55, A_56) | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0(A_56), u1_pre_topc(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.77/1.66  tff(c_74, plain, (![B_55]: (m1_pre_topc(B_55, '#skF_2') | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_71])).
% 3.77/1.66  tff(c_80, plain, (![B_55]: (m1_pre_topc(B_55, '#skF_2') | ~m1_pre_topc(B_55, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_74])).
% 3.77/1.66  tff(c_105, plain, (![A_60]: (m1_pre_topc(A_60, '#skF_2') | ~m1_pre_topc(A_60, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_101, c_80])).
% 3.77/1.66  tff(c_114, plain, (![A_60]: (m1_pre_topc(A_60, '#skF_2') | ~m1_pre_topc(A_60, '#skF_3') | ~l1_pre_topc(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_105])).
% 3.77/1.66  tff(c_111, plain, (![A_60]: (m1_pre_topc(A_60, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_60, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_60))), inference(superposition, [status(thm), theory('equality')], [c_38, c_101])).
% 3.77/1.66  tff(c_119, plain, (![A_63]: (m1_pre_topc(A_63, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_63, '#skF_2') | ~l1_pre_topc(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_111])).
% 3.77/1.66  tff(c_8, plain, (![B_5, A_3]: (m1_pre_topc(B_5, A_3) | ~m1_pre_topc(B_5, g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.77/1.66  tff(c_125, plain, (![A_63]: (m1_pre_topc(A_63, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_63, '#skF_2') | ~l1_pre_topc(A_63))), inference(resolution, [status(thm)], [c_119, c_8])).
% 3.77/1.66  tff(c_131, plain, (![A_64]: (m1_pre_topc(A_64, '#skF_3') | ~m1_pre_topc(A_64, '#skF_2') | ~l1_pre_topc(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_125])).
% 3.77/1.66  tff(c_138, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_14, c_131])).
% 3.77/1.66  tff(c_142, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_138])).
% 3.77/1.66  tff(c_16, plain, (![B_12, A_10]: (r1_tarski(u1_struct_0(B_12), u1_struct_0(A_10)) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.77/1.66  tff(c_67, plain, (![B_53, A_54]: (r1_tarski(u1_struct_0(B_53), u1_struct_0(A_54)) | ~m1_pre_topc(B_53, A_54) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.77/1.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.77/1.66  tff(c_143, plain, (![B_65, A_66]: (u1_struct_0(B_65)=u1_struct_0(A_66) | ~r1_tarski(u1_struct_0(A_66), u1_struct_0(B_65)) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_67, c_2])).
% 3.77/1.66  tff(c_154, plain, (![B_67, A_68]: (u1_struct_0(B_67)=u1_struct_0(A_68) | ~m1_pre_topc(A_68, B_67) | ~l1_pre_topc(B_67) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_16, c_143])).
% 3.77/1.66  tff(c_156, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_142, c_154])).
% 3.77/1.66  tff(c_167, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_156])).
% 3.77/1.66  tff(c_190, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_167])).
% 3.77/1.66  tff(c_225, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_114, c_190])).
% 3.77/1.66  tff(c_228, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_225])).
% 3.77/1.66  tff(c_231, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_228])).
% 3.77/1.66  tff(c_235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_231])).
% 3.77/1.66  tff(c_236, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_167])).
% 3.77/1.66  tff(c_255, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_38])).
% 3.77/1.66  tff(c_738, plain, (![D_100, B_101, A_102]: (v2_tex_2(D_100, B_101) | ~v2_tex_2(D_100, A_102) | g1_pre_topc(u1_struct_0(B_101), u1_pre_topc(B_101))!=g1_pre_topc(u1_struct_0(A_102), u1_pre_topc(A_102)) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0(B_101))) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(B_101) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.77/1.66  tff(c_742, plain, (![D_100, B_101]: (v2_tex_2(D_100, B_101) | ~v2_tex_2(D_100, '#skF_2') | g1_pre_topc(u1_struct_0(B_101), u1_pre_topc(B_101))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0(B_101))) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc(B_101) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_236, c_738])).
% 3.77/1.66  tff(c_746, plain, (![D_100, B_101]: (v2_tex_2(D_100, B_101) | ~v2_tex_2(D_100, '#skF_2') | g1_pre_topc(u1_struct_0(B_101), u1_pre_topc(B_101))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0(B_101))) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_236, c_255, c_742])).
% 3.77/1.66  tff(c_856, plain, (![D_100]: (v2_tex_2(D_100, '#skF_3') | ~v2_tex_2(D_100, '#skF_2') | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_100, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_746])).
% 3.77/1.66  tff(c_864, plain, (![D_113]: (v2_tex_2(D_113, '#skF_3') | ~v2_tex_2(D_113, '#skF_2') | ~m1_subset_1(D_113, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_856])).
% 3.77/1.66  tff(c_874, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_47, c_864])).
% 3.77/1.66  tff(c_881, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_874])).
% 3.77/1.66  tff(c_883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_881])).
% 3.77/1.66  tff(c_885, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_185])).
% 3.77/1.66  tff(c_24, plain, (![A_13, B_19]: (m1_subset_1('#skF_1'(A_13, B_19), k1_zfmisc_1(u1_struct_0(A_13))) | v3_tex_2(B_19, A_13) | ~v2_tex_2(B_19, A_13) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.77/1.66  tff(c_898, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_167])).
% 3.77/1.66  tff(c_933, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_114, c_898])).
% 3.77/1.66  tff(c_936, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_933])).
% 3.77/1.66  tff(c_939, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_936])).
% 3.77/1.66  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_939])).
% 3.77/1.66  tff(c_944, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_167])).
% 3.77/1.66  tff(c_884, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_185])).
% 3.77/1.66  tff(c_1011, plain, (![B_117, A_118]: (r1_tarski(B_117, '#skF_1'(A_118, B_117)) | v3_tex_2(B_117, A_118) | ~v2_tex_2(B_117, A_118) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.77/1.66  tff(c_1015, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_47, c_1011])).
% 3.77/1.66  tff(c_1020, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_885, c_1015])).
% 3.77/1.66  tff(c_1021, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_1020])).
% 3.77/1.66  tff(c_1233, plain, (![C_130, B_131, A_132]: (C_130=B_131 | ~r1_tarski(B_131, C_130) | ~v2_tex_2(C_130, A_132) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_132))) | ~v3_tex_2(B_131, A_132) | ~m1_subset_1(B_131, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.77/1.66  tff(c_1239, plain, (![A_132]: ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), A_132) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_132))) | ~v3_tex_2('#skF_4', A_132) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_1021, c_1233])).
% 3.77/1.66  tff(c_1330, plain, (![A_135]: (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), A_135) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_135))) | ~v3_tex_2('#skF_4', A_135) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(negUnitSimplification, [status(thm)], [c_884, c_1239])).
% 3.77/1.66  tff(c_1337, plain, (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_tex_2('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_944, c_1330])).
% 3.77/1.66  tff(c_1343, plain, (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_47, c_944, c_34, c_1337])).
% 3.77/1.66  tff(c_1344, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1343])).
% 3.77/1.66  tff(c_1347, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_1344])).
% 3.77/1.66  tff(c_1350, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_47, c_885, c_1347])).
% 3.77/1.66  tff(c_1352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1350])).
% 3.77/1.66  tff(c_1353, plain, (~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_1343])).
% 3.77/1.66  tff(c_886, plain, (![A_114, B_115]: (v2_tex_2('#skF_1'(A_114, B_115), A_114) | v3_tex_2(B_115, A_114) | ~v2_tex_2(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.77/1.66  tff(c_888, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_47, c_886])).
% 3.77/1.66  tff(c_893, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_885, c_888])).
% 3.77/1.66  tff(c_894, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_893])).
% 3.77/1.66  tff(c_1354, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1343])).
% 3.77/1.66  tff(c_963, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_944, c_38])).
% 3.77/1.66  tff(c_1392, plain, (![D_136, B_137, A_138]: (v2_tex_2(D_136, B_137) | ~v2_tex_2(D_136, A_138) | g1_pre_topc(u1_struct_0(B_137), u1_pre_topc(B_137))!=g1_pre_topc(u1_struct_0(A_138), u1_pre_topc(A_138)) | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0(B_137))) | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(B_137) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.77/1.66  tff(c_1394, plain, (![D_136, A_138]: (v2_tex_2(D_136, '#skF_2') | ~v2_tex_2(D_136, A_138) | g1_pre_topc(u1_struct_0(A_138), u1_pre_topc(A_138))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')) | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_138))), inference(superposition, [status(thm), theory('equality')], [c_944, c_1392])).
% 3.77/1.66  tff(c_1398, plain, (![D_136, A_138]: (v2_tex_2(D_136, '#skF_2') | ~v2_tex_2(D_136, A_138) | g1_pre_topc(u1_struct_0(A_138), u1_pre_topc(A_138))!=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_944, c_963, c_1394])).
% 3.77/1.66  tff(c_1578, plain, (![D_136]: (v2_tex_2(D_136, '#skF_2') | ~v2_tex_2(D_136, '#skF_3') | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_1398])).
% 3.77/1.66  tff(c_1586, plain, (![D_151]: (v2_tex_2(D_151, '#skF_2') | ~v2_tex_2(D_151, '#skF_3') | ~m1_subset_1(D_151, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1578])).
% 3.77/1.66  tff(c_1592, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1354, c_1586])).
% 3.77/1.66  tff(c_1603, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_894, c_1592])).
% 3.77/1.66  tff(c_1605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1353, c_1603])).
% 3.77/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.66  
% 3.77/1.66  Inference rules
% 3.77/1.66  ----------------------
% 3.77/1.66  #Ref     : 5
% 3.77/1.66  #Sup     : 278
% 3.77/1.66  #Fact    : 0
% 3.77/1.66  #Define  : 0
% 3.77/1.66  #Split   : 6
% 3.77/1.66  #Chain   : 0
% 3.77/1.66  #Close   : 0
% 3.77/1.66  
% 3.77/1.66  Ordering : KBO
% 3.77/1.66  
% 3.77/1.66  Simplification rules
% 3.77/1.66  ----------------------
% 3.77/1.66  #Subsume      : 73
% 3.77/1.66  #Demod        : 403
% 3.77/1.66  #Tautology    : 89
% 3.77/1.66  #SimpNegUnit  : 19
% 3.77/1.66  #BackRed      : 4
% 3.77/1.66  
% 3.77/1.66  #Partial instantiations: 0
% 3.77/1.66  #Strategies tried      : 1
% 3.77/1.66  
% 3.77/1.66  Timing (in seconds)
% 3.77/1.66  ----------------------
% 3.77/1.66  Preprocessing        : 0.34
% 3.77/1.66  Parsing              : 0.18
% 3.77/1.66  CNF conversion       : 0.03
% 3.77/1.66  Main loop            : 0.51
% 3.77/1.66  Inferencing          : 0.17
% 3.77/1.66  Reduction            : 0.17
% 3.77/1.66  Demodulation         : 0.12
% 3.77/1.66  BG Simplification    : 0.02
% 3.77/1.66  Subsumption          : 0.11
% 3.77/1.66  Abstraction          : 0.02
% 3.77/1.66  MUC search           : 0.00
% 3.77/1.66  Cooper               : 0.00
% 3.77/1.66  Total                : 0.89
% 3.77/1.66  Index Insertion      : 0.00
% 3.77/1.66  Index Deletion       : 0.00
% 3.77/1.66  Index Matching       : 0.00
% 3.77/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
