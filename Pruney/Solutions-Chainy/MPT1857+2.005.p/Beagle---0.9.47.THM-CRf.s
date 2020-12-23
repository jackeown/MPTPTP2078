%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:09 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 328 expanded)
%              Number of leaves         :   28 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  347 (1235 expanded)
%              Number of equality atoms :   36 ( 337 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
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
                        & v2_tex_2(C,A) )
                     => v2_tex_2(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(c_32,plain,(
    ~ v2_tex_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_34,plain,(
    v2_tex_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    v2_tex_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_166,plain,(
    ! [A_91,B_92] :
      ( r1_tarski('#skF_2'(A_91,B_92),B_92)
      | v2_tex_2(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_168,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_166])).

tff(c_173,plain,
    ( r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_168])).

tff(c_174,plain,(
    r1_tarski('#skF_2'('#skF_4','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_173])).

tff(c_24,plain,(
    ! [A_33,B_47] :
      ( m1_subset_1('#skF_2'(A_33,B_47),k1_zfmisc_1(u1_struct_0(A_33)))
      | v2_tex_2(B_47,A_33)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4,plain,(
    ! [A_4] :
      ( m1_subset_1(u1_pre_topc(A_4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_85,plain,(
    ! [D_76,B_77,C_78,A_79] :
      ( D_76 = B_77
      | g1_pre_topc(C_78,D_76) != g1_pre_topc(A_79,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_154,plain,(
    ! [B_89,A_90] :
      ( u1_pre_topc('#skF_3') = B_89
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(A_90,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_85])).

tff(c_158,plain,(
    ! [A_4] :
      ( u1_pre_topc(A_4) = u1_pre_topc('#skF_3')
      | g1_pre_topc(u1_struct_0(A_4),u1_pre_topc(A_4)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_154])).

tff(c_216,plain,
    ( u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_158])).

tff(c_218,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_216])).

tff(c_94,plain,(
    ! [C_80,A_81,D_82,B_83] :
      ( C_80 = A_81
      | g1_pre_topc(C_80,D_82) != g1_pre_topc(A_81,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,(
    ! [C_80,D_82] :
      ( u1_struct_0('#skF_3') = C_80
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_80,D_82)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_94])).

tff(c_227,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_255,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_227])).

tff(c_243,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_4])).

tff(c_253,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_243])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_253])).

tff(c_257,plain,(
    ! [C_80,D_82] :
      ( u1_struct_0('#skF_3') = C_80
      | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != g1_pre_topc(C_80,D_82) ) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_323,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_257])).

tff(c_376,plain,(
    ! [A_106,B_107,C_108] :
      ( v3_pre_topc('#skF_1'(A_106,B_107,C_108),A_106)
      | ~ r1_tarski(C_108,B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_378,plain,(
    ! [B_107,C_108] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_107,C_108),'#skF_3')
      | ~ r1_tarski(C_108,B_107)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_107,'#skF_3')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_376])).

tff(c_561,plain,(
    ! [B_125,C_126] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_125,C_126),'#skF_3')
      | ~ r1_tarski(C_126,B_125)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_125,'#skF_3')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_323,c_378])).

tff(c_569,plain,(
    ! [B_125,B_47] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_125,'#skF_2'('#skF_4',B_47)),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_4',B_47),B_125)
      | ~ v2_tex_2(B_125,'#skF_3')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_47,'#skF_4')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_561])).

tff(c_578,plain,(
    ! [B_125,B_47] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_125,'#skF_2'('#skF_4',B_47)),'#skF_3')
      | ~ r1_tarski('#skF_2'('#skF_4',B_47),B_125)
      | ~ v2_tex_2(B_125,'#skF_3')
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_47,'#skF_4')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_569])).

tff(c_18,plain,(
    ! [A_32] :
      ( m1_pre_topc(A_32,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_292,plain,(
    ! [D_99,C_100,A_101] :
      ( v3_pre_topc(D_99,C_100)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(u1_struct_0(C_100)))
      | ~ v3_pre_topc(D_99,A_101)
      | ~ m1_pre_topc(C_100,A_101)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_300,plain,(
    ! [A_101] :
      ( v3_pre_topc('#skF_6','#skF_4')
      | ~ v3_pre_topc('#skF_6',A_101)
      | ~ m1_pre_topc('#skF_4',A_101)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_40,c_292])).

tff(c_398,plain,(
    ! [A_111] :
      ( ~ v3_pre_topc('#skF_6',A_111)
      | ~ m1_pre_topc('#skF_4',A_111)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_404,plain,
    ( ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_398])).

tff(c_409,plain,
    ( ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_404])).

tff(c_410,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_413,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_410])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_413])).

tff(c_419,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_99,plain,(
    ! [A_84,B_85] :
      ( m1_pre_topc(A_84,g1_pre_topc(u1_struct_0(B_85),u1_pre_topc(B_85)))
      | ~ m1_pre_topc(A_84,B_85)
      | ~ l1_pre_topc(B_85)
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_64,plain,(
    ! [B_73,A_74] :
      ( m1_pre_topc(B_73,A_74)
      | ~ m1_pre_topc(B_73,g1_pre_topc(u1_struct_0(A_74),u1_pre_topc(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_67,plain,(
    ! [B_73] :
      ( m1_pre_topc(B_73,'#skF_3')
      | ~ m1_pre_topc(B_73,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_64])).

tff(c_73,plain,(
    ! [B_73] :
      ( m1_pre_topc(B_73,'#skF_3')
      | ~ m1_pre_topc(B_73,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_67])).

tff(c_103,plain,(
    ! [A_84] :
      ( m1_pre_topc(A_84,'#skF_3')
      | ~ m1_pre_topc(A_84,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_84) ) ),
    inference(resolution,[status(thm)],[c_99,c_73])).

tff(c_115,plain,(
    ! [A_84] :
      ( m1_pre_topc(A_84,'#skF_3')
      | ~ m1_pre_topc(A_84,'#skF_4')
      | ~ l1_pre_topc(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_103])).

tff(c_401,plain,
    ( ~ v3_pre_topc('#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_398])).

tff(c_406,plain,
    ( ~ v3_pre_topc('#skF_6','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_401])).

tff(c_441,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_444,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_115,c_441])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_419,c_444])).

tff(c_450,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_30,plain,(
    ! [A_33,B_47,C_54] :
      ( m1_subset_1('#skF_1'(A_33,B_47,C_54),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ r1_tarski(C_54,B_47)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ v2_tex_2(B_47,A_33)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_426,plain,(
    ! [A_112,B_113,C_114] :
      ( m1_subset_1('#skF_1'(A_112,B_113,C_114),k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ r1_tarski(C_114,B_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v2_tex_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_435,plain,(
    ! [B_113,C_114] :
      ( m1_subset_1('#skF_1'('#skF_3',B_113,C_114),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_114,B_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_113,'#skF_3')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_426])).

tff(c_651,plain,(
    ! [B_138,C_139] :
      ( m1_subset_1('#skF_1'('#skF_3',B_138,C_139),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_139,B_138)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_138,'#skF_3')
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_323,c_323,c_435])).

tff(c_16,plain,(
    ! [D_31,C_29,A_17] :
      ( v3_pre_topc(D_31,C_29)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0(C_29)))
      | ~ v3_pre_topc(D_31,A_17)
      | ~ m1_pre_topc(C_29,A_17)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1294,plain,(
    ! [B_261,C_262,A_263] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_261,C_262),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_261,C_262),A_263)
      | ~ m1_pre_topc('#skF_4',A_263)
      | ~ m1_subset_1('#skF_1'('#skF_3',B_261,C_262),k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ l1_pre_topc(A_263)
      | ~ r1_tarski(C_262,B_261)
      | ~ m1_subset_1(C_262,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_261,'#skF_3')
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_651,c_16])).

tff(c_1301,plain,(
    ! [B_47,C_54] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_47,C_54),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_47,C_54),'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_54,B_47)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_47,'#skF_3')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_1294])).

tff(c_1328,plain,(
    ! [B_267,C_268] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_267,C_268),'#skF_4')
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_267,C_268),'#skF_3')
      | ~ r1_tarski(C_268,B_267)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_267,'#skF_3')
      | ~ m1_subset_1(B_267,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_323,c_323,c_450,c_1301])).

tff(c_1389,plain,(
    ! [B_275,B_276] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_275,'#skF_2'('#skF_4',B_276)),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_276),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_276),B_275)
      | ~ v2_tex_2(B_275,'#skF_3')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_276,'#skF_4')
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_578,c_1328])).

tff(c_1392,plain,(
    ! [B_275,B_47] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_275,'#skF_2'('#skF_4',B_47)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_47),B_275)
      | ~ v2_tex_2(B_275,'#skF_3')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_47,'#skF_4')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_1389])).

tff(c_1395,plain,(
    ! [B_275,B_47] :
      ( v3_pre_topc('#skF_1'('#skF_3',B_275,'#skF_2'('#skF_4',B_47)),'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_47),B_275)
      | ~ v2_tex_2(B_275,'#skF_3')
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_47,'#skF_4')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1392])).

tff(c_440,plain,(
    ! [B_113,C_114] :
      ( m1_subset_1('#skF_1'('#skF_3',B_113,C_114),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(C_114,B_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_113,'#skF_3')
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_323,c_323,c_435])).

tff(c_606,plain,(
    ! [A_128,B_129,C_130] :
      ( k9_subset_1(u1_struct_0(A_128),B_129,'#skF_1'(A_128,B_129,C_130)) = C_130
      | ~ r1_tarski(C_130,B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ v2_tex_2(B_129,A_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_612,plain,(
    ! [B_129,C_130] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_129,'#skF_1'('#skF_3',B_129,C_130)) = C_130
      | ~ r1_tarski(C_130,B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_129,'#skF_3')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_606])).

tff(c_691,plain,(
    ! [B_142,C_143] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_142,'#skF_1'('#skF_3',B_142,C_143)) = C_143
      | ~ r1_tarski(C_143,B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_323,c_323,c_612])).

tff(c_701,plain,(
    ! [B_142,B_47] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_142,'#skF_1'('#skF_3',B_142,'#skF_2'('#skF_4',B_47))) = '#skF_2'('#skF_4',B_47)
      | ~ r1_tarski('#skF_2'('#skF_4',B_47),B_142)
      | ~ v2_tex_2(B_142,'#skF_3')
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_47,'#skF_4')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_691])).

tff(c_1090,plain,(
    ! [B_207,B_208] :
      ( k9_subset_1(u1_struct_0('#skF_4'),B_207,'#skF_1'('#skF_3',B_207,'#skF_2'('#skF_4',B_208))) = '#skF_2'('#skF_4',B_208)
      | ~ r1_tarski('#skF_2'('#skF_4',B_208),B_207)
      | ~ v2_tex_2(B_207,'#skF_3')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_208,'#skF_4')
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_701])).

tff(c_20,plain,(
    ! [A_33,B_47,D_57] :
      ( k9_subset_1(u1_struct_0(A_33),B_47,D_57) != '#skF_2'(A_33,B_47)
      | ~ v3_pre_topc(D_57,A_33)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(u1_struct_0(A_33)))
      | v2_tex_2(B_47,A_33)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1097,plain,(
    ! [B_208,B_207] :
      ( '#skF_2'('#skF_4',B_208) != '#skF_2'('#skF_4',B_207)
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_207,'#skF_2'('#skF_4',B_208)),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_207,'#skF_2'('#skF_4',B_208)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_207,'#skF_4')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_208),B_207)
      | ~ v2_tex_2(B_207,'#skF_3')
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_208,'#skF_4')
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1090,c_20])).

tff(c_1807,plain,(
    ! [B_359,B_358] :
      ( '#skF_2'('#skF_4',B_359) != '#skF_2'('#skF_4',B_358)
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_359,'#skF_2'('#skF_4',B_358)),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_359,'#skF_2'('#skF_4',B_358)),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_359,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_358),B_359)
      | ~ v2_tex_2(B_359,'#skF_3')
      | ~ m1_subset_1(B_359,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_358,'#skF_4')
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1097])).

tff(c_1813,plain,(
    ! [B_361,B_360] :
      ( '#skF_2'('#skF_4',B_361) != '#skF_2'('#skF_4',B_360)
      | ~ v3_pre_topc('#skF_1'('#skF_3',B_361,'#skF_2'('#skF_4',B_360)),'#skF_4')
      | v2_tex_2(B_361,'#skF_4')
      | v2_tex_2(B_360,'#skF_4')
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_360),B_361)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_360),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_361,'#skF_3')
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_440,c_1807])).

tff(c_1817,plain,(
    ! [B_363,B_362] :
      ( '#skF_2'('#skF_4',B_363) != '#skF_2'('#skF_4',B_362)
      | v2_tex_2(B_363,'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_362),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_2'('#skF_4',B_362),B_363)
      | ~ v2_tex_2(B_363,'#skF_3')
      | ~ m1_subset_1(B_363,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_362,'#skF_4')
      | ~ m1_subset_1(B_362,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1395,c_1813])).

tff(c_1820,plain,(
    ! [B_47,B_363] :
      ( '#skF_2'('#skF_4',B_47) != '#skF_2'('#skF_4',B_363)
      | v2_tex_2(B_363,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_47),B_363)
      | ~ v2_tex_2(B_363,'#skF_3')
      | ~ m1_subset_1(B_363,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_47,'#skF_4')
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_1817])).

tff(c_1831,plain,(
    ! [B_367,B_366] :
      ( '#skF_2'('#skF_4',B_367) != '#skF_2'('#skF_4',B_366)
      | v2_tex_2(B_367,'#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_4',B_366),B_367)
      | ~ v2_tex_2(B_367,'#skF_3')
      | ~ m1_subset_1(B_367,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_tex_2(B_366,'#skF_4')
      | ~ m1_subset_1(B_366,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1820])).

tff(c_1843,plain,
    ( ~ v2_tex_2('#skF_6','#skF_3')
    | v2_tex_2('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_174,c_1831])).

tff(c_1854,plain,(
    v2_tex_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_48,c_1843])).

tff(c_1856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1854])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:55:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.15  
% 5.92/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.15  %$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > k9_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 5.92/2.15  
% 5.92/2.15  %Foreground sorts:
% 5.92/2.15  
% 5.92/2.15  
% 5.92/2.15  %Background operators:
% 5.92/2.15  
% 5.92/2.15  
% 5.92/2.15  %Foreground operators:
% 5.92/2.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.92/2.15  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.92/2.15  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.92/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.15  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.92/2.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.92/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.92/2.15  tff('#skF_5', type, '#skF_5': $i).
% 5.92/2.15  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.92/2.15  tff('#skF_6', type, '#skF_6': $i).
% 5.92/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.92/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.92/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.92/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.92/2.15  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.92/2.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.92/2.15  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.92/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.92/2.15  
% 5.92/2.17  tff(f_123, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (C = D)) & v2_tex_2(C, A)) => v2_tex_2(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tex_2)).
% 5.92/2.17  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 5.92/2.17  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 5.92/2.17  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 5.92/2.17  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.92/2.17  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 5.92/2.17  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.92/2.17  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 5.92/2.17  tff(c_32, plain, (~v2_tex_2('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.92/2.17  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.92/2.17  tff(c_36, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.92/2.17  tff(c_34, plain, (v2_tex_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.92/2.17  tff(c_48, plain, (v2_tex_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34])).
% 5.92/2.17  tff(c_44, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.92/2.17  tff(c_166, plain, (![A_91, B_92]: (r1_tarski('#skF_2'(A_91, B_92), B_92) | v2_tex_2(B_92, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.17  tff(c_168, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_166])).
% 5.92/2.17  tff(c_173, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_168])).
% 5.92/2.17  tff(c_174, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_32, c_173])).
% 5.92/2.17  tff(c_24, plain, (![A_33, B_47]: (m1_subset_1('#skF_2'(A_33, B_47), k1_zfmisc_1(u1_struct_0(A_33))) | v2_tex_2(B_47, A_33) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.17  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.92/2.17  tff(c_4, plain, (![A_4]: (m1_subset_1(u1_pre_topc(A_4), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.92/2.17  tff(c_38, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.92/2.18  tff(c_85, plain, (![D_76, B_77, C_78, A_79]: (D_76=B_77 | g1_pre_topc(C_78, D_76)!=g1_pre_topc(A_79, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.18  tff(c_154, plain, (![B_89, A_90]: (u1_pre_topc('#skF_3')=B_89 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(A_90, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(A_90))))), inference(superposition, [status(thm), theory('equality')], [c_38, c_85])).
% 5.92/2.18  tff(c_158, plain, (![A_4]: (u1_pre_topc(A_4)=u1_pre_topc('#skF_3') | g1_pre_topc(u1_struct_0(A_4), u1_pre_topc(A_4))!=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_4, c_154])).
% 5.92/2.18  tff(c_216, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_158])).
% 5.92/2.18  tff(c_218, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_216])).
% 5.92/2.18  tff(c_94, plain, (![C_80, A_81, D_82, B_83]: (C_80=A_81 | g1_pre_topc(C_80, D_82)!=g1_pre_topc(A_81, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.92/2.18  tff(c_98, plain, (![C_80, D_82]: (u1_struct_0('#skF_3')=C_80 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_80, D_82) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_38, c_94])).
% 5.92/2.18  tff(c_227, plain, (~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_98])).
% 5.92/2.18  tff(c_255, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_227])).
% 5.92/2.18  tff(c_243, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_218, c_4])).
% 5.92/2.18  tff(c_253, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_243])).
% 5.92/2.18  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_253])).
% 5.92/2.18  tff(c_257, plain, (![C_80, D_82]: (u1_struct_0('#skF_3')=C_80 | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=g1_pre_topc(C_80, D_82))), inference(splitRight, [status(thm)], [c_98])).
% 5.92/2.18  tff(c_323, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_257])).
% 5.92/2.18  tff(c_376, plain, (![A_106, B_107, C_108]: (v3_pre_topc('#skF_1'(A_106, B_107, C_108), A_106) | ~r1_tarski(C_108, B_107) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0(A_106))) | ~v2_tex_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.18  tff(c_378, plain, (![B_107, C_108]: (v3_pre_topc('#skF_1'('#skF_3', B_107, C_108), '#skF_3') | ~r1_tarski(C_108, B_107) | ~m1_subset_1(C_108, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_107, '#skF_3') | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_323, c_376])).
% 5.92/2.18  tff(c_561, plain, (![B_125, C_126]: (v3_pre_topc('#skF_1'('#skF_3', B_125, C_126), '#skF_3') | ~r1_tarski(C_126, B_125) | ~m1_subset_1(C_126, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_125, '#skF_3') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_323, c_378])).
% 5.92/2.18  tff(c_569, plain, (![B_125, B_47]: (v3_pre_topc('#skF_1'('#skF_3', B_125, '#skF_2'('#skF_4', B_47)), '#skF_3') | ~r1_tarski('#skF_2'('#skF_4', B_47), B_125) | ~v2_tex_2(B_125, '#skF_3') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_47, '#skF_4') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_561])).
% 5.92/2.18  tff(c_578, plain, (![B_125, B_47]: (v3_pre_topc('#skF_1'('#skF_3', B_125, '#skF_2'('#skF_4', B_47)), '#skF_3') | ~r1_tarski('#skF_2'('#skF_4', B_47), B_125) | ~v2_tex_2(B_125, '#skF_3') | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_47, '#skF_4') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_569])).
% 5.92/2.18  tff(c_18, plain, (![A_32]: (m1_pre_topc(A_32, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.92/2.18  tff(c_292, plain, (![D_99, C_100, A_101]: (v3_pre_topc(D_99, C_100) | ~m1_subset_1(D_99, k1_zfmisc_1(u1_struct_0(C_100))) | ~v3_pre_topc(D_99, A_101) | ~m1_pre_topc(C_100, A_101) | ~m1_subset_1(D_99, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.92/2.18  tff(c_300, plain, (![A_101]: (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', A_101) | ~m1_pre_topc('#skF_4', A_101) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_40, c_292])).
% 5.92/2.18  tff(c_398, plain, (![A_111]: (~v3_pre_topc('#skF_6', A_111) | ~m1_pre_topc('#skF_4', A_111) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111))), inference(splitLeft, [status(thm)], [c_300])).
% 5.92/2.18  tff(c_404, plain, (~v3_pre_topc('#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_398])).
% 5.92/2.18  tff(c_409, plain, (~v3_pre_topc('#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_404])).
% 5.92/2.18  tff(c_410, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_409])).
% 5.92/2.18  tff(c_413, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_410])).
% 5.92/2.18  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_413])).
% 5.92/2.18  tff(c_419, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_409])).
% 5.92/2.18  tff(c_99, plain, (![A_84, B_85]: (m1_pre_topc(A_84, g1_pre_topc(u1_struct_0(B_85), u1_pre_topc(B_85))) | ~m1_pre_topc(A_84, B_85) | ~l1_pre_topc(B_85) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.92/2.18  tff(c_64, plain, (![B_73, A_74]: (m1_pre_topc(B_73, A_74) | ~m1_pre_topc(B_73, g1_pre_topc(u1_struct_0(A_74), u1_pre_topc(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.92/2.18  tff(c_67, plain, (![B_73]: (m1_pre_topc(B_73, '#skF_3') | ~m1_pre_topc(B_73, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_64])).
% 5.92/2.18  tff(c_73, plain, (![B_73]: (m1_pre_topc(B_73, '#skF_3') | ~m1_pre_topc(B_73, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_67])).
% 5.92/2.18  tff(c_103, plain, (![A_84]: (m1_pre_topc(A_84, '#skF_3') | ~m1_pre_topc(A_84, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_84))), inference(resolution, [status(thm)], [c_99, c_73])).
% 5.92/2.18  tff(c_115, plain, (![A_84]: (m1_pre_topc(A_84, '#skF_3') | ~m1_pre_topc(A_84, '#skF_4') | ~l1_pre_topc(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_103])).
% 5.92/2.18  tff(c_401, plain, (~v3_pre_topc('#skF_6', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_323, c_398])).
% 5.92/2.18  tff(c_406, plain, (~v3_pre_topc('#skF_6', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_401])).
% 5.92/2.18  tff(c_441, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_406])).
% 5.92/2.18  tff(c_444, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_115, c_441])).
% 5.92/2.18  tff(c_448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_419, c_444])).
% 5.92/2.18  tff(c_450, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_406])).
% 5.92/2.18  tff(c_30, plain, (![A_33, B_47, C_54]: (m1_subset_1('#skF_1'(A_33, B_47, C_54), k1_zfmisc_1(u1_struct_0(A_33))) | ~r1_tarski(C_54, B_47) | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0(A_33))) | ~v2_tex_2(B_47, A_33) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.18  tff(c_426, plain, (![A_112, B_113, C_114]: (m1_subset_1('#skF_1'(A_112, B_113, C_114), k1_zfmisc_1(u1_struct_0(A_112))) | ~r1_tarski(C_114, B_113) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_112))) | ~v2_tex_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.18  tff(c_435, plain, (![B_113, C_114]: (m1_subset_1('#skF_1'('#skF_3', B_113, C_114), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_114, B_113) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_113, '#skF_3') | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_323, c_426])).
% 5.92/2.18  tff(c_651, plain, (![B_138, C_139]: (m1_subset_1('#skF_1'('#skF_3', B_138, C_139), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_139, B_138) | ~m1_subset_1(C_139, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_138, '#skF_3') | ~m1_subset_1(B_138, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_323, c_323, c_435])).
% 5.92/2.18  tff(c_16, plain, (![D_31, C_29, A_17]: (v3_pre_topc(D_31, C_29) | ~m1_subset_1(D_31, k1_zfmisc_1(u1_struct_0(C_29))) | ~v3_pre_topc(D_31, A_17) | ~m1_pre_topc(C_29, A_17) | ~m1_subset_1(D_31, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.92/2.18  tff(c_1294, plain, (![B_261, C_262, A_263]: (v3_pre_topc('#skF_1'('#skF_3', B_261, C_262), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_3', B_261, C_262), A_263) | ~m1_pre_topc('#skF_4', A_263) | ~m1_subset_1('#skF_1'('#skF_3', B_261, C_262), k1_zfmisc_1(u1_struct_0(A_263))) | ~l1_pre_topc(A_263) | ~r1_tarski(C_262, B_261) | ~m1_subset_1(C_262, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_261, '#skF_3') | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_651, c_16])).
% 5.92/2.18  tff(c_1301, plain, (![B_47, C_54]: (v3_pre_topc('#skF_1'('#skF_3', B_47, C_54), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_3', B_47, C_54), '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_54, B_47) | ~m1_subset_1(C_54, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_47, '#skF_3') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_1294])).
% 5.92/2.18  tff(c_1328, plain, (![B_267, C_268]: (v3_pre_topc('#skF_1'('#skF_3', B_267, C_268), '#skF_4') | ~v3_pre_topc('#skF_1'('#skF_3', B_267, C_268), '#skF_3') | ~r1_tarski(C_268, B_267) | ~m1_subset_1(C_268, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_267, '#skF_3') | ~m1_subset_1(B_267, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_323, c_323, c_450, c_1301])).
% 5.92/2.18  tff(c_1389, plain, (![B_275, B_276]: (v3_pre_topc('#skF_1'('#skF_3', B_275, '#skF_2'('#skF_4', B_276)), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', B_276), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_276), B_275) | ~v2_tex_2(B_275, '#skF_3') | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_276, '#skF_4') | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_578, c_1328])).
% 5.92/2.18  tff(c_1392, plain, (![B_275, B_47]: (v3_pre_topc('#skF_1'('#skF_3', B_275, '#skF_2'('#skF_4', B_47)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_47), B_275) | ~v2_tex_2(B_275, '#skF_3') | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_47, '#skF_4') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_1389])).
% 5.92/2.18  tff(c_1395, plain, (![B_275, B_47]: (v3_pre_topc('#skF_1'('#skF_3', B_275, '#skF_2'('#skF_4', B_47)), '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_47), B_275) | ~v2_tex_2(B_275, '#skF_3') | ~m1_subset_1(B_275, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_47, '#skF_4') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1392])).
% 5.92/2.18  tff(c_440, plain, (![B_113, C_114]: (m1_subset_1('#skF_1'('#skF_3', B_113, C_114), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(C_114, B_113) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_113, '#skF_3') | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_323, c_323, c_435])).
% 5.92/2.18  tff(c_606, plain, (![A_128, B_129, C_130]: (k9_subset_1(u1_struct_0(A_128), B_129, '#skF_1'(A_128, B_129, C_130))=C_130 | ~r1_tarski(C_130, B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(A_128))) | ~v2_tex_2(B_129, A_128) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.18  tff(c_612, plain, (![B_129, C_130]: (k9_subset_1(u1_struct_0('#skF_3'), B_129, '#skF_1'('#skF_3', B_129, C_130))=C_130 | ~r1_tarski(C_130, B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_129, '#skF_3') | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_323, c_606])).
% 5.92/2.18  tff(c_691, plain, (![B_142, C_143]: (k9_subset_1(u1_struct_0('#skF_4'), B_142, '#skF_1'('#skF_3', B_142, C_143))=C_143 | ~r1_tarski(C_143, B_142) | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_323, c_323, c_612])).
% 5.92/2.18  tff(c_701, plain, (![B_142, B_47]: (k9_subset_1(u1_struct_0('#skF_4'), B_142, '#skF_1'('#skF_3', B_142, '#skF_2'('#skF_4', B_47)))='#skF_2'('#skF_4', B_47) | ~r1_tarski('#skF_2'('#skF_4', B_47), B_142) | ~v2_tex_2(B_142, '#skF_3') | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_47, '#skF_4') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_691])).
% 5.92/2.18  tff(c_1090, plain, (![B_207, B_208]: (k9_subset_1(u1_struct_0('#skF_4'), B_207, '#skF_1'('#skF_3', B_207, '#skF_2'('#skF_4', B_208)))='#skF_2'('#skF_4', B_208) | ~r1_tarski('#skF_2'('#skF_4', B_208), B_207) | ~v2_tex_2(B_207, '#skF_3') | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_208, '#skF_4') | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_701])).
% 5.92/2.18  tff(c_20, plain, (![A_33, B_47, D_57]: (k9_subset_1(u1_struct_0(A_33), B_47, D_57)!='#skF_2'(A_33, B_47) | ~v3_pre_topc(D_57, A_33) | ~m1_subset_1(D_57, k1_zfmisc_1(u1_struct_0(A_33))) | v2_tex_2(B_47, A_33) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.92/2.18  tff(c_1097, plain, (![B_208, B_207]: ('#skF_2'('#skF_4', B_208)!='#skF_2'('#skF_4', B_207) | ~v3_pre_topc('#skF_1'('#skF_3', B_207, '#skF_2'('#skF_4', B_208)), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_207, '#skF_2'('#skF_4', B_208)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_207, '#skF_4') | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_208), B_207) | ~v2_tex_2(B_207, '#skF_3') | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_208, '#skF_4') | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_1090, c_20])).
% 5.92/2.18  tff(c_1807, plain, (![B_359, B_358]: ('#skF_2'('#skF_4', B_359)!='#skF_2'('#skF_4', B_358) | ~v3_pre_topc('#skF_1'('#skF_3', B_359, '#skF_2'('#skF_4', B_358)), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', B_359, '#skF_2'('#skF_4', B_358)), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_359, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_358), B_359) | ~v2_tex_2(B_359, '#skF_3') | ~m1_subset_1(B_359, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_358, '#skF_4') | ~m1_subset_1(B_358, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1097])).
% 5.92/2.18  tff(c_1813, plain, (![B_361, B_360]: ('#skF_2'('#skF_4', B_361)!='#skF_2'('#skF_4', B_360) | ~v3_pre_topc('#skF_1'('#skF_3', B_361, '#skF_2'('#skF_4', B_360)), '#skF_4') | v2_tex_2(B_361, '#skF_4') | v2_tex_2(B_360, '#skF_4') | ~m1_subset_1(B_360, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_360), B_361) | ~m1_subset_1('#skF_2'('#skF_4', B_360), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_361, '#skF_3') | ~m1_subset_1(B_361, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_440, c_1807])).
% 5.92/2.18  tff(c_1817, plain, (![B_363, B_362]: ('#skF_2'('#skF_4', B_363)!='#skF_2'('#skF_4', B_362) | v2_tex_2(B_363, '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', B_362), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_2'('#skF_4', B_362), B_363) | ~v2_tex_2(B_363, '#skF_3') | ~m1_subset_1(B_363, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_362, '#skF_4') | ~m1_subset_1(B_362, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1395, c_1813])).
% 5.92/2.18  tff(c_1820, plain, (![B_47, B_363]: ('#skF_2'('#skF_4', B_47)!='#skF_2'('#skF_4', B_363) | v2_tex_2(B_363, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_47), B_363) | ~v2_tex_2(B_363, '#skF_3') | ~m1_subset_1(B_363, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_47, '#skF_4') | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_1817])).
% 5.92/2.18  tff(c_1831, plain, (![B_367, B_366]: ('#skF_2'('#skF_4', B_367)!='#skF_2'('#skF_4', B_366) | v2_tex_2(B_367, '#skF_4') | ~r1_tarski('#skF_2'('#skF_4', B_366), B_367) | ~v2_tex_2(B_367, '#skF_3') | ~m1_subset_1(B_367, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_tex_2(B_366, '#skF_4') | ~m1_subset_1(B_366, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1820])).
% 5.92/2.18  tff(c_1843, plain, (~v2_tex_2('#skF_6', '#skF_3') | v2_tex_2('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_174, c_1831])).
% 5.92/2.18  tff(c_1854, plain, (v2_tex_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_48, c_1843])).
% 5.92/2.18  tff(c_1856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1854])).
% 5.92/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.92/2.18  
% 5.92/2.18  Inference rules
% 5.92/2.18  ----------------------
% 5.92/2.18  #Ref     : 6
% 5.92/2.18  #Sup     : 352
% 5.92/2.18  #Fact    : 0
% 5.92/2.18  #Define  : 0
% 5.92/2.18  #Split   : 9
% 5.92/2.18  #Chain   : 0
% 5.92/2.18  #Close   : 0
% 5.92/2.18  
% 5.92/2.18  Ordering : KBO
% 5.92/2.18  
% 5.92/2.18  Simplification rules
% 5.92/2.18  ----------------------
% 5.92/2.18  #Subsume      : 82
% 5.92/2.18  #Demod        : 495
% 5.92/2.18  #Tautology    : 118
% 5.92/2.18  #SimpNegUnit  : 8
% 5.92/2.18  #BackRed      : 9
% 5.92/2.18  
% 5.92/2.18  #Partial instantiations: 0
% 5.92/2.18  #Strategies tried      : 1
% 5.92/2.18  
% 5.92/2.18  Timing (in seconds)
% 5.92/2.18  ----------------------
% 5.92/2.18  Preprocessing        : 0.34
% 5.92/2.18  Parsing              : 0.18
% 5.92/2.18  CNF conversion       : 0.03
% 5.92/2.18  Main loop            : 1.05
% 5.92/2.18  Inferencing          : 0.40
% 5.92/2.18  Reduction            : 0.31
% 5.92/2.18  Demodulation         : 0.22
% 5.92/2.18  BG Simplification    : 0.03
% 5.92/2.18  Subsumption          : 0.25
% 5.92/2.18  Abstraction          : 0.04
% 5.92/2.18  MUC search           : 0.00
% 5.92/2.18  Cooper               : 0.00
% 5.92/2.18  Total                : 1.44
% 5.92/2.18  Index Insertion      : 0.00
% 5.92/2.18  Index Deletion       : 0.00
% 5.92/2.18  Index Matching       : 0.00
% 5.92/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
