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
% DateTime   : Thu Dec  3 10:30:05 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 709 expanded)
%              Number of leaves         :   29 ( 273 expanded)
%              Depth                    :   21
%              Number of atoms          :  288 (2663 expanded)
%              Number of equality atoms :   47 ( 211 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v1_tops_1(B,A)
                & v2_tex_2(B,A) )
             => v3_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

tff(f_80,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v1_tops_1(B,A)
                  & r1_tarski(B,C) )
               => v1_tops_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

tff(c_38,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_40,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_454,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1('#skF_1'(A_108,B_109),k1_zfmisc_1(u1_struct_0(A_108)))
      | v3_tex_2(B_109,A_108)
      | ~ v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_486,plain,(
    ! [A_108,B_109] :
      ( r1_tarski('#skF_1'(A_108,B_109),u1_struct_0(A_108))
      | v3_tex_2(B_109,A_108)
      | ~ v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(resolution,[status(thm)],[c_454,c_8])).

tff(c_343,plain,(
    ! [A_87,B_88] :
      ( '#skF_1'(A_87,B_88) != B_88
      | v3_tex_2(B_88,A_87)
      | ~ v2_tex_2(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_350,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_343])).

tff(c_354,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_350])).

tff(c_355,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_354])).

tff(c_98,plain,(
    ! [A_57,B_58,C_59] :
      ( k9_subset_1(A_57,B_58,C_59) = k3_xboole_0(B_58,C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [B_60] : k9_subset_1(u1_struct_0('#skF_3'),B_60,'#skF_4') = k3_xboole_0(B_60,'#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [A_48,B_49,C_50] :
      ( k9_subset_1(A_48,B_49,B_49) = B_49
      | ~ m1_subset_1(C_50,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [B_52,B_53,A_54] :
      ( k9_subset_1(B_52,B_53,B_53) = B_53
      | ~ r1_tarski(A_54,B_52) ) ),
    inference(resolution,[status(thm)],[c_10,c_62])).

tff(c_85,plain,(
    ! [A_1,B_53] : k9_subset_1(A_1,B_53,B_53) = B_53 ),
    inference(resolution,[status(thm)],[c_2,c_78])).

tff(c_112,plain,(
    k3_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_85])).

tff(c_125,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_2])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_42,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_327,plain,(
    ! [A_85,B_86] :
      ( k2_pre_topc(A_85,B_86) = u1_struct_0(A_85)
      | ~ v1_tops_1(B_86,A_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_334,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_327])).

tff(c_338,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_334])).

tff(c_765,plain,(
    ! [A_151,B_152,C_153] :
      ( k9_subset_1(u1_struct_0(A_151),B_152,k2_pre_topc(A_151,C_153)) = C_153
      | ~ r1_tarski(C_153,B_152)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ v2_tex_2(B_152,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_774,plain,(
    ! [B_152] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_152,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_152)
      | ~ v2_tex_2(B_152,'#skF_3')
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_765])).

tff(c_780,plain,(
    ! [B_152] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_152,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_152)
      | ~ v2_tex_2(B_152,'#skF_3')
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_338,c_774])).

tff(c_782,plain,(
    ! [B_154] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_154,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_154)
      | ~ v2_tex_2(B_154,'#skF_3')
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_780])).

tff(c_797,plain,
    ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_782])).

tff(c_808,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_125,c_797])).

tff(c_24,plain,(
    ! [A_21,B_27] :
      ( m1_subset_1('#skF_1'(A_21,B_27),k1_zfmisc_1(u1_struct_0(A_21)))
      | v3_tex_2(B_27,A_21)
      | ~ v2_tex_2(B_27,A_21)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_399,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(B_101,'#skF_1'(A_102,B_101))
      | v3_tex_2(B_101,A_102)
      | ~ v2_tex_2(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_404,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_399])).

tff(c_408,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_404])).

tff(c_409,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_408])).

tff(c_594,plain,(
    ! [C_118,A_119,B_120] :
      ( v1_tops_1(C_118,A_119)
      | ~ r1_tarski(B_120,C_118)
      | ~ v1_tops_1(B_120,A_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_667,plain,(
    ! [A_129] :
      ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),A_129)
      | ~ v1_tops_1('#skF_4',A_129)
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_409,c_594])).

tff(c_671,plain,
    ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_667])).

tff(c_677,plain,
    ( v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_42,c_671])).

tff(c_678,plain,(
    v1_tops_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_677])).

tff(c_16,plain,(
    ! [A_18,B_20] :
      ( k2_pre_topc(A_18,B_20) = u1_struct_0(A_18)
      | ~ v1_tops_1(B_20,A_18)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_886,plain,(
    ! [A_162,B_163] :
      ( k2_pre_topc(A_162,'#skF_1'(A_162,B_163)) = u1_struct_0(A_162)
      | ~ v1_tops_1('#skF_1'(A_162,B_163),A_162)
      | v3_tex_2(B_163,A_162)
      | ~ v2_tex_2(B_163,A_162)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(resolution,[status(thm)],[c_454,c_16])).

tff(c_888,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_678,c_886])).

tff(c_891,plain,
    ( k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_888])).

tff(c_892,plain,(
    k2_pre_topc('#skF_3','#skF_1'('#skF_3','#skF_4')) = u1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_891])).

tff(c_1392,plain,(
    ! [A_218,B_219,A_220] :
      ( k9_subset_1(u1_struct_0(A_218),B_219,k2_pre_topc(A_218,A_220)) = A_220
      | ~ r1_tarski(A_220,B_219)
      | ~ v2_tex_2(B_219,A_218)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218)
      | ~ r1_tarski(A_220,u1_struct_0(A_218)) ) ),
    inference(resolution,[status(thm)],[c_10,c_765])).

tff(c_1401,plain,(
    ! [A_220] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_220)) = A_220
      | ~ r1_tarski(A_220,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_220,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1392])).

tff(c_1407,plain,(
    ! [A_220] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_220)) = A_220
      | ~ r1_tarski(A_220,'#skF_4')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_220,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_1401])).

tff(c_1409,plain,(
    ! [A_221] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_221)) = A_221
      | ~ r1_tarski(A_221,'#skF_4')
      | ~ r1_tarski(A_221,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1407])).

tff(c_1422,plain,
    ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_1409])).

tff(c_1432,plain,
    ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_1422])).

tff(c_1433,plain,
    ( ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_1432])).

tff(c_1436,plain,(
    ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1433])).

tff(c_1439,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_486,c_1436])).

tff(c_1442,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_1439])).

tff(c_1444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1442])).

tff(c_1446,plain,(
    r1_tarski('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1433])).

tff(c_381,plain,(
    ! [A_93,B_94] :
      ( v2_tex_2('#skF_1'(A_93,B_94),A_93)
      | v3_tex_2(B_94,A_93)
      | ~ v2_tex_2(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_386,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_381])).

tff(c_390,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_386])).

tff(c_391,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_390])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] :
      ( k9_subset_1(A_6,B_7,C_8) = k3_xboole_0(B_7,C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_869,plain,(
    ! [A_159,B_160,B_161] :
      ( k9_subset_1(u1_struct_0(A_159),B_160,'#skF_1'(A_159,B_161)) = k3_xboole_0(B_160,'#skF_1'(A_159,B_161))
      | v3_tex_2(B_161,A_159)
      | ~ v2_tex_2(B_161,A_159)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_454,c_6])).

tff(c_878,plain,(
    ! [B_160] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_160,'#skF_1'('#skF_3','#skF_4')) = k3_xboole_0(B_160,'#skF_1'('#skF_3','#skF_4'))
      | v3_tex_2('#skF_4','#skF_3')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_869])).

tff(c_884,plain,(
    ! [B_160] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_160,'#skF_1'('#skF_3','#skF_4')) = k3_xboole_0(B_160,'#skF_1'('#skF_3','#skF_4'))
      | v3_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_878])).

tff(c_897,plain,(
    ! [B_164] : k9_subset_1(u1_struct_0('#skF_3'),B_164,'#skF_1'('#skF_3','#skF_4')) = k3_xboole_0(B_164,'#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_884])).

tff(c_904,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3','#skF_4')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_85])).

tff(c_944,plain,(
    r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_2])).

tff(c_1546,plain,(
    ! [A_230,A_231,A_232] :
      ( k9_subset_1(u1_struct_0(A_230),A_231,k2_pre_topc(A_230,A_232)) = A_232
      | ~ r1_tarski(A_232,A_231)
      | ~ v2_tex_2(A_231,A_230)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230)
      | ~ r1_tarski(A_232,u1_struct_0(A_230))
      | ~ r1_tarski(A_231,u1_struct_0(A_230)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1392])).

tff(c_1570,plain,(
    ! [A_231] :
      ( k9_subset_1(u1_struct_0('#skF_3'),A_231,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),A_231)
      | ~ v2_tex_2(A_231,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_231,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_1546])).

tff(c_1590,plain,(
    ! [A_231] :
      ( k9_subset_1(u1_struct_0('#skF_3'),A_231,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),A_231)
      | ~ v2_tex_2(A_231,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_231,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_48,c_46,c_1570])).

tff(c_1612,plain,(
    ! [A_235] :
      ( k9_subset_1(u1_struct_0('#skF_3'),A_235,u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),A_235)
      | ~ v2_tex_2(A_235,'#skF_3')
      | ~ r1_tarski(A_235,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1590])).

tff(c_805,plain,(
    ! [A_9] :
      ( k9_subset_1(u1_struct_0('#skF_3'),A_9,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_9)
      | ~ v2_tex_2(A_9,'#skF_3')
      | ~ r1_tarski(A_9,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_782])).

tff(c_1624,plain,(
    ! [A_235] :
      ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_4',A_235)
      | ~ v2_tex_2(A_235,'#skF_3')
      | ~ r1_tarski(A_235,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),A_235)
      | ~ v2_tex_2(A_235,'#skF_3')
      | ~ r1_tarski(A_235,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1612,c_805])).

tff(c_1669,plain,(
    ! [A_236] :
      ( ~ r1_tarski('#skF_4',A_236)
      | ~ v2_tex_2(A_236,'#skF_3')
      | ~ r1_tarski(A_236,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),A_236)
      | ~ v2_tex_2(A_236,'#skF_3')
      | ~ r1_tarski(A_236,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_1624])).

tff(c_1671,plain,
    ( ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1446,c_1669])).

tff(c_1689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1446,c_391,c_944,c_409,c_1671])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:14:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.93  
% 4.46/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.93  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.46/1.93  
% 4.46/1.93  %Foreground sorts:
% 4.46/1.93  
% 4.46/1.93  
% 4.46/1.93  %Background operators:
% 4.46/1.93  
% 4.46/1.93  
% 4.46/1.93  %Foreground operators:
% 4.46/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.46/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.93  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.46/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.46/1.93  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 4.46/1.93  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.46/1.93  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.46/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.46/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.46/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.93  tff('#skF_4', type, '#skF_4': $i).
% 4.46/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.46/1.93  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.46/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.46/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.46/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.46/1.93  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.46/1.93  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.46/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.46/1.93  
% 4.46/1.95  tff(f_116, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 4.46/1.95  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.46/1.95  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.46/1.95  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.46/1.95  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.46/1.95  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 4.46/1.95  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 4.46/1.95  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.46/1.95  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & r1_tarski(B, C)) => v1_tops_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tops_1)).
% 4.46/1.95  tff(c_38, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.46/1.95  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.46/1.95  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.46/1.95  tff(c_40, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.46/1.95  tff(c_454, plain, (![A_108, B_109]: (m1_subset_1('#skF_1'(A_108, B_109), k1_zfmisc_1(u1_struct_0(A_108))) | v3_tex_2(B_109, A_108) | ~v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.95  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.46/1.95  tff(c_486, plain, (![A_108, B_109]: (r1_tarski('#skF_1'(A_108, B_109), u1_struct_0(A_108)) | v3_tex_2(B_109, A_108) | ~v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(resolution, [status(thm)], [c_454, c_8])).
% 4.46/1.95  tff(c_343, plain, (![A_87, B_88]: ('#skF_1'(A_87, B_88)!=B_88 | v3_tex_2(B_88, A_87) | ~v2_tex_2(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.95  tff(c_350, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_343])).
% 4.46/1.95  tff(c_354, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_350])).
% 4.46/1.95  tff(c_355, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_38, c_354])).
% 4.46/1.95  tff(c_98, plain, (![A_57, B_58, C_59]: (k9_subset_1(A_57, B_58, C_59)=k3_xboole_0(B_58, C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.46/1.95  tff(c_105, plain, (![B_60]: (k9_subset_1(u1_struct_0('#skF_3'), B_60, '#skF_4')=k3_xboole_0(B_60, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_98])).
% 4.46/1.95  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.46/1.95  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.46/1.95  tff(c_62, plain, (![A_48, B_49, C_50]: (k9_subset_1(A_48, B_49, B_49)=B_49 | ~m1_subset_1(C_50, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.95  tff(c_78, plain, (![B_52, B_53, A_54]: (k9_subset_1(B_52, B_53, B_53)=B_53 | ~r1_tarski(A_54, B_52))), inference(resolution, [status(thm)], [c_10, c_62])).
% 4.46/1.95  tff(c_85, plain, (![A_1, B_53]: (k9_subset_1(A_1, B_53, B_53)=B_53)), inference(resolution, [status(thm)], [c_2, c_78])).
% 4.46/1.95  tff(c_112, plain, (k3_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_105, c_85])).
% 4.46/1.95  tff(c_125, plain, (r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_112, c_2])).
% 4.46/1.95  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.46/1.95  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.46/1.95  tff(c_42, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.46/1.95  tff(c_327, plain, (![A_85, B_86]: (k2_pre_topc(A_85, B_86)=u1_struct_0(A_85) | ~v1_tops_1(B_86, A_85) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.46/1.95  tff(c_334, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_327])).
% 4.46/1.95  tff(c_338, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_334])).
% 4.46/1.95  tff(c_765, plain, (![A_151, B_152, C_153]: (k9_subset_1(u1_struct_0(A_151), B_152, k2_pre_topc(A_151, C_153))=C_153 | ~r1_tarski(C_153, B_152) | ~m1_subset_1(C_153, k1_zfmisc_1(u1_struct_0(A_151))) | ~v2_tex_2(B_152, A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.46/1.95  tff(c_774, plain, (![B_152]: (k9_subset_1(u1_struct_0('#skF_3'), B_152, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_152) | ~v2_tex_2(B_152, '#skF_3') | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_765])).
% 4.46/1.95  tff(c_780, plain, (![B_152]: (k9_subset_1(u1_struct_0('#skF_3'), B_152, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_152) | ~v2_tex_2(B_152, '#skF_3') | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_338, c_774])).
% 4.46/1.95  tff(c_782, plain, (![B_154]: (k9_subset_1(u1_struct_0('#skF_3'), B_154, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_154) | ~v2_tex_2(B_154, '#skF_3') | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_780])).
% 4.46/1.95  tff(c_797, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_782])).
% 4.46/1.95  tff(c_808, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_125, c_797])).
% 4.46/1.95  tff(c_24, plain, (![A_21, B_27]: (m1_subset_1('#skF_1'(A_21, B_27), k1_zfmisc_1(u1_struct_0(A_21))) | v3_tex_2(B_27, A_21) | ~v2_tex_2(B_27, A_21) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.95  tff(c_399, plain, (![B_101, A_102]: (r1_tarski(B_101, '#skF_1'(A_102, B_101)) | v3_tex_2(B_101, A_102) | ~v2_tex_2(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.95  tff(c_404, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_399])).
% 4.46/1.95  tff(c_408, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_404])).
% 4.46/1.95  tff(c_409, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_408])).
% 4.46/1.95  tff(c_594, plain, (![C_118, A_119, B_120]: (v1_tops_1(C_118, A_119) | ~r1_tarski(B_120, C_118) | ~v1_tops_1(B_120, A_119) | ~m1_subset_1(C_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.46/1.95  tff(c_667, plain, (![A_129]: (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), A_129) | ~v1_tops_1('#skF_4', A_129) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(resolution, [status(thm)], [c_409, c_594])).
% 4.46/1.95  tff(c_671, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_667])).
% 4.46/1.95  tff(c_677, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_42, c_671])).
% 4.46/1.95  tff(c_678, plain, (v1_tops_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_677])).
% 4.46/1.95  tff(c_16, plain, (![A_18, B_20]: (k2_pre_topc(A_18, B_20)=u1_struct_0(A_18) | ~v1_tops_1(B_20, A_18) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.46/1.95  tff(c_886, plain, (![A_162, B_163]: (k2_pre_topc(A_162, '#skF_1'(A_162, B_163))=u1_struct_0(A_162) | ~v1_tops_1('#skF_1'(A_162, B_163), A_162) | v3_tex_2(B_163, A_162) | ~v2_tex_2(B_163, A_162) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(resolution, [status(thm)], [c_454, c_16])).
% 4.46/1.95  tff(c_888, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_678, c_886])).
% 4.46/1.95  tff(c_891, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_888])).
% 4.46/1.95  tff(c_892, plain, (k2_pre_topc('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=u1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_891])).
% 4.46/1.95  tff(c_1392, plain, (![A_218, B_219, A_220]: (k9_subset_1(u1_struct_0(A_218), B_219, k2_pre_topc(A_218, A_220))=A_220 | ~r1_tarski(A_220, B_219) | ~v2_tex_2(B_219, A_218) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218) | ~r1_tarski(A_220, u1_struct_0(A_218)))), inference(resolution, [status(thm)], [c_10, c_765])).
% 4.46/1.95  tff(c_1401, plain, (![A_220]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_220))=A_220 | ~r1_tarski(A_220, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_220, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_1392])).
% 4.46/1.95  tff(c_1407, plain, (![A_220]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_220))=A_220 | ~r1_tarski(A_220, '#skF_4') | v2_struct_0('#skF_3') | ~r1_tarski(A_220, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_1401])).
% 4.46/1.95  tff(c_1409, plain, (![A_221]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_221))=A_221 | ~r1_tarski(A_221, '#skF_4') | ~r1_tarski(A_221, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_1407])).
% 4.46/1.95  tff(c_1422, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_892, c_1409])).
% 4.46/1.95  tff(c_1432, plain, ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_1422])).
% 4.46/1.95  tff(c_1433, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_355, c_1432])).
% 4.46/1.95  tff(c_1436, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1433])).
% 4.46/1.95  tff(c_1439, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_486, c_1436])).
% 4.46/1.95  tff(c_1442, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_1439])).
% 4.46/1.95  tff(c_1444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1442])).
% 4.46/1.95  tff(c_1446, plain, (r1_tarski('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1433])).
% 4.46/1.95  tff(c_381, plain, (![A_93, B_94]: (v2_tex_2('#skF_1'(A_93, B_94), A_93) | v3_tex_2(B_94, A_93) | ~v2_tex_2(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.46/1.95  tff(c_386, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_381])).
% 4.46/1.95  tff(c_390, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_386])).
% 4.46/1.95  tff(c_391, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_390])).
% 4.46/1.95  tff(c_6, plain, (![A_6, B_7, C_8]: (k9_subset_1(A_6, B_7, C_8)=k3_xboole_0(B_7, C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.46/1.95  tff(c_869, plain, (![A_159, B_160, B_161]: (k9_subset_1(u1_struct_0(A_159), B_160, '#skF_1'(A_159, B_161))=k3_xboole_0(B_160, '#skF_1'(A_159, B_161)) | v3_tex_2(B_161, A_159) | ~v2_tex_2(B_161, A_159) | ~m1_subset_1(B_161, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(resolution, [status(thm)], [c_454, c_6])).
% 4.46/1.95  tff(c_878, plain, (![B_160]: (k9_subset_1(u1_struct_0('#skF_3'), B_160, '#skF_1'('#skF_3', '#skF_4'))=k3_xboole_0(B_160, '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_869])).
% 4.46/1.95  tff(c_884, plain, (![B_160]: (k9_subset_1(u1_struct_0('#skF_3'), B_160, '#skF_1'('#skF_3', '#skF_4'))=k3_xboole_0(B_160, '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_878])).
% 4.46/1.95  tff(c_897, plain, (![B_164]: (k9_subset_1(u1_struct_0('#skF_3'), B_164, '#skF_1'('#skF_3', '#skF_4'))=k3_xboole_0(B_164, '#skF_1'('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_38, c_884])).
% 4.46/1.95  tff(c_904, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', '#skF_4'))='#skF_1'('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_897, c_85])).
% 4.46/1.95  tff(c_944, plain, (r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_904, c_2])).
% 4.46/1.95  tff(c_1546, plain, (![A_230, A_231, A_232]: (k9_subset_1(u1_struct_0(A_230), A_231, k2_pre_topc(A_230, A_232))=A_232 | ~r1_tarski(A_232, A_231) | ~v2_tex_2(A_231, A_230) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230) | ~r1_tarski(A_232, u1_struct_0(A_230)) | ~r1_tarski(A_231, u1_struct_0(A_230)))), inference(resolution, [status(thm)], [c_10, c_1392])).
% 4.46/1.95  tff(c_1570, plain, (![A_231]: (k9_subset_1(u1_struct_0('#skF_3'), A_231, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), A_231) | ~v2_tex_2(A_231, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3')) | ~r1_tarski(A_231, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_892, c_1546])).
% 4.46/1.95  tff(c_1590, plain, (![A_231]: (k9_subset_1(u1_struct_0('#skF_3'), A_231, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), A_231) | ~v2_tex_2(A_231, '#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_231, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1446, c_48, c_46, c_1570])).
% 4.46/1.95  tff(c_1612, plain, (![A_235]: (k9_subset_1(u1_struct_0('#skF_3'), A_235, u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), A_235) | ~v2_tex_2(A_235, '#skF_3') | ~r1_tarski(A_235, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_50, c_1590])).
% 4.46/1.95  tff(c_805, plain, (![A_9]: (k9_subset_1(u1_struct_0('#skF_3'), A_9, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', A_9) | ~v2_tex_2(A_9, '#skF_3') | ~r1_tarski(A_9, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_782])).
% 4.46/1.95  tff(c_1624, plain, (![A_235]: ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', A_235) | ~v2_tex_2(A_235, '#skF_3') | ~r1_tarski(A_235, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), A_235) | ~v2_tex_2(A_235, '#skF_3') | ~r1_tarski(A_235, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1612, c_805])).
% 4.46/1.95  tff(c_1669, plain, (![A_236]: (~r1_tarski('#skF_4', A_236) | ~v2_tex_2(A_236, '#skF_3') | ~r1_tarski(A_236, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), A_236) | ~v2_tex_2(A_236, '#skF_3') | ~r1_tarski(A_236, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_355, c_1624])).
% 4.46/1.95  tff(c_1671, plain, (~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | ~r1_tarski('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1446, c_1669])).
% 4.46/1.95  tff(c_1689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1446, c_391, c_944, c_409, c_1671])).
% 4.46/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.95  
% 4.46/1.95  Inference rules
% 4.46/1.95  ----------------------
% 4.46/1.95  #Ref     : 0
% 4.46/1.95  #Sup     : 367
% 4.46/1.95  #Fact    : 0
% 4.46/1.95  #Define  : 0
% 4.46/1.95  #Split   : 6
% 4.46/1.95  #Chain   : 0
% 4.46/1.95  #Close   : 0
% 4.46/1.95  
% 4.46/1.95  Ordering : KBO
% 4.46/1.95  
% 4.46/1.95  Simplification rules
% 4.46/1.95  ----------------------
% 4.46/1.95  #Subsume      : 42
% 4.46/1.95  #Demod        : 248
% 4.46/1.95  #Tautology    : 158
% 4.46/1.95  #SimpNegUnit  : 46
% 4.46/1.95  #BackRed      : 0
% 4.46/1.95  
% 4.46/1.95  #Partial instantiations: 0
% 4.46/1.95  #Strategies tried      : 1
% 4.46/1.95  
% 4.46/1.95  Timing (in seconds)
% 4.46/1.95  ----------------------
% 4.46/1.96  Preprocessing        : 0.35
% 4.46/1.96  Parsing              : 0.19
% 4.46/1.96  CNF conversion       : 0.02
% 4.46/1.96  Main loop            : 0.71
% 4.46/1.96  Inferencing          : 0.27
% 4.46/1.96  Reduction            : 0.22
% 4.46/1.96  Demodulation         : 0.16
% 4.46/1.96  BG Simplification    : 0.03
% 4.46/1.96  Subsumption          : 0.14
% 4.46/1.96  Abstraction          : 0.04
% 4.46/1.96  MUC search           : 0.00
% 4.46/1.96  Cooper               : 0.00
% 4.46/1.96  Total                : 1.10
% 4.46/1.96  Index Insertion      : 0.00
% 4.46/1.96  Index Deletion       : 0.00
% 4.46/1.96  Index Matching       : 0.00
% 4.46/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
