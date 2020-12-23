%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:04 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 150 expanded)
%              Number of leaves         :   29 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  193 ( 517 expanded)
%              Number of equality atoms :   38 (  44 expanded)
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

tff(f_106,negated_conjecture,(
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

tff(f_70,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_89,axiom,(
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

tff(c_38,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_40,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_208,plain,(
    ! [A_69,B_70] :
      ( '#skF_1'(A_69,B_70) != B_70
      | v3_tex_2(B_70,A_69)
      | ~ v2_tex_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_215,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_208])).

tff(c_219,plain,
    ( '#skF_1'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_215])).

tff(c_220,plain,(
    '#skF_1'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_219])).

tff(c_236,plain,(
    ! [A_75,B_76] :
      ( v2_tex_2('#skF_1'(A_75,B_76),A_75)
      | v3_tex_2(B_76,A_75)
      | ~ v2_tex_2(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_241,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_236])).

tff(c_245,plain,
    ( v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_241])).

tff(c_246,plain,(
    v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_245])).

tff(c_248,plain,(
    ! [B_79,A_80] :
      ( r1_tarski(B_79,'#skF_1'(A_80,B_79))
      | v3_tex_2(B_79,A_80)
      | ~ v2_tex_2(B_79,A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_253,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_248])).

tff(c_257,plain,
    ( r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_253])).

tff(c_258,plain,(
    r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_257])).

tff(c_318,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1('#skF_1'(A_87,B_88),k1_zfmisc_1(u1_struct_0(A_87)))
      | v3_tex_2(B_88,A_87)
      | ~ v2_tex_2(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_390,plain,(
    ! [A_91,B_92] :
      ( r1_tarski('#skF_1'(A_91,B_92),u1_struct_0(A_91))
      | v3_tex_2(B_92,A_91)
      | ~ v2_tex_2(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_318,c_10])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_521,plain,(
    ! [A_102,B_103] :
      ( k3_xboole_0('#skF_1'(A_102,B_103),u1_struct_0(A_102)) = '#skF_1'(A_102,B_103)
      | v3_tex_2(B_103,A_102)
      | ~ v2_tex_2(B_103,A_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_390,c_4])).

tff(c_530,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_521])).

tff(c_538,plain,
    ( k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_530])).

tff(c_539,plain,(
    k3_xboole_0('#skF_1'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_538])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( k9_subset_1(A_8,B_9,C_10) = k3_xboole_0(B_9,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_798,plain,(
    ! [A_131,B_132,B_133] :
      ( k9_subset_1(u1_struct_0(A_131),B_132,'#skF_1'(A_131,B_133)) = k3_xboole_0(B_132,'#skF_1'(A_131,B_133))
      | v3_tex_2(B_133,A_131)
      | ~ v2_tex_2(B_133,A_131)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_318,c_8])).

tff(c_807,plain,(
    ! [B_132] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_132,'#skF_1'('#skF_3','#skF_4')) = k3_xboole_0(B_132,'#skF_1'('#skF_3','#skF_4'))
      | v3_tex_2('#skF_4','#skF_3')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_798])).

tff(c_813,plain,(
    ! [B_132] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_132,'#skF_1'('#skF_3','#skF_4')) = k3_xboole_0(B_132,'#skF_1'('#skF_3','#skF_4'))
      | v3_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_807])).

tff(c_814,plain,(
    ! [B_132] : k9_subset_1(u1_struct_0('#skF_3'),B_132,'#skF_1'('#skF_3','#skF_4')) = k3_xboole_0(B_132,'#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_813])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( k9_subset_1(A_5,C_7,B_6) = k9_subset_1(A_5,B_6,C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_989,plain,(
    ! [A_160,B_161,B_162] :
      ( k9_subset_1(u1_struct_0(A_160),B_161,'#skF_1'(A_160,B_162)) = k9_subset_1(u1_struct_0(A_160),'#skF_1'(A_160,B_162),B_161)
      | v3_tex_2(B_162,A_160)
      | ~ v2_tex_2(B_162,A_160)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(resolution,[status(thm)],[c_318,c_6])).

tff(c_998,plain,(
    ! [B_161] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_161,'#skF_1'('#skF_3','#skF_4')) = k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4'),B_161)
      | v3_tex_2('#skF_4','#skF_3')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_989])).

tff(c_1004,plain,(
    ! [B_161] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4'),B_161) = k3_xboole_0(B_161,'#skF_1'('#skF_3','#skF_4'))
      | v3_tex_2('#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_814,c_998])).

tff(c_1006,plain,(
    ! [B_163] : k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4'),B_163) = k3_xboole_0(B_163,'#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1004])).

tff(c_24,plain,(
    ! [A_16,B_22] :
      ( m1_subset_1('#skF_1'(A_16,B_22),k1_zfmisc_1(u1_struct_0(A_16)))
      | v3_tex_2(B_22,A_16)
      | ~ v2_tex_2(B_22,A_16)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_42,plain,(
    v1_tops_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_173,plain,(
    ! [A_63,B_64] :
      ( k2_pre_topc(A_63,B_64) = u1_struct_0(A_63)
      | ~ v1_tops_1(B_64,A_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_180,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_173])).

tff(c_184,plain,(
    k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_180])).

tff(c_698,plain,(
    ! [A_120,B_121,C_122] :
      ( k9_subset_1(u1_struct_0(A_120),B_121,k2_pre_topc(A_120,C_122)) = C_122
      | ~ r1_tarski(C_122,B_121)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ v2_tex_2(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_707,plain,(
    ! [B_121] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_121,k2_pre_topc('#skF_3','#skF_4')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_121)
      | ~ v2_tex_2(B_121,'#skF_3')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_698])).

tff(c_713,plain,(
    ! [B_121] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_121,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_121)
      | ~ v2_tex_2(B_121,'#skF_3')
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_184,c_707])).

tff(c_715,plain,(
    ! [B_123] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_123,u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4',B_123)
      | ~ v2_tex_2(B_123,'#skF_3')
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_713])).

tff(c_723,plain,(
    ! [B_22] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_22),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_22))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_22),'#skF_3')
      | v3_tex_2(B_22,'#skF_3')
      | ~ v2_tex_2(B_22,'#skF_3')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_715])).

tff(c_737,plain,(
    ! [B_22] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3',B_22),u1_struct_0('#skF_3')) = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_1'('#skF_3',B_22))
      | ~ v2_tex_2('#skF_1'('#skF_3',B_22),'#skF_3')
      | v3_tex_2(B_22,'#skF_3')
      | ~ v2_tex_2(B_22,'#skF_3')
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_723])).

tff(c_1017,plain,
    ( k3_xboole_0(u1_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1006,c_737])).

tff(c_1070,plain,
    ( '#skF_1'('#skF_3','#skF_4') = '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_246,c_258,c_539,c_2,c_1017])).

tff(c_1072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_220,c_1070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n008.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:34:00 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.50  
% 3.41/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.50  %$ v3_tex_2 > v2_tex_2 > v1_tops_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.41/1.50  
% 3.41/1.50  %Foreground sorts:
% 3.41/1.50  
% 3.41/1.50  
% 3.41/1.50  %Background operators:
% 3.41/1.50  
% 3.41/1.50  
% 3.41/1.50  %Foreground operators:
% 3.41/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.41/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.41/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.50  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 3.41/1.50  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.41/1.50  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.41/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.41/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.41/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.41/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.41/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.41/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.41/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.41/1.51  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.41/1.51  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.41/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.41/1.51  
% 3.41/1.52  tff(f_106, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_tops_1(B, A) & v2_tex_2(B, A)) => v3_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tex_2)).
% 3.41/1.52  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.41/1.52  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.41/1.52  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.41/1.52  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.41/1.52  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.41/1.52  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.41/1.52  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 3.41/1.52  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.41/1.52  tff(c_38, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.52  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.52  tff(c_40, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.52  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.52  tff(c_208, plain, (![A_69, B_70]: ('#skF_1'(A_69, B_70)!=B_70 | v3_tex_2(B_70, A_69) | ~v2_tex_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.41/1.52  tff(c_215, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_208])).
% 3.41/1.52  tff(c_219, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_215])).
% 3.41/1.52  tff(c_220, plain, ('#skF_1'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_38, c_219])).
% 3.41/1.52  tff(c_236, plain, (![A_75, B_76]: (v2_tex_2('#skF_1'(A_75, B_76), A_75) | v3_tex_2(B_76, A_75) | ~v2_tex_2(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.41/1.52  tff(c_241, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_236])).
% 3.41/1.52  tff(c_245, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_241])).
% 3.41/1.52  tff(c_246, plain, (v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_245])).
% 3.41/1.52  tff(c_248, plain, (![B_79, A_80]: (r1_tarski(B_79, '#skF_1'(A_80, B_79)) | v3_tex_2(B_79, A_80) | ~v2_tex_2(B_79, A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.41/1.52  tff(c_253, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_248])).
% 3.41/1.52  tff(c_257, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_253])).
% 3.41/1.52  tff(c_258, plain, (r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_257])).
% 3.41/1.52  tff(c_318, plain, (![A_87, B_88]: (m1_subset_1('#skF_1'(A_87, B_88), k1_zfmisc_1(u1_struct_0(A_87))) | v3_tex_2(B_88, A_87) | ~v2_tex_2(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.41/1.52  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.41/1.52  tff(c_390, plain, (![A_91, B_92]: (r1_tarski('#skF_1'(A_91, B_92), u1_struct_0(A_91)) | v3_tex_2(B_92, A_91) | ~v2_tex_2(B_92, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_318, c_10])).
% 3.41/1.52  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.41/1.52  tff(c_521, plain, (![A_102, B_103]: (k3_xboole_0('#skF_1'(A_102, B_103), u1_struct_0(A_102))='#skF_1'(A_102, B_103) | v3_tex_2(B_103, A_102) | ~v2_tex_2(B_103, A_102) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(resolution, [status(thm)], [c_390, c_4])).
% 3.41/1.52  tff(c_530, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_521])).
% 3.41/1.52  tff(c_538, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_530])).
% 3.41/1.52  tff(c_539, plain, (k3_xboole_0('#skF_1'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))='#skF_1'('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_538])).
% 3.41/1.52  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.41/1.52  tff(c_8, plain, (![A_8, B_9, C_10]: (k9_subset_1(A_8, B_9, C_10)=k3_xboole_0(B_9, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.41/1.52  tff(c_798, plain, (![A_131, B_132, B_133]: (k9_subset_1(u1_struct_0(A_131), B_132, '#skF_1'(A_131, B_133))=k3_xboole_0(B_132, '#skF_1'(A_131, B_133)) | v3_tex_2(B_133, A_131) | ~v2_tex_2(B_133, A_131) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_318, c_8])).
% 3.41/1.52  tff(c_807, plain, (![B_132]: (k9_subset_1(u1_struct_0('#skF_3'), B_132, '#skF_1'('#skF_3', '#skF_4'))=k3_xboole_0(B_132, '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_798])).
% 3.41/1.52  tff(c_813, plain, (![B_132]: (k9_subset_1(u1_struct_0('#skF_3'), B_132, '#skF_1'('#skF_3', '#skF_4'))=k3_xboole_0(B_132, '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_807])).
% 3.41/1.52  tff(c_814, plain, (![B_132]: (k9_subset_1(u1_struct_0('#skF_3'), B_132, '#skF_1'('#skF_3', '#skF_4'))=k3_xboole_0(B_132, '#skF_1'('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_38, c_813])).
% 3.41/1.52  tff(c_6, plain, (![A_5, C_7, B_6]: (k9_subset_1(A_5, C_7, B_6)=k9_subset_1(A_5, B_6, C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.41/1.52  tff(c_989, plain, (![A_160, B_161, B_162]: (k9_subset_1(u1_struct_0(A_160), B_161, '#skF_1'(A_160, B_162))=k9_subset_1(u1_struct_0(A_160), '#skF_1'(A_160, B_162), B_161) | v3_tex_2(B_162, A_160) | ~v2_tex_2(B_162, A_160) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(resolution, [status(thm)], [c_318, c_6])).
% 3.41/1.52  tff(c_998, plain, (![B_161]: (k9_subset_1(u1_struct_0('#skF_3'), B_161, '#skF_1'('#skF_3', '#skF_4'))=k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', '#skF_4'), B_161) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_989])).
% 3.41/1.52  tff(c_1004, plain, (![B_161]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', '#skF_4'), B_161)=k3_xboole_0(B_161, '#skF_1'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_814, c_998])).
% 3.41/1.52  tff(c_1006, plain, (![B_163]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', '#skF_4'), B_163)=k3_xboole_0(B_163, '#skF_1'('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_38, c_1004])).
% 3.41/1.52  tff(c_24, plain, (![A_16, B_22]: (m1_subset_1('#skF_1'(A_16, B_22), k1_zfmisc_1(u1_struct_0(A_16))) | v3_tex_2(B_22, A_16) | ~v2_tex_2(B_22, A_16) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.41/1.52  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.52  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.52  tff(c_42, plain, (v1_tops_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.52  tff(c_173, plain, (![A_63, B_64]: (k2_pre_topc(A_63, B_64)=u1_struct_0(A_63) | ~v1_tops_1(B_64, A_63) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.41/1.52  tff(c_180, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_173])).
% 3.41/1.52  tff(c_184, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_180])).
% 3.41/1.52  tff(c_698, plain, (![A_120, B_121, C_122]: (k9_subset_1(u1_struct_0(A_120), B_121, k2_pre_topc(A_120, C_122))=C_122 | ~r1_tarski(C_122, B_121) | ~m1_subset_1(C_122, k1_zfmisc_1(u1_struct_0(A_120))) | ~v2_tex_2(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.41/1.52  tff(c_707, plain, (![B_121]: (k9_subset_1(u1_struct_0('#skF_3'), B_121, k2_pre_topc('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', B_121) | ~v2_tex_2(B_121, '#skF_3') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_698])).
% 3.41/1.52  tff(c_713, plain, (![B_121]: (k9_subset_1(u1_struct_0('#skF_3'), B_121, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_121) | ~v2_tex_2(B_121, '#skF_3') | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_184, c_707])).
% 3.41/1.52  tff(c_715, plain, (![B_123]: (k9_subset_1(u1_struct_0('#skF_3'), B_123, u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', B_123) | ~v2_tex_2(B_123, '#skF_3') | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_713])).
% 3.41/1.52  tff(c_723, plain, (![B_22]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_22), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_22)) | ~v2_tex_2('#skF_1'('#skF_3', B_22), '#skF_3') | v3_tex_2(B_22, '#skF_3') | ~v2_tex_2(B_22, '#skF_3') | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_715])).
% 3.41/1.52  tff(c_737, plain, (![B_22]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', B_22), u1_struct_0('#skF_3'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', B_22)) | ~v2_tex_2('#skF_1'('#skF_3', B_22), '#skF_3') | v3_tex_2(B_22, '#skF_3') | ~v2_tex_2(B_22, '#skF_3') | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_723])).
% 3.41/1.52  tff(c_1017, plain, (k3_xboole_0(u1_struct_0('#skF_3'), '#skF_1'('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1006, c_737])).
% 3.41/1.52  tff(c_1070, plain, ('#skF_1'('#skF_3', '#skF_4')='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_246, c_258, c_539, c_2, c_1017])).
% 3.41/1.52  tff(c_1072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_220, c_1070])).
% 3.41/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.52  
% 3.41/1.52  Inference rules
% 3.41/1.52  ----------------------
% 3.41/1.52  #Ref     : 0
% 3.41/1.52  #Sup     : 230
% 3.41/1.52  #Fact    : 0
% 3.41/1.52  #Define  : 0
% 3.41/1.52  #Split   : 2
% 3.41/1.52  #Chain   : 0
% 3.41/1.52  #Close   : 0
% 3.41/1.52  
% 3.41/1.52  Ordering : KBO
% 3.41/1.52  
% 3.41/1.52  Simplification rules
% 3.41/1.52  ----------------------
% 3.41/1.52  #Subsume      : 39
% 3.41/1.52  #Demod        : 130
% 3.41/1.52  #Tautology    : 80
% 3.41/1.52  #SimpNegUnit  : 30
% 3.41/1.52  #BackRed      : 0
% 3.41/1.52  
% 3.41/1.52  #Partial instantiations: 0
% 3.41/1.52  #Strategies tried      : 1
% 3.41/1.52  
% 3.41/1.52  Timing (in seconds)
% 3.41/1.52  ----------------------
% 3.55/1.52  Preprocessing        : 0.32
% 3.55/1.52  Parsing              : 0.16
% 3.55/1.52  CNF conversion       : 0.02
% 3.55/1.52  Main loop            : 0.45
% 3.55/1.52  Inferencing          : 0.17
% 3.55/1.52  Reduction            : 0.14
% 3.55/1.52  Demodulation         : 0.10
% 3.55/1.52  BG Simplification    : 0.03
% 3.55/1.52  Subsumption          : 0.10
% 3.55/1.52  Abstraction          : 0.03
% 3.55/1.52  MUC search           : 0.00
% 3.55/1.52  Cooper               : 0.00
% 3.55/1.53  Total                : 0.80
% 3.55/1.53  Index Insertion      : 0.00
% 3.55/1.53  Index Deletion       : 0.00
% 3.55/1.53  Index Matching       : 0.00
% 3.55/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
