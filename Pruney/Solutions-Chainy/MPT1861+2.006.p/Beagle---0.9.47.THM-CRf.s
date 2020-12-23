%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:10 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 129 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 233 expanded)
%              Number of equality atoms :   16 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [B_33,A_34] : k1_setfam_1(k2_tarski(B_33,A_34)) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_10,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_10])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_146,plain,(
    ! [A_39,B_40,C_41] :
      ( k9_subset_1(A_39,B_40,C_41) = k3_xboole_0(B_40,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    ! [B_42] : k9_subset_1(u1_struct_0('#skF_1'),B_42,'#skF_2') = k3_xboole_0(B_42,'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_146])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_163,plain,(
    ! [B_42] :
      ( m1_subset_1(k3_xboole_0(B_42,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_6])).

tff(c_171,plain,(
    ! [B_43] : m1_subset_1(k3_xboole_0(B_43,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_163])).

tff(c_181,plain,(
    ! [B_33] : m1_subset_1(k3_xboole_0('#skF_2',B_33),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_171])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_240,plain,(
    ! [C_48,A_49,B_50] :
      ( v2_tex_2(C_48,A_49)
      | ~ v2_tex_2(B_50,A_49)
      | ~ r1_tarski(C_48,B_50)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_568,plain,(
    ! [A_77,B_78,A_79] :
      ( v2_tex_2(k3_xboole_0(A_77,B_78),A_79)
      | ~ v2_tex_2(A_77,A_79)
      | ~ m1_subset_1(k3_xboole_0(A_77,B_78),k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ m1_subset_1(A_77,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_2,c_240])).

tff(c_598,plain,(
    ! [B_33] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_33),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_181,c_568])).

tff(c_647,plain,(
    ! [B_80] : v2_tex_2(k3_xboole_0('#skF_2',B_80),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_24,c_598])).

tff(c_651,plain,(
    ! [B_33] : v2_tex_2(k3_xboole_0(B_33,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_647])).

tff(c_154,plain,(
    ! [B_40] : k9_subset_1(u1_struct_0('#skF_1'),B_40,'#skF_3') = k3_xboole_0(B_40,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_146])).

tff(c_14,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_183,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_14])).

tff(c_184,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_183])).

tff(c_658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_184])).

tff(c_659,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_694,plain,(
    ! [A_83,B_84] : k1_setfam_1(k2_tarski(A_83,B_84)) = k3_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_709,plain,(
    ! [B_85,A_86] : k1_setfam_1(k2_tarski(B_85,A_86)) = k3_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_694])).

tff(c_715,plain,(
    ! [B_85,A_86] : k3_xboole_0(B_85,A_86) = k3_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_10])).

tff(c_771,plain,(
    ! [A_89,B_90,C_91] :
      ( k9_subset_1(A_89,B_90,C_91) = k3_xboole_0(B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_776,plain,(
    ! [B_90] : k9_subset_1(u1_struct_0('#skF_1'),B_90,'#skF_3') = k3_xboole_0(B_90,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_771])).

tff(c_809,plain,(
    ! [A_96,B_97,C_98] :
      ( m1_subset_1(k9_subset_1(A_96,B_97,C_98),k1_zfmisc_1(A_96))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_814,plain,(
    ! [B_90] :
      ( m1_subset_1(k3_xboole_0(B_90,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_776,c_809])).

tff(c_823,plain,(
    ! [B_99] : m1_subset_1(k3_xboole_0(B_99,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_814])).

tff(c_833,plain,(
    ! [B_85] : m1_subset_1(k3_xboole_0('#skF_3',B_85),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_823])).

tff(c_835,plain,(
    ! [C_100,A_101,B_102] :
      ( v2_tex_2(C_100,A_101)
      | ~ v2_tex_2(B_102,A_101)
      | ~ r1_tarski(C_100,B_102)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1130,plain,(
    ! [A_128,B_129,A_130] :
      ( v2_tex_2(k3_xboole_0(A_128,B_129),A_130)
      | ~ v2_tex_2(A_128,A_130)
      | ~ m1_subset_1(k3_xboole_0(A_128,B_129),k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ m1_subset_1(A_128,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_2,c_835])).

tff(c_1157,plain,(
    ! [B_85] :
      ( v2_tex_2(k3_xboole_0('#skF_3',B_85),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_833,c_1130])).

tff(c_1196,plain,(
    ! [B_85] : v2_tex_2(k3_xboole_0('#skF_3',B_85),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_659,c_1157])).

tff(c_798,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_14])).

tff(c_799,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_798])).

tff(c_1205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.56  
% 3.28/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.56  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.28/1.56  
% 3.28/1.56  %Foreground sorts:
% 3.28/1.56  
% 3.28/1.56  
% 3.28/1.56  %Background operators:
% 3.28/1.56  
% 3.28/1.56  
% 3.28/1.56  %Foreground operators:
% 3.28/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.28/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.56  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.28/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.28/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.28/1.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.28/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.28/1.56  
% 3.44/1.58  tff(f_68, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 3.44/1.58  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.44/1.58  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.44/1.58  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.44/1.58  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.44/1.58  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.44/1.58  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 3.44/1.58  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.58  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.58  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.58  tff(c_58, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.58  tff(c_74, plain, (![B_33, A_34]: (k1_setfam_1(k2_tarski(B_33, A_34))=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_4, c_58])).
% 3.44/1.58  tff(c_10, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.58  tff(c_80, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_74, c_10])).
% 3.44/1.58  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.58  tff(c_16, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.58  tff(c_24, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_16])).
% 3.44/1.58  tff(c_146, plain, (![A_39, B_40, C_41]: (k9_subset_1(A_39, B_40, C_41)=k3_xboole_0(B_40, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.58  tff(c_157, plain, (![B_42]: (k9_subset_1(u1_struct_0('#skF_1'), B_42, '#skF_2')=k3_xboole_0(B_42, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_146])).
% 3.44/1.58  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.44/1.58  tff(c_163, plain, (![B_42]: (m1_subset_1(k3_xboole_0(B_42, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_157, c_6])).
% 3.44/1.58  tff(c_171, plain, (![B_43]: (m1_subset_1(k3_xboole_0(B_43, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_163])).
% 3.44/1.58  tff(c_181, plain, (![B_33]: (m1_subset_1(k3_xboole_0('#skF_2', B_33), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_80, c_171])).
% 3.44/1.58  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.58  tff(c_240, plain, (![C_48, A_49, B_50]: (v2_tex_2(C_48, A_49) | ~v2_tex_2(B_50, A_49) | ~r1_tarski(C_48, B_50) | ~m1_subset_1(C_48, k1_zfmisc_1(u1_struct_0(A_49))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.44/1.58  tff(c_568, plain, (![A_77, B_78, A_79]: (v2_tex_2(k3_xboole_0(A_77, B_78), A_79) | ~v2_tex_2(A_77, A_79) | ~m1_subset_1(k3_xboole_0(A_77, B_78), k1_zfmisc_1(u1_struct_0(A_79))) | ~m1_subset_1(A_77, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_2, c_240])).
% 3.44/1.58  tff(c_598, plain, (![B_33]: (v2_tex_2(k3_xboole_0('#skF_2', B_33), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_181, c_568])).
% 3.44/1.58  tff(c_647, plain, (![B_80]: (v2_tex_2(k3_xboole_0('#skF_2', B_80), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_24, c_598])).
% 3.44/1.58  tff(c_651, plain, (![B_33]: (v2_tex_2(k3_xboole_0(B_33, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_647])).
% 3.44/1.58  tff(c_154, plain, (![B_40]: (k9_subset_1(u1_struct_0('#skF_1'), B_40, '#skF_3')=k3_xboole_0(B_40, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_146])).
% 3.44/1.58  tff(c_14, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.58  tff(c_183, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_14])).
% 3.44/1.58  tff(c_184, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_183])).
% 3.44/1.58  tff(c_658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_651, c_184])).
% 3.44/1.58  tff(c_659, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_16])).
% 3.44/1.58  tff(c_694, plain, (![A_83, B_84]: (k1_setfam_1(k2_tarski(A_83, B_84))=k3_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.58  tff(c_709, plain, (![B_85, A_86]: (k1_setfam_1(k2_tarski(B_85, A_86))=k3_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_4, c_694])).
% 3.44/1.58  tff(c_715, plain, (![B_85, A_86]: (k3_xboole_0(B_85, A_86)=k3_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_709, c_10])).
% 3.44/1.58  tff(c_771, plain, (![A_89, B_90, C_91]: (k9_subset_1(A_89, B_90, C_91)=k3_xboole_0(B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.58  tff(c_776, plain, (![B_90]: (k9_subset_1(u1_struct_0('#skF_1'), B_90, '#skF_3')=k3_xboole_0(B_90, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_771])).
% 3.44/1.58  tff(c_809, plain, (![A_96, B_97, C_98]: (m1_subset_1(k9_subset_1(A_96, B_97, C_98), k1_zfmisc_1(A_96)) | ~m1_subset_1(C_98, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.44/1.58  tff(c_814, plain, (![B_90]: (m1_subset_1(k3_xboole_0(B_90, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_776, c_809])).
% 3.44/1.58  tff(c_823, plain, (![B_99]: (m1_subset_1(k3_xboole_0(B_99, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_814])).
% 3.44/1.58  tff(c_833, plain, (![B_85]: (m1_subset_1(k3_xboole_0('#skF_3', B_85), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_715, c_823])).
% 3.44/1.58  tff(c_835, plain, (![C_100, A_101, B_102]: (v2_tex_2(C_100, A_101) | ~v2_tex_2(B_102, A_101) | ~r1_tarski(C_100, B_102) | ~m1_subset_1(C_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.44/1.58  tff(c_1130, plain, (![A_128, B_129, A_130]: (v2_tex_2(k3_xboole_0(A_128, B_129), A_130) | ~v2_tex_2(A_128, A_130) | ~m1_subset_1(k3_xboole_0(A_128, B_129), k1_zfmisc_1(u1_struct_0(A_130))) | ~m1_subset_1(A_128, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_2, c_835])).
% 3.44/1.58  tff(c_1157, plain, (![B_85]: (v2_tex_2(k3_xboole_0('#skF_3', B_85), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_833, c_1130])).
% 3.44/1.58  tff(c_1196, plain, (![B_85]: (v2_tex_2(k3_xboole_0('#skF_3', B_85), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_659, c_1157])).
% 3.44/1.58  tff(c_798, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_776, c_14])).
% 3.44/1.58  tff(c_799, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_715, c_798])).
% 3.44/1.58  tff(c_1205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1196, c_799])).
% 3.44/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.58  
% 3.44/1.58  Inference rules
% 3.44/1.58  ----------------------
% 3.44/1.58  #Ref     : 0
% 3.44/1.58  #Sup     : 268
% 3.44/1.58  #Fact    : 0
% 3.44/1.58  #Define  : 0
% 3.44/1.58  #Split   : 1
% 3.44/1.58  #Chain   : 0
% 3.44/1.58  #Close   : 0
% 3.44/1.58  
% 3.44/1.58  Ordering : KBO
% 3.44/1.58  
% 3.44/1.58  Simplification rules
% 3.44/1.58  ----------------------
% 3.44/1.58  #Subsume      : 3
% 3.44/1.58  #Demod        : 135
% 3.44/1.58  #Tautology    : 130
% 3.44/1.58  #SimpNegUnit  : 0
% 3.44/1.58  #BackRed      : 4
% 3.44/1.58  
% 3.44/1.58  #Partial instantiations: 0
% 3.44/1.58  #Strategies tried      : 1
% 3.44/1.58  
% 3.44/1.58  Timing (in seconds)
% 3.44/1.58  ----------------------
% 3.44/1.58  Preprocessing        : 0.31
% 3.44/1.58  Parsing              : 0.17
% 3.44/1.58  CNF conversion       : 0.02
% 3.44/1.58  Main loop            : 0.47
% 3.44/1.58  Inferencing          : 0.16
% 3.44/1.58  Reduction            : 0.19
% 3.44/1.58  Demodulation         : 0.15
% 3.44/1.58  BG Simplification    : 0.02
% 3.44/1.58  Subsumption          : 0.06
% 3.44/1.58  Abstraction          : 0.03
% 3.44/1.58  MUC search           : 0.00
% 3.44/1.58  Cooper               : 0.00
% 3.44/1.58  Total                : 0.82
% 3.44/1.58  Index Insertion      : 0.00
% 3.44/1.58  Index Deletion       : 0.00
% 3.44/1.58  Index Matching       : 0.00
% 3.44/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
