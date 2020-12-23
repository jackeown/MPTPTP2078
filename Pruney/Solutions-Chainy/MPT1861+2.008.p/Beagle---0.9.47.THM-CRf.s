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
% DateTime   : Thu Dec  3 10:29:10 EST 2020

% Result     : Theorem 6.31s
% Output     : CNFRefutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 129 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 252 expanded)
%              Number of equality atoms :   16 (  38 expanded)
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

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3188,plain,(
    ! [A_215,B_216] : k1_setfam_1(k2_tarski(A_215,B_216)) = k3_xboole_0(A_215,B_216) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3203,plain,(
    ! [B_217,A_218] : k1_setfam_1(k2_tarski(B_217,A_218)) = k3_xboole_0(A_218,B_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_3188])).

tff(c_10,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3226,plain,(
    ! [B_219,A_220] : k3_xboole_0(B_219,A_220) = k3_xboole_0(A_220,B_219) ),
    inference(superposition,[status(thm),theory(equality)],[c_3203,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3241,plain,(
    ! [B_219,A_220] : r1_tarski(k3_xboole_0(B_219,A_220),A_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_3226,c_2])).

tff(c_76,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [B_36,A_37] : k1_setfam_1(k2_tarski(B_36,A_37)) = k3_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_76])).

tff(c_97,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,A_37) = k3_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_10])).

tff(c_20,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_62,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_153,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_160,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_40,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_70,c_153])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_327,plain,(
    ! [C_66,A_67,B_68] :
      ( v2_tex_2(C_66,A_67)
      | ~ v2_tex_2(B_68,A_67)
      | ~ r1_tarski(C_66,B_68)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_722,plain,(
    ! [A_102,B_103,A_104] :
      ( v2_tex_2(k3_xboole_0(A_102,B_103),A_104)
      | ~ v2_tex_2(A_102,A_104)
      | ~ m1_subset_1(k3_xboole_0(A_102,B_103),k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m1_subset_1(A_102,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_2,c_327])).

tff(c_1052,plain,(
    ! [A_128,B_129,A_130] :
      ( v2_tex_2(k3_xboole_0(A_128,B_129),A_130)
      | ~ v2_tex_2(A_128,A_130)
      | ~ m1_subset_1(A_128,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130)
      | ~ r1_tarski(k3_xboole_0(A_128,B_129),u1_struct_0(A_130)) ) ),
    inference(resolution,[status(thm)],[c_14,c_722])).

tff(c_1116,plain,(
    ! [A_128,B_129] :
      ( v2_tex_2(k3_xboole_0(A_128,B_129),'#skF_1')
      | ~ v2_tex_2(A_128,'#skF_1')
      | ~ m1_subset_1(A_128,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_128,B_129),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_160,c_1052])).

tff(c_3104,plain,(
    ! [A_206,B_207] :
      ( v2_tex_2(k3_xboole_0(A_206,B_207),'#skF_1')
      | ~ v2_tex_2(A_206,'#skF_1')
      | ~ m1_subset_1(A_206,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_206,B_207),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1116])).

tff(c_3111,plain,(
    ! [B_207] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_207),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_2',B_207),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_3104])).

tff(c_3117,plain,(
    ! [B_208] : v2_tex_2(k3_xboole_0('#skF_2',B_208),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28,c_3111])).

tff(c_3129,plain,(
    ! [B_36] : v2_tex_2(k3_xboole_0(B_36,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_3117])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_250,plain,(
    ! [A_56,B_57,C_58] :
      ( k9_subset_1(A_56,B_57,C_58) = k3_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_258,plain,(
    ! [B_57] : k9_subset_1(u1_struct_0('#skF_1'),B_57,'#skF_3') = k3_xboole_0(B_57,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_250])).

tff(c_18,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_358,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_18])).

tff(c_359,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_358])).

tff(c_3138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3129,c_359])).

tff(c_3139,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_3174,plain,(
    ! [A_211,B_212] :
      ( r1_tarski(A_211,B_212)
      | ~ m1_subset_1(A_211,k1_zfmisc_1(B_212)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3182,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_3174])).

tff(c_3265,plain,(
    ! [A_221,C_222,B_223] :
      ( r1_tarski(A_221,C_222)
      | ~ r1_tarski(B_223,C_222)
      | ~ r1_tarski(A_221,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3272,plain,(
    ! [A_221] :
      ( r1_tarski(A_221,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_221,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3182,c_3265])).

tff(c_3435,plain,(
    ! [C_247,A_248,B_249] :
      ( v2_tex_2(C_247,A_248)
      | ~ v2_tex_2(B_249,A_248)
      | ~ r1_tarski(C_247,B_249)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_pre_topc(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3781,plain,(
    ! [A_278,B_279,A_280] :
      ( v2_tex_2(k3_xboole_0(A_278,B_279),A_280)
      | ~ v2_tex_2(A_278,A_280)
      | ~ m1_subset_1(k3_xboole_0(A_278,B_279),k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ m1_subset_1(A_278,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(resolution,[status(thm)],[c_2,c_3435])).

tff(c_4058,plain,(
    ! [A_303,B_304,A_305] :
      ( v2_tex_2(k3_xboole_0(A_303,B_304),A_305)
      | ~ v2_tex_2(A_303,A_305)
      | ~ m1_subset_1(A_303,k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ l1_pre_topc(A_305)
      | ~ r1_tarski(k3_xboole_0(A_303,B_304),u1_struct_0(A_305)) ) ),
    inference(resolution,[status(thm)],[c_14,c_3781])).

tff(c_4116,plain,(
    ! [A_303,B_304] :
      ( v2_tex_2(k3_xboole_0(A_303,B_304),'#skF_1')
      | ~ v2_tex_2(A_303,'#skF_1')
      | ~ m1_subset_1(A_303,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_303,B_304),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3272,c_4058])).

tff(c_7018,plain,(
    ! [A_390,B_391] :
      ( v2_tex_2(k3_xboole_0(A_390,B_391),'#skF_1')
      | ~ v2_tex_2(A_390,'#skF_1')
      | ~ m1_subset_1(A_390,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_390,B_391),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4116])).

tff(c_7023,plain,(
    ! [B_391] :
      ( v2_tex_2(k3_xboole_0('#skF_3',B_391),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_3',B_391),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_7018])).

tff(c_7033,plain,(
    ! [B_392] :
      ( v2_tex_2(k3_xboole_0('#skF_3',B_392),'#skF_1')
      | ~ r1_tarski(k3_xboole_0('#skF_3',B_392),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3139,c_7023])).

tff(c_3209,plain,(
    ! [B_217,A_218] : k3_xboole_0(B_217,A_218) = k3_xboole_0(A_218,B_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_3203,c_10])).

tff(c_3293,plain,(
    ! [A_227,B_228,C_229] :
      ( k9_subset_1(A_227,B_228,C_229) = k3_xboole_0(B_228,C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(A_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3301,plain,(
    ! [B_228] : k9_subset_1(u1_struct_0('#skF_1'),B_228,'#skF_3') = k3_xboole_0(B_228,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_3293])).

tff(c_3469,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3301,c_18])).

tff(c_3470,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3209,c_3469])).

tff(c_7036,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7033,c_3470])).

tff(c_7056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3241,c_7036])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.31/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.25  
% 6.31/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.25  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 6.31/2.25  
% 6.31/2.25  %Foreground sorts:
% 6.31/2.25  
% 6.31/2.25  
% 6.31/2.25  %Background operators:
% 6.31/2.25  
% 6.31/2.25  
% 6.31/2.25  %Foreground operators:
% 6.31/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.31/2.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.31/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.31/2.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.31/2.25  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.31/2.25  tff('#skF_2', type, '#skF_2': $i).
% 6.31/2.25  tff('#skF_3', type, '#skF_3': $i).
% 6.31/2.25  tff('#skF_1', type, '#skF_1': $i).
% 6.31/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.31/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.31/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.31/2.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.31/2.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.31/2.25  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.31/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.31/2.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.31/2.25  
% 6.31/2.27  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.31/2.27  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.31/2.27  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.31/2.27  tff(f_74, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 6.31/2.27  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.31/2.27  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.31/2.27  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 6.31/2.27  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 6.31/2.27  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.31/2.27  tff(c_3188, plain, (![A_215, B_216]: (k1_setfam_1(k2_tarski(A_215, B_216))=k3_xboole_0(A_215, B_216))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.31/2.27  tff(c_3203, plain, (![B_217, A_218]: (k1_setfam_1(k2_tarski(B_217, A_218))=k3_xboole_0(A_218, B_217))), inference(superposition, [status(thm), theory('equality')], [c_6, c_3188])).
% 6.31/2.27  tff(c_10, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.31/2.27  tff(c_3226, plain, (![B_219, A_220]: (k3_xboole_0(B_219, A_220)=k3_xboole_0(A_220, B_219))), inference(superposition, [status(thm), theory('equality')], [c_3203, c_10])).
% 6.31/2.27  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.31/2.27  tff(c_3241, plain, (![B_219, A_220]: (r1_tarski(k3_xboole_0(B_219, A_220), A_220))), inference(superposition, [status(thm), theory('equality')], [c_3226, c_2])).
% 6.31/2.27  tff(c_76, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.31/2.27  tff(c_91, plain, (![B_36, A_37]: (k1_setfam_1(k2_tarski(B_36, A_37))=k3_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_6, c_76])).
% 6.31/2.27  tff(c_97, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k3_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_91, c_10])).
% 6.31/2.27  tff(c_20, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.31/2.27  tff(c_28, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_20])).
% 6.31/2.27  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.31/2.27  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.31/2.27  tff(c_62, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.31/2.27  tff(c_70, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_62])).
% 6.31/2.27  tff(c_153, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.31/2.27  tff(c_160, plain, (![A_40]: (r1_tarski(A_40, u1_struct_0('#skF_1')) | ~r1_tarski(A_40, '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_153])).
% 6.31/2.27  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.31/2.27  tff(c_327, plain, (![C_66, A_67, B_68]: (v2_tex_2(C_66, A_67) | ~v2_tex_2(B_68, A_67) | ~r1_tarski(C_66, B_68) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.31/2.27  tff(c_722, plain, (![A_102, B_103, A_104]: (v2_tex_2(k3_xboole_0(A_102, B_103), A_104) | ~v2_tex_2(A_102, A_104) | ~m1_subset_1(k3_xboole_0(A_102, B_103), k1_zfmisc_1(u1_struct_0(A_104))) | ~m1_subset_1(A_102, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_2, c_327])).
% 6.31/2.27  tff(c_1052, plain, (![A_128, B_129, A_130]: (v2_tex_2(k3_xboole_0(A_128, B_129), A_130) | ~v2_tex_2(A_128, A_130) | ~m1_subset_1(A_128, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130) | ~r1_tarski(k3_xboole_0(A_128, B_129), u1_struct_0(A_130)))), inference(resolution, [status(thm)], [c_14, c_722])).
% 6.31/2.27  tff(c_1116, plain, (![A_128, B_129]: (v2_tex_2(k3_xboole_0(A_128, B_129), '#skF_1') | ~v2_tex_2(A_128, '#skF_1') | ~m1_subset_1(A_128, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_128, B_129), '#skF_2'))), inference(resolution, [status(thm)], [c_160, c_1052])).
% 6.31/2.27  tff(c_3104, plain, (![A_206, B_207]: (v2_tex_2(k3_xboole_0(A_206, B_207), '#skF_1') | ~v2_tex_2(A_206, '#skF_1') | ~m1_subset_1(A_206, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_206, B_207), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1116])).
% 6.31/2.27  tff(c_3111, plain, (![B_207]: (v2_tex_2(k3_xboole_0('#skF_2', B_207), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_2', B_207), '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_3104])).
% 6.31/2.27  tff(c_3117, plain, (![B_208]: (v2_tex_2(k3_xboole_0('#skF_2', B_208), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28, c_3111])).
% 6.31/2.27  tff(c_3129, plain, (![B_36]: (v2_tex_2(k3_xboole_0(B_36, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_3117])).
% 6.31/2.27  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.31/2.27  tff(c_250, plain, (![A_56, B_57, C_58]: (k9_subset_1(A_56, B_57, C_58)=k3_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.31/2.27  tff(c_258, plain, (![B_57]: (k9_subset_1(u1_struct_0('#skF_1'), B_57, '#skF_3')=k3_xboole_0(B_57, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_250])).
% 6.31/2.27  tff(c_18, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.31/2.27  tff(c_358, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_258, c_18])).
% 6.31/2.27  tff(c_359, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_358])).
% 6.31/2.27  tff(c_3138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3129, c_359])).
% 6.31/2.27  tff(c_3139, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_20])).
% 6.31/2.27  tff(c_3174, plain, (![A_211, B_212]: (r1_tarski(A_211, B_212) | ~m1_subset_1(A_211, k1_zfmisc_1(B_212)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.31/2.27  tff(c_3182, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_3174])).
% 6.31/2.27  tff(c_3265, plain, (![A_221, C_222, B_223]: (r1_tarski(A_221, C_222) | ~r1_tarski(B_223, C_222) | ~r1_tarski(A_221, B_223))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.31/2.27  tff(c_3272, plain, (![A_221]: (r1_tarski(A_221, u1_struct_0('#skF_1')) | ~r1_tarski(A_221, '#skF_2'))), inference(resolution, [status(thm)], [c_3182, c_3265])).
% 6.31/2.27  tff(c_3435, plain, (![C_247, A_248, B_249]: (v2_tex_2(C_247, A_248) | ~v2_tex_2(B_249, A_248) | ~r1_tarski(C_247, B_249) | ~m1_subset_1(C_247, k1_zfmisc_1(u1_struct_0(A_248))) | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_pre_topc(A_248))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.31/2.27  tff(c_3781, plain, (![A_278, B_279, A_280]: (v2_tex_2(k3_xboole_0(A_278, B_279), A_280) | ~v2_tex_2(A_278, A_280) | ~m1_subset_1(k3_xboole_0(A_278, B_279), k1_zfmisc_1(u1_struct_0(A_280))) | ~m1_subset_1(A_278, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(resolution, [status(thm)], [c_2, c_3435])).
% 6.31/2.27  tff(c_4058, plain, (![A_303, B_304, A_305]: (v2_tex_2(k3_xboole_0(A_303, B_304), A_305) | ~v2_tex_2(A_303, A_305) | ~m1_subset_1(A_303, k1_zfmisc_1(u1_struct_0(A_305))) | ~l1_pre_topc(A_305) | ~r1_tarski(k3_xboole_0(A_303, B_304), u1_struct_0(A_305)))), inference(resolution, [status(thm)], [c_14, c_3781])).
% 6.31/2.27  tff(c_4116, plain, (![A_303, B_304]: (v2_tex_2(k3_xboole_0(A_303, B_304), '#skF_1') | ~v2_tex_2(A_303, '#skF_1') | ~m1_subset_1(A_303, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_303, B_304), '#skF_2'))), inference(resolution, [status(thm)], [c_3272, c_4058])).
% 6.31/2.27  tff(c_7018, plain, (![A_390, B_391]: (v2_tex_2(k3_xboole_0(A_390, B_391), '#skF_1') | ~v2_tex_2(A_390, '#skF_1') | ~m1_subset_1(A_390, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_390, B_391), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4116])).
% 6.31/2.27  tff(c_7023, plain, (![B_391]: (v2_tex_2(k3_xboole_0('#skF_3', B_391), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_3', B_391), '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_7018])).
% 6.31/2.27  tff(c_7033, plain, (![B_392]: (v2_tex_2(k3_xboole_0('#skF_3', B_392), '#skF_1') | ~r1_tarski(k3_xboole_0('#skF_3', B_392), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3139, c_7023])).
% 6.31/2.27  tff(c_3209, plain, (![B_217, A_218]: (k3_xboole_0(B_217, A_218)=k3_xboole_0(A_218, B_217))), inference(superposition, [status(thm), theory('equality')], [c_3203, c_10])).
% 6.31/2.27  tff(c_3293, plain, (![A_227, B_228, C_229]: (k9_subset_1(A_227, B_228, C_229)=k3_xboole_0(B_228, C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(A_227)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.31/2.27  tff(c_3301, plain, (![B_228]: (k9_subset_1(u1_struct_0('#skF_1'), B_228, '#skF_3')=k3_xboole_0(B_228, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_3293])).
% 6.31/2.27  tff(c_3469, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3301, c_18])).
% 6.31/2.27  tff(c_3470, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3209, c_3469])).
% 6.31/2.27  tff(c_7036, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_7033, c_3470])).
% 6.31/2.27  tff(c_7056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3241, c_7036])).
% 6.31/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.27  
% 6.31/2.27  Inference rules
% 6.31/2.27  ----------------------
% 6.31/2.27  #Ref     : 0
% 6.31/2.27  #Sup     : 1734
% 6.31/2.27  #Fact    : 0
% 6.31/2.27  #Define  : 0
% 6.31/2.27  #Split   : 5
% 6.31/2.27  #Chain   : 0
% 6.31/2.27  #Close   : 0
% 6.31/2.27  
% 6.31/2.27  Ordering : KBO
% 6.31/2.27  
% 6.31/2.27  Simplification rules
% 6.31/2.27  ----------------------
% 6.31/2.27  #Subsume      : 226
% 6.31/2.27  #Demod        : 504
% 6.31/2.27  #Tautology    : 599
% 6.31/2.27  #SimpNegUnit  : 3
% 6.31/2.27  #BackRed      : 3
% 6.31/2.27  
% 6.31/2.27  #Partial instantiations: 0
% 6.31/2.27  #Strategies tried      : 1
% 6.31/2.27  
% 6.31/2.27  Timing (in seconds)
% 6.31/2.27  ----------------------
% 6.31/2.27  Preprocessing        : 0.30
% 6.31/2.27  Parsing              : 0.16
% 6.31/2.27  CNF conversion       : 0.02
% 6.31/2.27  Main loop            : 1.22
% 6.31/2.27  Inferencing          : 0.37
% 6.31/2.27  Reduction            : 0.51
% 6.31/2.27  Demodulation         : 0.43
% 6.31/2.27  BG Simplification    : 0.04
% 6.31/2.27  Subsumption          : 0.21
% 6.31/2.27  Abstraction          : 0.06
% 6.31/2.27  MUC search           : 0.00
% 6.31/2.27  Cooper               : 0.00
% 6.31/2.27  Total                : 1.55
% 6.31/2.27  Index Insertion      : 0.00
% 6.31/2.27  Index Deletion       : 0.00
% 6.31/2.27  Index Matching       : 0.00
% 6.31/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
