%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:10 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.00s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 184 expanded)
%              Number of leaves         :   25 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 337 expanded)
%              Number of equality atoms :   26 (  77 expanded)
%              Maximal formula depth    :   11 (   4 average)
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

tff(f_76,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_61,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7311,plain,(
    ! [A_222,B_223] :
      ( r1_tarski(A_222,B_223)
      | ~ m1_subset_1(A_222,k1_zfmisc_1(B_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7323,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_7311])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7322,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_7311])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7327,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7322,c_6])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k3_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7335,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7327,c_4])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7295,plain,(
    ! [A_218,B_219] : k1_setfam_1(k2_tarski(A_218,B_219)) = k3_xboole_0(A_218,B_219) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7387,plain,(
    ! [B_227,A_228] : k1_setfam_1(k2_tarski(B_227,A_228)) = k3_xboole_0(A_228,B_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_7295])).

tff(c_12,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7410,plain,(
    ! [B_229,A_230] : k3_xboole_0(B_229,A_230) = k3_xboole_0(A_230,B_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_7387,c_12])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7425,plain,(
    ! [B_229,A_230,B_2] :
      ( r1_tarski(k3_xboole_0(B_229,A_230),B_2)
      | ~ r1_tarski(A_230,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7410,c_2])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_85,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_97,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_105,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_97,c_6])).

tff(c_142,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_4])).

tff(c_69,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_161,plain,(
    ! [B_43,A_44] : k1_setfam_1(k2_tarski(B_43,A_44)) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_167,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_12])).

tff(c_184,plain,(
    ! [B_45,A_46] : k3_xboole_0(B_45,A_46) = k3_xboole_0(A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_12])).

tff(c_229,plain,(
    ! [B_47,A_48] : r1_tarski(k3_xboole_0(B_47,A_48),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_4])).

tff(c_1166,plain,(
    ! [B_85,A_86] : k3_xboole_0(k3_xboole_0(B_85,A_86),A_86) = k3_xboole_0(B_85,A_86) ),
    inference(resolution,[status(thm)],[c_229,c_6])).

tff(c_1556,plain,(
    ! [A_92,B_93] : k3_xboole_0(A_92,k3_xboole_0(B_93,A_92)) = k3_xboole_0(B_93,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_1166,c_167])).

tff(c_1668,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,k3_xboole_0(B_43,A_44)) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_1556])).

tff(c_113,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(k3_xboole_0(A_40,C_41),B_42)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_905,plain,(
    ! [A_79,C_80,B_81] :
      ( k3_xboole_0(k3_xboole_0(A_79,C_80),B_81) = k3_xboole_0(A_79,C_80)
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(resolution,[status(thm)],[c_113,c_6])).

tff(c_4240,plain,(
    ! [B_157,A_158,C_159] :
      ( k3_xboole_0(B_157,k3_xboole_0(A_158,C_159)) = k3_xboole_0(A_158,C_159)
      | ~ r1_tarski(A_158,B_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_167])).

tff(c_6919,plain,(
    ! [A_204,C_205,B_206,B_207] :
      ( r1_tarski(k3_xboole_0(A_204,C_205),B_206)
      | ~ r1_tarski(B_207,B_206)
      | ~ r1_tarski(A_204,B_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4240,c_2])).

tff(c_6965,plain,(
    ! [A_208,C_209] :
      ( r1_tarski(k3_xboole_0(A_208,C_209),u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_208,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_97,c_6919])).

tff(c_22,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_471,plain,(
    ! [C_60,A_61,B_62] :
      ( v2_tex_2(C_60,A_61)
      | ~ v2_tex_2(B_62,A_61)
      | ~ r1_tarski(C_60,B_62)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1720,plain,(
    ! [A_97,C_98,A_99,B_100] :
      ( v2_tex_2(k3_xboole_0(A_97,C_98),A_99)
      | ~ v2_tex_2(B_100,A_99)
      | ~ m1_subset_1(k3_xboole_0(A_97,C_98),k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ r1_tarski(A_97,B_100) ) ),
    inference(resolution,[status(thm)],[c_2,c_471])).

tff(c_3656,plain,(
    ! [A_142,C_143,A_144,B_145] :
      ( v2_tex_2(k3_xboole_0(A_142,C_143),A_144)
      | ~ v2_tex_2(B_145,A_144)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ r1_tarski(A_142,B_145)
      | ~ r1_tarski(k3_xboole_0(A_142,C_143),u1_struct_0(A_144)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1720])).

tff(c_3663,plain,(
    ! [A_142,C_143] :
      ( v2_tex_2(k3_xboole_0(A_142,C_143),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_142,'#skF_2')
      | ~ r1_tarski(k3_xboole_0(A_142,C_143),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_3656])).

tff(c_3670,plain,(
    ! [A_142,C_143] :
      ( v2_tex_2(k3_xboole_0(A_142,C_143),'#skF_1')
      | ~ r1_tarski(A_142,'#skF_2')
      | ~ r1_tarski(k3_xboole_0(A_142,C_143),u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_3663])).

tff(c_7084,plain,(
    ! [A_210,C_211] :
      ( v2_tex_2(k3_xboole_0(A_210,C_211),'#skF_1')
      | ~ r1_tarski(A_210,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6965,c_3670])).

tff(c_7172,plain,(
    ! [A_212,B_213] :
      ( v2_tex_2(k3_xboole_0(A_212,B_213),'#skF_1')
      | ~ r1_tarski(B_213,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1668,c_7084])).

tff(c_259,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(A_49,B_50,C_51) = k3_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_267,plain,(
    ! [B_50] : k9_subset_1(u1_struct_0('#skF_1'),B_50,'#skF_3') = k3_xboole_0(B_50,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_259])).

tff(c_20,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_279,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_20])).

tff(c_280,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_279])).

tff(c_7175,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_7172,c_280])).

tff(c_7254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_7175])).

tff(c_7255,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_7697,plain,(
    ! [C_244,A_245,B_246] :
      ( v2_tex_2(C_244,A_245)
      | ~ v2_tex_2(B_246,A_245)
      | ~ r1_tarski(C_244,B_246)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8946,plain,(
    ! [A_281,C_282,A_283,B_284] :
      ( v2_tex_2(k3_xboole_0(A_281,C_282),A_283)
      | ~ v2_tex_2(B_284,A_283)
      | ~ m1_subset_1(k3_xboole_0(A_281,C_282),k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ m1_subset_1(B_284,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ l1_pre_topc(A_283)
      | ~ r1_tarski(A_281,B_284) ) ),
    inference(resolution,[status(thm)],[c_2,c_7697])).

tff(c_10883,plain,(
    ! [A_326,C_327,A_328,B_329] :
      ( v2_tex_2(k3_xboole_0(A_326,C_327),A_328)
      | ~ v2_tex_2(B_329,A_328)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328)
      | ~ r1_tarski(A_326,B_329)
      | ~ r1_tarski(k3_xboole_0(A_326,C_327),u1_struct_0(A_328)) ) ),
    inference(resolution,[status(thm)],[c_16,c_8946])).

tff(c_10888,plain,(
    ! [A_326,C_327] :
      ( v2_tex_2(k3_xboole_0(A_326,C_327),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_326,'#skF_3')
      | ~ r1_tarski(k3_xboole_0(A_326,C_327),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_10883])).

tff(c_11345,plain,(
    ! [A_337,C_338] :
      ( v2_tex_2(k3_xboole_0(A_337,C_338),'#skF_1')
      | ~ r1_tarski(A_337,'#skF_3')
      | ~ r1_tarski(k3_xboole_0(A_337,C_338),u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7255,c_10888])).

tff(c_11577,plain,(
    ! [B_347,A_348] :
      ( v2_tex_2(k3_xboole_0(B_347,A_348),'#skF_1')
      | ~ r1_tarski(B_347,'#skF_3')
      | ~ r1_tarski(A_348,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_7425,c_11345])).

tff(c_7393,plain,(
    ! [B_227,A_228] : k3_xboole_0(B_227,A_228) = k3_xboole_0(A_228,B_227) ),
    inference(superposition,[status(thm),theory(equality)],[c_7387,c_12])).

tff(c_7485,plain,(
    ! [A_233,B_234,C_235] :
      ( k9_subset_1(A_233,B_234,C_235) = k3_xboole_0(B_234,C_235)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(A_233)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7493,plain,(
    ! [B_234] : k9_subset_1(u1_struct_0('#skF_1'),B_234,'#skF_3') = k3_xboole_0(B_234,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_7485])).

tff(c_7505,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7493,c_20])).

tff(c_7506,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7393,c_7505])).

tff(c_11580,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_11577,c_7506])).

tff(c_11650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7323,c_7335,c_11580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:02:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.00/2.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.00/2.94  
% 8.00/2.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.00/2.94  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 8.00/2.94  
% 8.00/2.94  %Foreground sorts:
% 8.00/2.94  
% 8.00/2.94  
% 8.00/2.94  %Background operators:
% 8.00/2.94  
% 8.00/2.94  
% 8.00/2.94  %Foreground operators:
% 8.00/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.00/2.94  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.00/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.00/2.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.00/2.94  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.00/2.94  tff('#skF_2', type, '#skF_2': $i).
% 8.00/2.94  tff('#skF_3', type, '#skF_3': $i).
% 8.00/2.94  tff('#skF_1', type, '#skF_1': $i).
% 8.00/2.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.00/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.00/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.00/2.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.00/2.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.00/2.94  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.00/2.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.00/2.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.00/2.94  
% 8.00/2.96  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 8.00/2.96  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.00/2.96  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.00/2.96  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.00/2.96  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.00/2.96  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.00/2.96  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 8.00/2.96  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 8.00/2.96  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.00/2.96  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.00/2.96  tff(c_7311, plain, (![A_222, B_223]: (r1_tarski(A_222, B_223) | ~m1_subset_1(A_222, k1_zfmisc_1(B_223)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.00/2.96  tff(c_7323, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_7311])).
% 8.00/2.96  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.00/2.96  tff(c_7322, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_7311])).
% 8.00/2.96  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.00/2.96  tff(c_7327, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_7322, c_6])).
% 8.00/2.96  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k3_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.00/2.96  tff(c_7335, plain, (r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7327, c_4])).
% 8.00/2.96  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.00/2.96  tff(c_7295, plain, (![A_218, B_219]: (k1_setfam_1(k2_tarski(A_218, B_219))=k3_xboole_0(A_218, B_219))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.00/2.96  tff(c_7387, plain, (![B_227, A_228]: (k1_setfam_1(k2_tarski(B_227, A_228))=k3_xboole_0(A_228, B_227))), inference(superposition, [status(thm), theory('equality')], [c_8, c_7295])).
% 8.00/2.96  tff(c_12, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.00/2.96  tff(c_7410, plain, (![B_229, A_230]: (k3_xboole_0(B_229, A_230)=k3_xboole_0(A_230, B_229))), inference(superposition, [status(thm), theory('equality')], [c_7387, c_12])).
% 8.00/2.96  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.00/2.96  tff(c_7425, plain, (![B_229, A_230, B_2]: (r1_tarski(k3_xboole_0(B_229, A_230), B_2) | ~r1_tarski(A_230, B_2))), inference(superposition, [status(thm), theory('equality')], [c_7410, c_2])).
% 8.00/2.96  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.00/2.96  tff(c_85, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.00/2.96  tff(c_97, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_85])).
% 8.00/2.96  tff(c_105, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_97, c_6])).
% 8.00/2.96  tff(c_142, plain, (r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_105, c_4])).
% 8.00/2.96  tff(c_69, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.00/2.96  tff(c_161, plain, (![B_43, A_44]: (k1_setfam_1(k2_tarski(B_43, A_44))=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_8, c_69])).
% 8.00/2.96  tff(c_167, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_161, c_12])).
% 8.00/2.96  tff(c_184, plain, (![B_45, A_46]: (k3_xboole_0(B_45, A_46)=k3_xboole_0(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_161, c_12])).
% 8.00/2.96  tff(c_229, plain, (![B_47, A_48]: (r1_tarski(k3_xboole_0(B_47, A_48), A_48))), inference(superposition, [status(thm), theory('equality')], [c_184, c_4])).
% 8.00/2.96  tff(c_1166, plain, (![B_85, A_86]: (k3_xboole_0(k3_xboole_0(B_85, A_86), A_86)=k3_xboole_0(B_85, A_86))), inference(resolution, [status(thm)], [c_229, c_6])).
% 8.00/2.96  tff(c_1556, plain, (![A_92, B_93]: (k3_xboole_0(A_92, k3_xboole_0(B_93, A_92))=k3_xboole_0(B_93, A_92))), inference(superposition, [status(thm), theory('equality')], [c_1166, c_167])).
% 8.00/2.96  tff(c_1668, plain, (![B_43, A_44]: (k3_xboole_0(B_43, k3_xboole_0(B_43, A_44))=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_167, c_1556])).
% 8.00/2.96  tff(c_113, plain, (![A_40, C_41, B_42]: (r1_tarski(k3_xboole_0(A_40, C_41), B_42) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.00/2.96  tff(c_905, plain, (![A_79, C_80, B_81]: (k3_xboole_0(k3_xboole_0(A_79, C_80), B_81)=k3_xboole_0(A_79, C_80) | ~r1_tarski(A_79, B_81))), inference(resolution, [status(thm)], [c_113, c_6])).
% 8.00/2.96  tff(c_4240, plain, (![B_157, A_158, C_159]: (k3_xboole_0(B_157, k3_xboole_0(A_158, C_159))=k3_xboole_0(A_158, C_159) | ~r1_tarski(A_158, B_157))), inference(superposition, [status(thm), theory('equality')], [c_905, c_167])).
% 8.00/2.96  tff(c_6919, plain, (![A_204, C_205, B_206, B_207]: (r1_tarski(k3_xboole_0(A_204, C_205), B_206) | ~r1_tarski(B_207, B_206) | ~r1_tarski(A_204, B_207))), inference(superposition, [status(thm), theory('equality')], [c_4240, c_2])).
% 8.00/2.96  tff(c_6965, plain, (![A_208, C_209]: (r1_tarski(k3_xboole_0(A_208, C_209), u1_struct_0('#skF_1')) | ~r1_tarski(A_208, '#skF_2'))), inference(resolution, [status(thm)], [c_97, c_6919])).
% 8.00/2.96  tff(c_22, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.00/2.96  tff(c_30, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 8.00/2.96  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.00/2.96  tff(c_471, plain, (![C_60, A_61, B_62]: (v2_tex_2(C_60, A_61) | ~v2_tex_2(B_62, A_61) | ~r1_tarski(C_60, B_62) | ~m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.00/2.96  tff(c_1720, plain, (![A_97, C_98, A_99, B_100]: (v2_tex_2(k3_xboole_0(A_97, C_98), A_99) | ~v2_tex_2(B_100, A_99) | ~m1_subset_1(k3_xboole_0(A_97, C_98), k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~r1_tarski(A_97, B_100))), inference(resolution, [status(thm)], [c_2, c_471])).
% 8.00/2.96  tff(c_3656, plain, (![A_142, C_143, A_144, B_145]: (v2_tex_2(k3_xboole_0(A_142, C_143), A_144) | ~v2_tex_2(B_145, A_144) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144) | ~r1_tarski(A_142, B_145) | ~r1_tarski(k3_xboole_0(A_142, C_143), u1_struct_0(A_144)))), inference(resolution, [status(thm)], [c_16, c_1720])).
% 8.00/2.96  tff(c_3663, plain, (![A_142, C_143]: (v2_tex_2(k3_xboole_0(A_142, C_143), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_142, '#skF_2') | ~r1_tarski(k3_xboole_0(A_142, C_143), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_3656])).
% 8.00/2.96  tff(c_3670, plain, (![A_142, C_143]: (v2_tex_2(k3_xboole_0(A_142, C_143), '#skF_1') | ~r1_tarski(A_142, '#skF_2') | ~r1_tarski(k3_xboole_0(A_142, C_143), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_3663])).
% 8.00/2.96  tff(c_7084, plain, (![A_210, C_211]: (v2_tex_2(k3_xboole_0(A_210, C_211), '#skF_1') | ~r1_tarski(A_210, '#skF_2'))), inference(resolution, [status(thm)], [c_6965, c_3670])).
% 8.00/2.96  tff(c_7172, plain, (![A_212, B_213]: (v2_tex_2(k3_xboole_0(A_212, B_213), '#skF_1') | ~r1_tarski(B_213, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1668, c_7084])).
% 8.00/2.96  tff(c_259, plain, (![A_49, B_50, C_51]: (k9_subset_1(A_49, B_50, C_51)=k3_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.00/2.96  tff(c_267, plain, (![B_50]: (k9_subset_1(u1_struct_0('#skF_1'), B_50, '#skF_3')=k3_xboole_0(B_50, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_259])).
% 8.00/2.96  tff(c_20, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.00/2.96  tff(c_279, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_267, c_20])).
% 8.00/2.96  tff(c_280, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_279])).
% 8.00/2.96  tff(c_7175, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_7172, c_280])).
% 8.00/2.96  tff(c_7254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_7175])).
% 8.00/2.96  tff(c_7255, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 8.00/2.96  tff(c_7697, plain, (![C_244, A_245, B_246]: (v2_tex_2(C_244, A_245) | ~v2_tex_2(B_246, A_245) | ~r1_tarski(C_244, B_246) | ~m1_subset_1(C_244, k1_zfmisc_1(u1_struct_0(A_245))) | ~m1_subset_1(B_246, k1_zfmisc_1(u1_struct_0(A_245))) | ~l1_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.00/2.96  tff(c_8946, plain, (![A_281, C_282, A_283, B_284]: (v2_tex_2(k3_xboole_0(A_281, C_282), A_283) | ~v2_tex_2(B_284, A_283) | ~m1_subset_1(k3_xboole_0(A_281, C_282), k1_zfmisc_1(u1_struct_0(A_283))) | ~m1_subset_1(B_284, k1_zfmisc_1(u1_struct_0(A_283))) | ~l1_pre_topc(A_283) | ~r1_tarski(A_281, B_284))), inference(resolution, [status(thm)], [c_2, c_7697])).
% 8.00/2.96  tff(c_10883, plain, (![A_326, C_327, A_328, B_329]: (v2_tex_2(k3_xboole_0(A_326, C_327), A_328) | ~v2_tex_2(B_329, A_328) | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328) | ~r1_tarski(A_326, B_329) | ~r1_tarski(k3_xboole_0(A_326, C_327), u1_struct_0(A_328)))), inference(resolution, [status(thm)], [c_16, c_8946])).
% 8.00/2.96  tff(c_10888, plain, (![A_326, C_327]: (v2_tex_2(k3_xboole_0(A_326, C_327), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_326, '#skF_3') | ~r1_tarski(k3_xboole_0(A_326, C_327), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_10883])).
% 8.00/2.96  tff(c_11345, plain, (![A_337, C_338]: (v2_tex_2(k3_xboole_0(A_337, C_338), '#skF_1') | ~r1_tarski(A_337, '#skF_3') | ~r1_tarski(k3_xboole_0(A_337, C_338), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7255, c_10888])).
% 8.00/2.96  tff(c_11577, plain, (![B_347, A_348]: (v2_tex_2(k3_xboole_0(B_347, A_348), '#skF_1') | ~r1_tarski(B_347, '#skF_3') | ~r1_tarski(A_348, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_7425, c_11345])).
% 8.00/2.96  tff(c_7393, plain, (![B_227, A_228]: (k3_xboole_0(B_227, A_228)=k3_xboole_0(A_228, B_227))), inference(superposition, [status(thm), theory('equality')], [c_7387, c_12])).
% 8.00/2.96  tff(c_7485, plain, (![A_233, B_234, C_235]: (k9_subset_1(A_233, B_234, C_235)=k3_xboole_0(B_234, C_235) | ~m1_subset_1(C_235, k1_zfmisc_1(A_233)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.00/2.96  tff(c_7493, plain, (![B_234]: (k9_subset_1(u1_struct_0('#skF_1'), B_234, '#skF_3')=k3_xboole_0(B_234, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_7485])).
% 8.00/2.96  tff(c_7505, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7493, c_20])).
% 8.00/2.96  tff(c_7506, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7393, c_7505])).
% 8.00/2.96  tff(c_11580, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_11577, c_7506])).
% 8.00/2.96  tff(c_11650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7323, c_7335, c_11580])).
% 8.00/2.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.00/2.96  
% 8.00/2.96  Inference rules
% 8.00/2.96  ----------------------
% 8.00/2.96  #Ref     : 0
% 8.00/2.96  #Sup     : 3032
% 8.00/2.96  #Fact    : 0
% 8.00/2.96  #Define  : 0
% 8.00/2.96  #Split   : 5
% 8.00/2.96  #Chain   : 0
% 8.00/2.96  #Close   : 0
% 8.00/2.96  
% 8.00/2.96  Ordering : KBO
% 8.00/2.96  
% 8.00/2.96  Simplification rules
% 8.00/2.96  ----------------------
% 8.00/2.96  #Subsume      : 628
% 8.00/2.96  #Demod        : 3529
% 8.00/2.96  #Tautology    : 1433
% 8.00/2.96  #SimpNegUnit  : 17
% 8.00/2.96  #BackRed      : 2
% 8.00/2.96  
% 8.00/2.96  #Partial instantiations: 0
% 8.00/2.96  #Strategies tried      : 1
% 8.00/2.96  
% 8.00/2.96  Timing (in seconds)
% 8.00/2.96  ----------------------
% 8.00/2.96  Preprocessing        : 0.30
% 8.00/2.96  Parsing              : 0.16
% 8.00/2.96  CNF conversion       : 0.02
% 8.00/2.96  Main loop            : 1.77
% 8.00/2.96  Inferencing          : 0.43
% 8.00/2.96  Reduction            : 0.91
% 8.00/2.96  Demodulation         : 0.78
% 8.00/2.96  BG Simplification    : 0.05
% 8.00/2.96  Subsumption          : 0.29
% 8.00/2.96  Abstraction          : 0.09
% 8.00/2.96  MUC search           : 0.00
% 8.00/2.96  Cooper               : 0.00
% 8.00/2.96  Total                : 2.11
% 8.00/2.96  Index Insertion      : 0.00
% 8.00/2.96  Index Deletion       : 0.00
% 8.00/2.96  Index Matching       : 0.00
% 8.00/2.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
