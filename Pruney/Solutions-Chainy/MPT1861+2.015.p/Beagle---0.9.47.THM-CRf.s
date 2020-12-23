%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:11 EST 2020

% Result     : Theorem 8.75s
% Output     : CNFRefutation 9.11s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 210 expanded)
%              Number of leaves         :   27 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  171 ( 373 expanded)
%              Number of equality atoms :   29 (  77 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_80,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_65,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_82,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_82])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_98,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_90,c_6])).

tff(c_121,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_139,plain,(
    ! [A_48,B_49] : r1_tarski(k3_xboole_0(A_48,B_49),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_8])).

tff(c_145,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_139])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,(
    ! [A_55,B_56] : k3_xboole_0(k4_xboole_0(A_55,B_56),A_55) = k4_xboole_0(A_55,B_56) ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_233,plain,(
    ! [A_55,B_56] : k3_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_2])).

tff(c_210,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(k4_xboole_0(A_52,C_53),B_54)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1895,plain,(
    ! [A_108,C_109,B_110] :
      ( k3_xboole_0(k4_xboole_0(A_108,C_109),B_110) = k4_xboole_0(A_108,C_109)
      | ~ r1_tarski(A_108,B_110) ) ),
    inference(resolution,[status(thm)],[c_210,c_6])).

tff(c_2012,plain,(
    ! [A_10,B_11,B_110] :
      ( k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(k3_xboole_0(A_10,B_11),B_110)
      | ~ r1_tarski(A_10,B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1895])).

tff(c_2667,plain,(
    ! [A_124,B_125,B_126] :
      ( k3_xboole_0(k3_xboole_0(A_124,B_125),B_126) = k3_xboole_0(A_124,B_125)
      | ~ r1_tarski(A_124,B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2012])).

tff(c_455,plain,(
    ! [A_72,B_73,B_74] :
      ( r1_tarski(k3_xboole_0(A_72,B_73),B_74)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_210])).

tff(c_481,plain,(
    ! [A_1,B_2,B_74] :
      ( r1_tarski(k3_xboole_0(A_1,B_2),B_74)
      | ~ r1_tarski(B_2,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_455])).

tff(c_5699,plain,(
    ! [A_167,B_168,B_169,B_170] :
      ( r1_tarski(k3_xboole_0(A_167,B_168),B_169)
      | ~ r1_tarski(B_170,B_169)
      | ~ r1_tarski(A_167,B_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2667,c_481])).

tff(c_5872,plain,(
    ! [A_175,B_176] :
      ( r1_tarski(k3_xboole_0(A_175,B_176),u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_175,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_90,c_5699])).

tff(c_5946,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(k4_xboole_0(A_55,B_56),u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_55,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_5872])).

tff(c_26,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_396,plain,(
    ! [C_66,A_67,B_68] :
      ( v2_tex_2(C_66,A_67)
      | ~ v2_tex_2(B_68,A_67)
      | ~ r1_tarski(C_66,B_68)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2261,plain,(
    ! [A_116,C_117,A_118,B_119] :
      ( v2_tex_2(k4_xboole_0(A_116,C_117),A_118)
      | ~ v2_tex_2(B_119,A_118)
      | ~ m1_subset_1(k4_xboole_0(A_116,C_117),k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(B_119,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ r1_tarski(A_116,B_119) ) ),
    inference(resolution,[status(thm)],[c_4,c_396])).

tff(c_7492,plain,(
    ! [A_198,C_199,A_200,B_201] :
      ( v2_tex_2(k4_xboole_0(A_198,C_199),A_200)
      | ~ v2_tex_2(B_201,A_200)
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200)
      | ~ r1_tarski(A_198,B_201)
      | ~ r1_tarski(k4_xboole_0(A_198,C_199),u1_struct_0(A_200)) ) ),
    inference(resolution,[status(thm)],[c_20,c_2261])).

tff(c_7499,plain,(
    ! [A_198,C_199] :
      ( v2_tex_2(k4_xboole_0(A_198,C_199),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_198,'#skF_2')
      | ~ r1_tarski(k4_xboole_0(A_198,C_199),u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_7492])).

tff(c_7510,plain,(
    ! [A_202,C_203] :
      ( v2_tex_2(k4_xboole_0(A_202,C_203),'#skF_1')
      | ~ r1_tarski(A_202,'#skF_2')
      | ~ r1_tarski(k4_xboole_0(A_202,C_203),u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_7499])).

tff(c_7572,plain,(
    ! [A_204,B_205] :
      ( v2_tex_2(k4_xboole_0(A_204,B_205),'#skF_1')
      | ~ r1_tarski(A_204,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_5946,c_7510])).

tff(c_7590,plain,(
    ! [A_206,B_207] :
      ( v2_tex_2(k3_xboole_0(A_206,B_207),'#skF_1')
      | ~ r1_tarski(A_206,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_7572])).

tff(c_7801,plain,(
    ! [A_212,B_213] :
      ( v2_tex_2(k3_xboole_0(A_212,B_213),'#skF_1')
      | ~ r1_tarski(B_213,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7590])).

tff(c_322,plain,(
    ! [A_61,B_62,C_63] :
      ( k9_subset_1(A_61,B_62,C_63) = k3_xboole_0(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_330,plain,(
    ! [B_62] : k9_subset_1(u1_struct_0('#skF_1'),B_62,'#skF_3') = k3_xboole_0(B_62,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_322])).

tff(c_24,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_439,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_24])).

tff(c_440,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_439])).

tff(c_7804,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_7801,c_440])).

tff(c_7907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_7804])).

tff(c_7908,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_7952,plain,(
    ! [A_218,B_219] :
      ( r1_tarski(A_218,B_219)
      | ~ m1_subset_1(A_218,k1_zfmisc_1(B_219)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_7959,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_7952])).

tff(c_7975,plain,(
    ! [A_224,B_225] :
      ( k3_xboole_0(A_224,B_225) = A_224
      | ~ r1_tarski(A_224,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7986,plain,(
    k3_xboole_0('#skF_3',u1_struct_0('#skF_1')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7959,c_7975])).

tff(c_8001,plain,(
    ! [A_229,B_230] : k4_xboole_0(A_229,k4_xboole_0(A_229,B_230)) = k3_xboole_0(A_229,B_230) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8022,plain,(
    ! [A_231,B_232] : r1_tarski(k3_xboole_0(A_231,B_232),A_231) ),
    inference(superposition,[status(thm),theory(equality)],[c_8001,c_8])).

tff(c_8028,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7986,c_8022])).

tff(c_8042,plain,(
    k3_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8028,c_6])).

tff(c_8063,plain,(
    ! [A_233,B_234] : r1_tarski(k3_xboole_0(A_233,B_234),B_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8022])).

tff(c_9054,plain,(
    ! [A_278,B_279] : k3_xboole_0(k3_xboole_0(A_278,B_279),B_279) = k3_xboole_0(A_278,B_279) ),
    inference(resolution,[status(thm)],[c_8063,c_6])).

tff(c_9292,plain,(
    ! [A_283,B_284] : k3_xboole_0(k3_xboole_0(A_283,B_284),A_283) = k3_xboole_0(B_284,A_283) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9054])).

tff(c_9407,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),'#skF_3') = k3_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7986,c_9292])).

tff(c_9450,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8042,c_9407])).

tff(c_8093,plain,(
    ! [A_235,B_236] : k3_xboole_0(k4_xboole_0(A_235,B_236),A_235) = k4_xboole_0(A_235,B_236) ),
    inference(resolution,[status(thm)],[c_8,c_7975])).

tff(c_8013,plain,(
    ! [A_229,B_230] : r1_tarski(k3_xboole_0(A_229,B_230),A_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_8001,c_8])).

tff(c_8102,plain,(
    ! [A_235,B_236] : r1_tarski(k4_xboole_0(A_235,B_236),k4_xboole_0(A_235,B_236)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8093,c_8013])).

tff(c_7996,plain,(
    ! [A_226,C_227,B_228] :
      ( r1_tarski(k4_xboole_0(A_226,C_227),B_228)
      | ~ r1_tarski(A_226,B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9951,plain,(
    ! [A_290,C_291,B_292] :
      ( k3_xboole_0(k4_xboole_0(A_290,C_291),B_292) = k4_xboole_0(A_290,C_291)
      | ~ r1_tarski(A_290,B_292) ) ),
    inference(resolution,[status(thm)],[c_7996,c_6])).

tff(c_8325,plain,(
    ! [A_251,B_252,B_253] :
      ( r1_tarski(k3_xboole_0(A_251,B_252),B_253)
      | ~ r1_tarski(A_251,B_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8001,c_4])).

tff(c_8351,plain,(
    ! [A_1,B_2,B_253] :
      ( r1_tarski(k3_xboole_0(A_1,B_2),B_253)
      | ~ r1_tarski(B_2,B_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8325])).

tff(c_13002,plain,(
    ! [A_333,C_334,B_335,B_336] :
      ( r1_tarski(k4_xboole_0(A_333,C_334),B_335)
      | ~ r1_tarski(B_336,B_335)
      | ~ r1_tarski(A_333,B_336) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9951,c_8351])).

tff(c_14815,plain,(
    ! [A_379,C_380,A_381,B_382] :
      ( r1_tarski(k4_xboole_0(A_379,C_380),A_381)
      | ~ r1_tarski(A_379,k4_xboole_0(A_381,B_382)) ) ),
    inference(resolution,[status(thm)],[c_8,c_13002])).

tff(c_14861,plain,(
    ! [A_383,B_384,C_385] : r1_tarski(k4_xboole_0(k4_xboole_0(A_383,B_384),C_385),A_383) ),
    inference(resolution,[status(thm)],[c_8102,c_14815])).

tff(c_14925,plain,(
    ! [A_386,B_387,C_388] : r1_tarski(k4_xboole_0(k3_xboole_0(A_386,B_387),C_388),A_386) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_14861])).

tff(c_15138,plain,(
    ! [C_394] : r1_tarski(k4_xboole_0('#skF_3',C_394),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9450,c_14925])).

tff(c_8291,plain,(
    ! [C_248,A_249,B_250] :
      ( v2_tex_2(C_248,A_249)
      | ~ v2_tex_2(B_250,A_249)
      | ~ r1_tarski(C_248,B_250)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10354,plain,(
    ! [A_295,B_296,A_297] :
      ( v2_tex_2(k4_xboole_0(A_295,B_296),A_297)
      | ~ v2_tex_2(A_295,A_297)
      | ~ m1_subset_1(k4_xboole_0(A_295,B_296),k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ m1_subset_1(A_295,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ l1_pre_topc(A_297) ) ),
    inference(resolution,[status(thm)],[c_8,c_8291])).

tff(c_10378,plain,(
    ! [A_295,B_296,A_297] :
      ( v2_tex_2(k4_xboole_0(A_295,B_296),A_297)
      | ~ v2_tex_2(A_295,A_297)
      | ~ m1_subset_1(A_295,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ l1_pre_topc(A_297)
      | ~ r1_tarski(k4_xboole_0(A_295,B_296),u1_struct_0(A_297)) ) ),
    inference(resolution,[status(thm)],[c_20,c_10354])).

tff(c_15141,plain,(
    ! [C_394] :
      ( v2_tex_2(k4_xboole_0('#skF_3',C_394),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_15138,c_10378])).

tff(c_15176,plain,(
    ! [C_395] : v2_tex_2(k4_xboole_0('#skF_3',C_395),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_7908,c_15141])).

tff(c_15190,plain,(
    ! [B_11] : v2_tex_2(k3_xboole_0('#skF_3',B_11),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_15176])).

tff(c_8140,plain,(
    ! [A_239,B_240,C_241] :
      ( k9_subset_1(A_239,B_240,C_241) = k3_xboole_0(B_240,C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(A_239)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8148,plain,(
    ! [B_240] : k9_subset_1(u1_struct_0('#skF_1'),B_240,'#skF_3') = k3_xboole_0(B_240,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_8140])).

tff(c_8280,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8148,c_24])).

tff(c_8281,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8280])).

tff(c_15269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15190,c_8281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:45:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.75/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.75/3.18  
% 8.75/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.75/3.18  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 8.75/3.18  
% 8.75/3.18  %Foreground sorts:
% 8.75/3.18  
% 8.75/3.18  
% 8.75/3.18  %Background operators:
% 8.75/3.18  
% 8.75/3.18  
% 8.75/3.18  %Foreground operators:
% 8.75/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.75/3.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.75/3.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.75/3.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.75/3.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.75/3.18  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 8.75/3.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.75/3.18  tff('#skF_2', type, '#skF_2': $i).
% 8.75/3.18  tff('#skF_3', type, '#skF_3': $i).
% 8.75/3.18  tff('#skF_1', type, '#skF_1': $i).
% 8.75/3.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.75/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.75/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.75/3.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.75/3.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.75/3.18  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.75/3.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.75/3.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.75/3.18  
% 9.11/3.20  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.11/3.20  tff(f_80, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 9.11/3.20  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.11/3.20  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.11/3.20  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.11/3.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.11/3.20  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 9.11/3.20  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 9.11/3.20  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.11/3.20  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.11/3.20  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.11/3.20  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.11/3.20  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.11/3.20  tff(c_82, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.11/3.20  tff(c_90, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_82])).
% 9.11/3.20  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.11/3.20  tff(c_98, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(resolution, [status(thm)], [c_90, c_6])).
% 9.11/3.20  tff(c_121, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.11/3.20  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.11/3.20  tff(c_139, plain, (![A_48, B_49]: (r1_tarski(k3_xboole_0(A_48, B_49), A_48))), inference(superposition, [status(thm), theory('equality')], [c_121, c_8])).
% 9.11/3.20  tff(c_145, plain, (r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_98, c_139])).
% 9.11/3.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.11/3.20  tff(c_77, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.11/3.20  tff(c_218, plain, (![A_55, B_56]: (k3_xboole_0(k4_xboole_0(A_55, B_56), A_55)=k4_xboole_0(A_55, B_56))), inference(resolution, [status(thm)], [c_8, c_77])).
% 9.11/3.20  tff(c_233, plain, (![A_55, B_56]: (k3_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_218, c_2])).
% 9.11/3.20  tff(c_210, plain, (![A_52, C_53, B_54]: (r1_tarski(k4_xboole_0(A_52, C_53), B_54) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.11/3.20  tff(c_1895, plain, (![A_108, C_109, B_110]: (k3_xboole_0(k4_xboole_0(A_108, C_109), B_110)=k4_xboole_0(A_108, C_109) | ~r1_tarski(A_108, B_110))), inference(resolution, [status(thm)], [c_210, c_6])).
% 9.11/3.20  tff(c_2012, plain, (![A_10, B_11, B_110]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(k3_xboole_0(A_10, B_11), B_110) | ~r1_tarski(A_10, B_110))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1895])).
% 9.11/3.20  tff(c_2667, plain, (![A_124, B_125, B_126]: (k3_xboole_0(k3_xboole_0(A_124, B_125), B_126)=k3_xboole_0(A_124, B_125) | ~r1_tarski(A_124, B_126))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2012])).
% 9.11/3.20  tff(c_455, plain, (![A_72, B_73, B_74]: (r1_tarski(k3_xboole_0(A_72, B_73), B_74) | ~r1_tarski(A_72, B_74))), inference(superposition, [status(thm), theory('equality')], [c_10, c_210])).
% 9.11/3.20  tff(c_481, plain, (![A_1, B_2, B_74]: (r1_tarski(k3_xboole_0(A_1, B_2), B_74) | ~r1_tarski(B_2, B_74))), inference(superposition, [status(thm), theory('equality')], [c_2, c_455])).
% 9.11/3.20  tff(c_5699, plain, (![A_167, B_168, B_169, B_170]: (r1_tarski(k3_xboole_0(A_167, B_168), B_169) | ~r1_tarski(B_170, B_169) | ~r1_tarski(A_167, B_170))), inference(superposition, [status(thm), theory('equality')], [c_2667, c_481])).
% 9.11/3.20  tff(c_5872, plain, (![A_175, B_176]: (r1_tarski(k3_xboole_0(A_175, B_176), u1_struct_0('#skF_1')) | ~r1_tarski(A_175, '#skF_2'))), inference(resolution, [status(thm)], [c_90, c_5699])).
% 9.11/3.20  tff(c_5946, plain, (![A_55, B_56]: (r1_tarski(k4_xboole_0(A_55, B_56), u1_struct_0('#skF_1')) | ~r1_tarski(A_55, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_233, c_5872])).
% 9.11/3.20  tff(c_26, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.11/3.20  tff(c_34, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 9.11/3.20  tff(c_20, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.11/3.20  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.11/3.20  tff(c_396, plain, (![C_66, A_67, B_68]: (v2_tex_2(C_66, A_67) | ~v2_tex_2(B_68, A_67) | ~r1_tarski(C_66, B_68) | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.11/3.20  tff(c_2261, plain, (![A_116, C_117, A_118, B_119]: (v2_tex_2(k4_xboole_0(A_116, C_117), A_118) | ~v2_tex_2(B_119, A_118) | ~m1_subset_1(k4_xboole_0(A_116, C_117), k1_zfmisc_1(u1_struct_0(A_118))) | ~m1_subset_1(B_119, k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~r1_tarski(A_116, B_119))), inference(resolution, [status(thm)], [c_4, c_396])).
% 9.11/3.20  tff(c_7492, plain, (![A_198, C_199, A_200, B_201]: (v2_tex_2(k4_xboole_0(A_198, C_199), A_200) | ~v2_tex_2(B_201, A_200) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200) | ~r1_tarski(A_198, B_201) | ~r1_tarski(k4_xboole_0(A_198, C_199), u1_struct_0(A_200)))), inference(resolution, [status(thm)], [c_20, c_2261])).
% 9.11/3.20  tff(c_7499, plain, (![A_198, C_199]: (v2_tex_2(k4_xboole_0(A_198, C_199), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_198, '#skF_2') | ~r1_tarski(k4_xboole_0(A_198, C_199), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_7492])).
% 9.11/3.20  tff(c_7510, plain, (![A_202, C_203]: (v2_tex_2(k4_xboole_0(A_202, C_203), '#skF_1') | ~r1_tarski(A_202, '#skF_2') | ~r1_tarski(k4_xboole_0(A_202, C_203), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_7499])).
% 9.11/3.20  tff(c_7572, plain, (![A_204, B_205]: (v2_tex_2(k4_xboole_0(A_204, B_205), '#skF_1') | ~r1_tarski(A_204, '#skF_2'))), inference(resolution, [status(thm)], [c_5946, c_7510])).
% 9.11/3.20  tff(c_7590, plain, (![A_206, B_207]: (v2_tex_2(k3_xboole_0(A_206, B_207), '#skF_1') | ~r1_tarski(A_206, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_7572])).
% 9.11/3.20  tff(c_7801, plain, (![A_212, B_213]: (v2_tex_2(k3_xboole_0(A_212, B_213), '#skF_1') | ~r1_tarski(B_213, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_7590])).
% 9.11/3.20  tff(c_322, plain, (![A_61, B_62, C_63]: (k9_subset_1(A_61, B_62, C_63)=k3_xboole_0(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.11/3.20  tff(c_330, plain, (![B_62]: (k9_subset_1(u1_struct_0('#skF_1'), B_62, '#skF_3')=k3_xboole_0(B_62, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_322])).
% 9.11/3.20  tff(c_24, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.11/3.20  tff(c_439, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_24])).
% 9.11/3.20  tff(c_440, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_439])).
% 9.11/3.20  tff(c_7804, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_7801, c_440])).
% 9.11/3.20  tff(c_7907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_7804])).
% 9.11/3.20  tff(c_7908, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 9.11/3.20  tff(c_7952, plain, (![A_218, B_219]: (r1_tarski(A_218, B_219) | ~m1_subset_1(A_218, k1_zfmisc_1(B_219)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.11/3.20  tff(c_7959, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_7952])).
% 9.11/3.20  tff(c_7975, plain, (![A_224, B_225]: (k3_xboole_0(A_224, B_225)=A_224 | ~r1_tarski(A_224, B_225))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.11/3.20  tff(c_7986, plain, (k3_xboole_0('#skF_3', u1_struct_0('#skF_1'))='#skF_3'), inference(resolution, [status(thm)], [c_7959, c_7975])).
% 9.11/3.20  tff(c_8001, plain, (![A_229, B_230]: (k4_xboole_0(A_229, k4_xboole_0(A_229, B_230))=k3_xboole_0(A_229, B_230))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.11/3.20  tff(c_8022, plain, (![A_231, B_232]: (r1_tarski(k3_xboole_0(A_231, B_232), A_231))), inference(superposition, [status(thm), theory('equality')], [c_8001, c_8])).
% 9.11/3.20  tff(c_8028, plain, (r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7986, c_8022])).
% 9.11/3.20  tff(c_8042, plain, (k3_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_8028, c_6])).
% 9.11/3.20  tff(c_8063, plain, (![A_233, B_234]: (r1_tarski(k3_xboole_0(A_233, B_234), B_234))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8022])).
% 9.11/3.20  tff(c_9054, plain, (![A_278, B_279]: (k3_xboole_0(k3_xboole_0(A_278, B_279), B_279)=k3_xboole_0(A_278, B_279))), inference(resolution, [status(thm)], [c_8063, c_6])).
% 9.11/3.20  tff(c_9292, plain, (![A_283, B_284]: (k3_xboole_0(k3_xboole_0(A_283, B_284), A_283)=k3_xboole_0(B_284, A_283))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9054])).
% 9.11/3.20  tff(c_9407, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_3')=k3_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7986, c_9292])).
% 9.11/3.20  tff(c_9450, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8042, c_9407])).
% 9.11/3.20  tff(c_8093, plain, (![A_235, B_236]: (k3_xboole_0(k4_xboole_0(A_235, B_236), A_235)=k4_xboole_0(A_235, B_236))), inference(resolution, [status(thm)], [c_8, c_7975])).
% 9.11/3.20  tff(c_8013, plain, (![A_229, B_230]: (r1_tarski(k3_xboole_0(A_229, B_230), A_229))), inference(superposition, [status(thm), theory('equality')], [c_8001, c_8])).
% 9.11/3.20  tff(c_8102, plain, (![A_235, B_236]: (r1_tarski(k4_xboole_0(A_235, B_236), k4_xboole_0(A_235, B_236)))), inference(superposition, [status(thm), theory('equality')], [c_8093, c_8013])).
% 9.11/3.20  tff(c_7996, plain, (![A_226, C_227, B_228]: (r1_tarski(k4_xboole_0(A_226, C_227), B_228) | ~r1_tarski(A_226, B_228))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.11/3.20  tff(c_9951, plain, (![A_290, C_291, B_292]: (k3_xboole_0(k4_xboole_0(A_290, C_291), B_292)=k4_xboole_0(A_290, C_291) | ~r1_tarski(A_290, B_292))), inference(resolution, [status(thm)], [c_7996, c_6])).
% 9.11/3.20  tff(c_8325, plain, (![A_251, B_252, B_253]: (r1_tarski(k3_xboole_0(A_251, B_252), B_253) | ~r1_tarski(A_251, B_253))), inference(superposition, [status(thm), theory('equality')], [c_8001, c_4])).
% 9.11/3.20  tff(c_8351, plain, (![A_1, B_2, B_253]: (r1_tarski(k3_xboole_0(A_1, B_2), B_253) | ~r1_tarski(B_2, B_253))), inference(superposition, [status(thm), theory('equality')], [c_2, c_8325])).
% 9.11/3.20  tff(c_13002, plain, (![A_333, C_334, B_335, B_336]: (r1_tarski(k4_xboole_0(A_333, C_334), B_335) | ~r1_tarski(B_336, B_335) | ~r1_tarski(A_333, B_336))), inference(superposition, [status(thm), theory('equality')], [c_9951, c_8351])).
% 9.11/3.20  tff(c_14815, plain, (![A_379, C_380, A_381, B_382]: (r1_tarski(k4_xboole_0(A_379, C_380), A_381) | ~r1_tarski(A_379, k4_xboole_0(A_381, B_382)))), inference(resolution, [status(thm)], [c_8, c_13002])).
% 9.11/3.20  tff(c_14861, plain, (![A_383, B_384, C_385]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_383, B_384), C_385), A_383))), inference(resolution, [status(thm)], [c_8102, c_14815])).
% 9.11/3.20  tff(c_14925, plain, (![A_386, B_387, C_388]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_386, B_387), C_388), A_386))), inference(superposition, [status(thm), theory('equality')], [c_10, c_14861])).
% 9.11/3.20  tff(c_15138, plain, (![C_394]: (r1_tarski(k4_xboole_0('#skF_3', C_394), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9450, c_14925])).
% 9.11/3.20  tff(c_8291, plain, (![C_248, A_249, B_250]: (v2_tex_2(C_248, A_249) | ~v2_tex_2(B_250, A_249) | ~r1_tarski(C_248, B_250) | ~m1_subset_1(C_248, k1_zfmisc_1(u1_struct_0(A_249))) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.11/3.20  tff(c_10354, plain, (![A_295, B_296, A_297]: (v2_tex_2(k4_xboole_0(A_295, B_296), A_297) | ~v2_tex_2(A_295, A_297) | ~m1_subset_1(k4_xboole_0(A_295, B_296), k1_zfmisc_1(u1_struct_0(A_297))) | ~m1_subset_1(A_295, k1_zfmisc_1(u1_struct_0(A_297))) | ~l1_pre_topc(A_297))), inference(resolution, [status(thm)], [c_8, c_8291])).
% 9.11/3.20  tff(c_10378, plain, (![A_295, B_296, A_297]: (v2_tex_2(k4_xboole_0(A_295, B_296), A_297) | ~v2_tex_2(A_295, A_297) | ~m1_subset_1(A_295, k1_zfmisc_1(u1_struct_0(A_297))) | ~l1_pre_topc(A_297) | ~r1_tarski(k4_xboole_0(A_295, B_296), u1_struct_0(A_297)))), inference(resolution, [status(thm)], [c_20, c_10354])).
% 9.11/3.20  tff(c_15141, plain, (![C_394]: (v2_tex_2(k4_xboole_0('#skF_3', C_394), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_15138, c_10378])).
% 9.11/3.20  tff(c_15176, plain, (![C_395]: (v2_tex_2(k4_xboole_0('#skF_3', C_395), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_7908, c_15141])).
% 9.11/3.20  tff(c_15190, plain, (![B_11]: (v2_tex_2(k3_xboole_0('#skF_3', B_11), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_15176])).
% 9.11/3.20  tff(c_8140, plain, (![A_239, B_240, C_241]: (k9_subset_1(A_239, B_240, C_241)=k3_xboole_0(B_240, C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(A_239)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.11/3.20  tff(c_8148, plain, (![B_240]: (k9_subset_1(u1_struct_0('#skF_1'), B_240, '#skF_3')=k3_xboole_0(B_240, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_8140])).
% 9.11/3.20  tff(c_8280, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8148, c_24])).
% 9.11/3.20  tff(c_8281, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8280])).
% 9.11/3.20  tff(c_15269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15190, c_8281])).
% 9.11/3.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.11/3.20  
% 9.11/3.20  Inference rules
% 9.11/3.20  ----------------------
% 9.11/3.20  #Ref     : 0
% 9.11/3.20  #Sup     : 3979
% 9.11/3.20  #Fact    : 0
% 9.11/3.20  #Define  : 0
% 9.11/3.20  #Split   : 2
% 9.11/3.20  #Chain   : 0
% 9.11/3.20  #Close   : 0
% 9.11/3.20  
% 9.11/3.20  Ordering : KBO
% 9.11/3.20  
% 9.11/3.20  Simplification rules
% 9.11/3.20  ----------------------
% 9.11/3.20  #Subsume      : 724
% 9.11/3.20  #Demod        : 4152
% 9.11/3.20  #Tautology    : 2071
% 9.11/3.20  #SimpNegUnit  : 3
% 9.11/3.20  #BackRed      : 3
% 9.11/3.20  
% 9.11/3.20  #Partial instantiations: 0
% 9.11/3.20  #Strategies tried      : 1
% 9.11/3.20  
% 9.11/3.20  Timing (in seconds)
% 9.11/3.20  ----------------------
% 9.11/3.20  Preprocessing        : 0.30
% 9.11/3.20  Parsing              : 0.16
% 9.11/3.20  CNF conversion       : 0.02
% 9.11/3.20  Main loop            : 2.12
% 9.11/3.20  Inferencing          : 0.51
% 9.11/3.21  Reduction            : 1.09
% 9.11/3.21  Demodulation         : 0.94
% 9.11/3.21  BG Simplification    : 0.07
% 9.11/3.21  Subsumption          : 0.34
% 9.16/3.21  Abstraction          : 0.10
% 9.16/3.21  MUC search           : 0.00
% 9.16/3.21  Cooper               : 0.00
% 9.16/3.21  Total                : 2.45
% 9.16/3.21  Index Insertion      : 0.00
% 9.16/3.21  Index Deletion       : 0.00
% 9.16/3.21  Index Matching       : 0.00
% 9.16/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
