%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:10 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 119 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  103 ( 221 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(f_78,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_84,plain,(
    ! [B_39,A_40] : k1_setfam_1(k2_tarski(B_39,A_40)) = k3_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_16,plain,(
    ! [A_18,B_19] : k1_setfam_1(k2_tarski(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,(
    ! [B_39,A_40] : k3_xboole_0(B_39,A_40) = k3_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_16])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_294,plain,(
    ! [A_57,B_58,C_59] :
      ( k7_subset_1(A_57,B_58,C_59) = k4_xboole_0(B_58,C_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_300,plain,(
    ! [C_59] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_59) = k4_xboole_0('#skF_2',C_59) ),
    inference(resolution,[status(thm)],[c_26,c_294])).

tff(c_471,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_subset_1(k7_subset_1(A_67,B_68,C_69),k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_478,plain,(
    ! [C_59] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_59),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_471])).

tff(c_488,plain,(
    ! [C_70] : m1_subset_1(k4_xboole_0('#skF_2',C_70),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_478])).

tff(c_496,plain,(
    ! [B_6] : m1_subset_1(k3_xboole_0('#skF_2',B_6),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_488])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_607,plain,(
    ! [C_76,A_77,B_78] :
      ( v2_tex_2(C_76,A_77)
      | ~ v2_tex_2(B_78,A_77)
      | ~ r1_tarski(C_76,B_78)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1972,plain,(
    ! [A_129,B_130,A_131] :
      ( v2_tex_2(k3_xboole_0(A_129,B_130),A_131)
      | ~ v2_tex_2(A_129,A_131)
      | ~ m1_subset_1(k3_xboole_0(A_129,B_130),k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_subset_1(A_129,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(resolution,[status(thm)],[c_2,c_607])).

tff(c_2011,plain,(
    ! [B_6] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_6),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_496,c_1972])).

tff(c_2059,plain,(
    ! [B_132] : v2_tex_2(k3_xboole_0('#skF_2',B_132),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_30,c_2011])).

tff(c_2079,plain,(
    ! [B_39] : v2_tex_2(k3_xboole_0(B_39,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_2059])).

tff(c_245,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,C_53) = k3_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_250,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_1'),B_52,'#skF_3') = k3_xboole_0(B_52,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_245])).

tff(c_20,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_283,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_20])).

tff(c_284,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_283])).

tff(c_2088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2079,c_284])).

tff(c_2089,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_2508,plain,(
    ! [A_165,B_166,C_167] :
      ( k7_subset_1(A_165,B_166,C_167) = k4_xboole_0(B_166,C_167)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2518,plain,(
    ! [C_168] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_168) = k4_xboole_0('#skF_3',C_168) ),
    inference(resolution,[status(thm)],[c_24,c_2508])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k7_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2524,plain,(
    ! [C_168] :
      ( m1_subset_1(k4_xboole_0('#skF_3',C_168),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2518,c_10])).

tff(c_2532,plain,(
    ! [C_169] : m1_subset_1(k4_xboole_0('#skF_3',C_169),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2524])).

tff(c_2540,plain,(
    ! [B_6] : m1_subset_1(k3_xboole_0('#skF_3',B_6),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2532])).

tff(c_2663,plain,(
    ! [C_176,A_177,B_178] :
      ( v2_tex_2(C_176,A_177)
      | ~ v2_tex_2(B_178,A_177)
      | ~ r1_tarski(C_176,B_178)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3793,plain,(
    ! [A_221,B_222,A_223] :
      ( v2_tex_2(k3_xboole_0(A_221,B_222),A_223)
      | ~ v2_tex_2(A_221,A_223)
      | ~ m1_subset_1(k3_xboole_0(A_221,B_222),k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ m1_subset_1(A_221,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223) ) ),
    inference(resolution,[status(thm)],[c_2,c_2663])).

tff(c_3826,plain,(
    ! [B_6] :
      ( v2_tex_2(k3_xboole_0('#skF_3',B_6),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2540,c_3793])).

tff(c_3864,plain,(
    ! [B_6] : v2_tex_2(k3_xboole_0('#skF_3',B_6),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_2089,c_3826])).

tff(c_2129,plain,(
    ! [A_137,B_138] : k1_setfam_1(k2_tarski(A_137,B_138)) = k3_xboole_0(A_137,B_138) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2144,plain,(
    ! [B_139,A_140] : k1_setfam_1(k2_tarski(B_139,A_140)) = k3_xboole_0(A_140,B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2129])).

tff(c_2150,plain,(
    ! [B_139,A_140] : k3_xboole_0(B_139,A_140) = k3_xboole_0(A_140,B_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_2144,c_16])).

tff(c_2334,plain,(
    ! [A_156,B_157,C_158] :
      ( k9_subset_1(A_156,B_157,C_158) = k3_xboole_0(B_157,C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(A_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2342,plain,(
    ! [B_157] : k9_subset_1(u1_struct_0('#skF_1'),B_157,'#skF_3') = k3_xboole_0(B_157,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2334])).

tff(c_2356,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2342,c_20])).

tff(c_2357,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2356])).

tff(c_3870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3864,c_2357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.84  
% 4.53/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.85  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.53/1.85  
% 4.53/1.85  %Foreground sorts:
% 4.53/1.85  
% 4.53/1.85  
% 4.53/1.85  %Background operators:
% 4.53/1.85  
% 4.53/1.85  
% 4.53/1.85  %Foreground operators:
% 4.53/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.53/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.53/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.53/1.85  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.53/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.53/1.85  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.53/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.53/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.53/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.53/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.53/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.53/1.85  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.53/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.53/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.53/1.85  
% 4.53/1.86  tff(f_78, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 4.53/1.86  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.53/1.86  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.53/1.86  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.53/1.86  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.53/1.86  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.53/1.86  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.53/1.86  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 4.53/1.86  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.53/1.86  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.53/1.86  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.53/1.86  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.53/1.86  tff(c_69, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.53/1.86  tff(c_84, plain, (![B_39, A_40]: (k1_setfam_1(k2_tarski(B_39, A_40))=k3_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_8, c_69])).
% 4.53/1.86  tff(c_16, plain, (![A_18, B_19]: (k1_setfam_1(k2_tarski(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.53/1.86  tff(c_90, plain, (![B_39, A_40]: (k3_xboole_0(B_39, A_40)=k3_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_84, c_16])).
% 4.53/1.86  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.53/1.86  tff(c_22, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.53/1.86  tff(c_30, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 4.53/1.86  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.53/1.86  tff(c_294, plain, (![A_57, B_58, C_59]: (k7_subset_1(A_57, B_58, C_59)=k4_xboole_0(B_58, C_59) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.53/1.86  tff(c_300, plain, (![C_59]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_59)=k4_xboole_0('#skF_2', C_59))), inference(resolution, [status(thm)], [c_26, c_294])).
% 4.53/1.86  tff(c_471, plain, (![A_67, B_68, C_69]: (m1_subset_1(k7_subset_1(A_67, B_68, C_69), k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.53/1.86  tff(c_478, plain, (![C_59]: (m1_subset_1(k4_xboole_0('#skF_2', C_59), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_300, c_471])).
% 4.53/1.86  tff(c_488, plain, (![C_70]: (m1_subset_1(k4_xboole_0('#skF_2', C_70), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_478])).
% 4.53/1.86  tff(c_496, plain, (![B_6]: (m1_subset_1(k3_xboole_0('#skF_2', B_6), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_488])).
% 4.53/1.86  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.53/1.86  tff(c_607, plain, (![C_76, A_77, B_78]: (v2_tex_2(C_76, A_77) | ~v2_tex_2(B_78, A_77) | ~r1_tarski(C_76, B_78) | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.53/1.86  tff(c_1972, plain, (![A_129, B_130, A_131]: (v2_tex_2(k3_xboole_0(A_129, B_130), A_131) | ~v2_tex_2(A_129, A_131) | ~m1_subset_1(k3_xboole_0(A_129, B_130), k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_subset_1(A_129, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(resolution, [status(thm)], [c_2, c_607])).
% 4.53/1.86  tff(c_2011, plain, (![B_6]: (v2_tex_2(k3_xboole_0('#skF_2', B_6), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_496, c_1972])).
% 4.53/1.86  tff(c_2059, plain, (![B_132]: (v2_tex_2(k3_xboole_0('#skF_2', B_132), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_30, c_2011])).
% 4.53/1.86  tff(c_2079, plain, (![B_39]: (v2_tex_2(k3_xboole_0(B_39, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_2059])).
% 4.53/1.86  tff(c_245, plain, (![A_51, B_52, C_53]: (k9_subset_1(A_51, B_52, C_53)=k3_xboole_0(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.53/1.86  tff(c_250, plain, (![B_52]: (k9_subset_1(u1_struct_0('#skF_1'), B_52, '#skF_3')=k3_xboole_0(B_52, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_245])).
% 4.53/1.86  tff(c_20, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.53/1.86  tff(c_283, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_20])).
% 4.53/1.86  tff(c_284, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_283])).
% 4.53/1.86  tff(c_2088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2079, c_284])).
% 4.53/1.86  tff(c_2089, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 4.53/1.86  tff(c_2508, plain, (![A_165, B_166, C_167]: (k7_subset_1(A_165, B_166, C_167)=k4_xboole_0(B_166, C_167) | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.53/1.86  tff(c_2518, plain, (![C_168]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_168)=k4_xboole_0('#skF_3', C_168))), inference(resolution, [status(thm)], [c_24, c_2508])).
% 4.53/1.86  tff(c_10, plain, (![A_9, B_10, C_11]: (m1_subset_1(k7_subset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.53/1.86  tff(c_2524, plain, (![C_168]: (m1_subset_1(k4_xboole_0('#skF_3', C_168), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2518, c_10])).
% 4.53/1.86  tff(c_2532, plain, (![C_169]: (m1_subset_1(k4_xboole_0('#skF_3', C_169), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2524])).
% 4.53/1.86  tff(c_2540, plain, (![B_6]: (m1_subset_1(k3_xboole_0('#skF_3', B_6), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2532])).
% 4.53/1.86  tff(c_2663, plain, (![C_176, A_177, B_178]: (v2_tex_2(C_176, A_177) | ~v2_tex_2(B_178, A_177) | ~r1_tarski(C_176, B_178) | ~m1_subset_1(C_176, k1_zfmisc_1(u1_struct_0(A_177))) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.53/1.86  tff(c_3793, plain, (![A_221, B_222, A_223]: (v2_tex_2(k3_xboole_0(A_221, B_222), A_223) | ~v2_tex_2(A_221, A_223) | ~m1_subset_1(k3_xboole_0(A_221, B_222), k1_zfmisc_1(u1_struct_0(A_223))) | ~m1_subset_1(A_221, k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223))), inference(resolution, [status(thm)], [c_2, c_2663])).
% 4.53/1.86  tff(c_3826, plain, (![B_6]: (v2_tex_2(k3_xboole_0('#skF_3', B_6), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_2540, c_3793])).
% 4.53/1.86  tff(c_3864, plain, (![B_6]: (v2_tex_2(k3_xboole_0('#skF_3', B_6), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_2089, c_3826])).
% 4.53/1.86  tff(c_2129, plain, (![A_137, B_138]: (k1_setfam_1(k2_tarski(A_137, B_138))=k3_xboole_0(A_137, B_138))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.53/1.86  tff(c_2144, plain, (![B_139, A_140]: (k1_setfam_1(k2_tarski(B_139, A_140))=k3_xboole_0(A_140, B_139))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2129])).
% 4.53/1.86  tff(c_2150, plain, (![B_139, A_140]: (k3_xboole_0(B_139, A_140)=k3_xboole_0(A_140, B_139))), inference(superposition, [status(thm), theory('equality')], [c_2144, c_16])).
% 4.53/1.86  tff(c_2334, plain, (![A_156, B_157, C_158]: (k9_subset_1(A_156, B_157, C_158)=k3_xboole_0(B_157, C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(A_156)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.53/1.86  tff(c_2342, plain, (![B_157]: (k9_subset_1(u1_struct_0('#skF_1'), B_157, '#skF_3')=k3_xboole_0(B_157, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_2334])).
% 4.53/1.86  tff(c_2356, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2342, c_20])).
% 4.53/1.86  tff(c_2357, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2356])).
% 4.53/1.86  tff(c_3870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3864, c_2357])).
% 4.53/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.53/1.86  
% 4.53/1.86  Inference rules
% 4.53/1.86  ----------------------
% 4.53/1.86  #Ref     : 0
% 4.53/1.86  #Sup     : 934
% 4.53/1.86  #Fact    : 0
% 4.53/1.86  #Define  : 0
% 4.53/1.86  #Split   : 1
% 4.53/1.86  #Chain   : 0
% 4.53/1.86  #Close   : 0
% 4.53/1.86  
% 4.53/1.86  Ordering : KBO
% 4.53/1.86  
% 4.53/1.86  Simplification rules
% 4.53/1.86  ----------------------
% 4.53/1.86  #Subsume      : 55
% 4.53/1.86  #Demod        : 726
% 4.53/1.86  #Tautology    : 475
% 4.53/1.86  #SimpNegUnit  : 0
% 4.53/1.86  #BackRed      : 4
% 4.53/1.86  
% 4.53/1.86  #Partial instantiations: 0
% 4.53/1.86  #Strategies tried      : 1
% 4.53/1.86  
% 4.53/1.86  Timing (in seconds)
% 4.53/1.86  ----------------------
% 4.53/1.86  Preprocessing        : 0.29
% 4.53/1.86  Parsing              : 0.15
% 4.53/1.86  CNF conversion       : 0.02
% 4.53/1.86  Main loop            : 0.76
% 4.53/1.86  Inferencing          : 0.22
% 4.53/1.86  Reduction            : 0.34
% 4.53/1.86  Demodulation         : 0.28
% 4.53/1.87  BG Simplification    : 0.03
% 4.53/1.87  Subsumption          : 0.11
% 4.53/1.87  Abstraction          : 0.04
% 4.53/1.87  MUC search           : 0.00
% 4.53/1.87  Cooper               : 0.00
% 4.53/1.87  Total                : 1.08
% 4.53/1.87  Index Insertion      : 0.00
% 4.53/1.87  Index Deletion       : 0.00
% 4.53/1.87  Index Matching       : 0.00
% 4.53/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
