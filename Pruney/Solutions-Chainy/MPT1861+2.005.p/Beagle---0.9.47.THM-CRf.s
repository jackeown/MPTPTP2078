%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:10 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 120 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 221 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_88,plain,(
    ! [B_39,A_40] : k1_setfam_1(k2_tarski(B_39,A_40)) = k3_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_64])).

tff(c_16,plain,(
    ! [A_18,B_19] : k1_setfam_1(k2_tarski(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    ! [B_39,A_40] : k3_xboole_0(B_39,A_40) = k3_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_16])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_248,plain,(
    ! [A_58,B_59,C_60] :
      ( k7_subset_1(A_58,B_59,C_60) = k4_xboole_0(B_59,C_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_267,plain,(
    ! [C_62] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_62) = k4_xboole_0('#skF_2',C_62) ),
    inference(resolution,[status(thm)],[c_26,c_248])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k7_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_273,plain,(
    ! [C_62] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_62),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_10])).

tff(c_281,plain,(
    ! [C_63] : m1_subset_1(k4_xboole_0('#skF_2',C_63),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_273])).

tff(c_297,plain,(
    ! [B_4] : m1_subset_1(k3_xboole_0('#skF_2',B_4),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_281])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_381,plain,(
    ! [C_69,A_70,B_71] :
      ( v2_tex_2(C_69,A_70)
      | ~ v2_tex_2(B_71,A_70)
      | ~ r1_tarski(C_69,B_71)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1122,plain,(
    ! [A_117,B_118,A_119] :
      ( v2_tex_2(k3_xboole_0(A_117,B_118),A_119)
      | ~ v2_tex_2(A_117,A_119)
      | ~ m1_subset_1(k3_xboole_0(A_117,B_118),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(A_117,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_2,c_381])).

tff(c_1155,plain,(
    ! [B_4] :
      ( v2_tex_2(k3_xboole_0('#skF_2',B_4),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_297,c_1122])).

tff(c_1195,plain,(
    ! [B_120] : v2_tex_2(k3_xboole_0('#skF_2',B_120),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_30,c_1155])).

tff(c_1199,plain,(
    ! [B_39] : v2_tex_2(k3_xboole_0(B_39,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1195])).

tff(c_227,plain,(
    ! [A_54,B_55,C_56] :
      ( k9_subset_1(A_54,B_55,C_56) = k3_xboole_0(B_55,C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_235,plain,(
    ! [B_55] : k9_subset_1(u1_struct_0('#skF_1'),B_55,'#skF_3') = k3_xboole_0(B_55,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_227])).

tff(c_20,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_237,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_20])).

tff(c_238,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_237])).

tff(c_1206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_238])).

tff(c_1207,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_1405,plain,(
    ! [A_142,B_143,C_144] :
      ( k7_subset_1(A_142,B_143,C_144) = k4_xboole_0(B_143,C_144)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1415,plain,(
    ! [C_145] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_145) = k4_xboole_0('#skF_3',C_145) ),
    inference(resolution,[status(thm)],[c_24,c_1405])).

tff(c_1421,plain,(
    ! [C_145] :
      ( m1_subset_1(k4_xboole_0('#skF_3',C_145),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1415,c_10])).

tff(c_1429,plain,(
    ! [C_146] : m1_subset_1(k4_xboole_0('#skF_3',C_146),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1421])).

tff(c_1443,plain,(
    ! [B_4] : m1_subset_1(k3_xboole_0('#skF_3',B_4),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1429])).

tff(c_1581,plain,(
    ! [C_158,A_159,B_160] :
      ( v2_tex_2(C_158,A_159)
      | ~ v2_tex_2(B_160,A_159)
      | ~ r1_tarski(C_158,B_160)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2345,plain,(
    ! [A_207,B_208,A_209] :
      ( v2_tex_2(k3_xboole_0(A_207,B_208),A_209)
      | ~ v2_tex_2(A_207,A_209)
      | ~ m1_subset_1(k3_xboole_0(A_207,B_208),k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ m1_subset_1(A_207,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(resolution,[status(thm)],[c_2,c_1581])).

tff(c_2381,plain,(
    ! [B_4] :
      ( v2_tex_2(k3_xboole_0('#skF_3',B_4),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1443,c_2345])).

tff(c_2423,plain,(
    ! [B_4] : v2_tex_2(k3_xboole_0('#skF_3',B_4),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_1207,c_2381])).

tff(c_1242,plain,(
    ! [A_123,B_124] : k1_setfam_1(k2_tarski(A_123,B_124)) = k3_xboole_0(A_123,B_124) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1257,plain,(
    ! [B_125,A_126] : k1_setfam_1(k2_tarski(B_125,A_126)) = k3_xboole_0(A_126,B_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1242])).

tff(c_1263,plain,(
    ! [B_125,A_126] : k3_xboole_0(B_125,A_126) = k3_xboole_0(A_126,B_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_16])).

tff(c_1527,plain,(
    ! [A_153,B_154,C_155] :
      ( k9_subset_1(A_153,B_154,C_155) = k3_xboole_0(B_154,C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(A_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1553,plain,(
    ! [B_154] : k9_subset_1(u1_struct_0('#skF_1'),B_154,'#skF_3') = k3_xboole_0(B_154,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1527])).

tff(c_1557,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1553,c_20])).

tff(c_1558,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1263,c_1557])).

tff(c_2426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2423,c_1558])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.66  
% 3.97/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.67  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.97/1.67  
% 3.97/1.67  %Foreground sorts:
% 3.97/1.67  
% 3.97/1.67  
% 3.97/1.67  %Background operators:
% 3.97/1.67  
% 3.97/1.67  
% 3.97/1.67  %Foreground operators:
% 3.97/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.97/1.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.97/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.97/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.97/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.97/1.67  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.97/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.97/1.67  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.97/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.97/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.97/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.97/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.97/1.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.97/1.67  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.97/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.97/1.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.97/1.67  
% 4.16/1.68  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 4.16/1.68  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.16/1.68  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.16/1.68  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.16/1.68  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.16/1.68  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.16/1.68  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.16/1.68  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 4.16/1.68  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.16/1.68  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.16/1.68  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.16/1.68  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.68  tff(c_64, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.16/1.68  tff(c_88, plain, (![B_39, A_40]: (k1_setfam_1(k2_tarski(B_39, A_40))=k3_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_6, c_64])).
% 4.16/1.68  tff(c_16, plain, (![A_18, B_19]: (k1_setfam_1(k2_tarski(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.16/1.68  tff(c_94, plain, (![B_39, A_40]: (k3_xboole_0(B_39, A_40)=k3_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_88, c_16])).
% 4.16/1.68  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.16/1.68  tff(c_22, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.16/1.68  tff(c_30, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 4.16/1.68  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.16/1.68  tff(c_248, plain, (![A_58, B_59, C_60]: (k7_subset_1(A_58, B_59, C_60)=k4_xboole_0(B_59, C_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.16/1.68  tff(c_267, plain, (![C_62]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_62)=k4_xboole_0('#skF_2', C_62))), inference(resolution, [status(thm)], [c_26, c_248])).
% 4.16/1.68  tff(c_10, plain, (![A_9, B_10, C_11]: (m1_subset_1(k7_subset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.16/1.68  tff(c_273, plain, (![C_62]: (m1_subset_1(k4_xboole_0('#skF_2', C_62), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_267, c_10])).
% 4.16/1.68  tff(c_281, plain, (![C_63]: (m1_subset_1(k4_xboole_0('#skF_2', C_63), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_273])).
% 4.16/1.68  tff(c_297, plain, (![B_4]: (m1_subset_1(k3_xboole_0('#skF_2', B_4), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_281])).
% 4.16/1.68  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.16/1.68  tff(c_381, plain, (![C_69, A_70, B_71]: (v2_tex_2(C_69, A_70) | ~v2_tex_2(B_71, A_70) | ~r1_tarski(C_69, B_71) | ~m1_subset_1(C_69, k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.16/1.68  tff(c_1122, plain, (![A_117, B_118, A_119]: (v2_tex_2(k3_xboole_0(A_117, B_118), A_119) | ~v2_tex_2(A_117, A_119) | ~m1_subset_1(k3_xboole_0(A_117, B_118), k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(A_117, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_2, c_381])).
% 4.16/1.68  tff(c_1155, plain, (![B_4]: (v2_tex_2(k3_xboole_0('#skF_2', B_4), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_297, c_1122])).
% 4.16/1.68  tff(c_1195, plain, (![B_120]: (v2_tex_2(k3_xboole_0('#skF_2', B_120), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_30, c_1155])).
% 4.16/1.68  tff(c_1199, plain, (![B_39]: (v2_tex_2(k3_xboole_0(B_39, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_1195])).
% 4.16/1.68  tff(c_227, plain, (![A_54, B_55, C_56]: (k9_subset_1(A_54, B_55, C_56)=k3_xboole_0(B_55, C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.16/1.68  tff(c_235, plain, (![B_55]: (k9_subset_1(u1_struct_0('#skF_1'), B_55, '#skF_3')=k3_xboole_0(B_55, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_227])).
% 4.16/1.68  tff(c_20, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.16/1.68  tff(c_237, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_20])).
% 4.16/1.68  tff(c_238, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_237])).
% 4.16/1.68  tff(c_1206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1199, c_238])).
% 4.16/1.68  tff(c_1207, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 4.16/1.68  tff(c_1405, plain, (![A_142, B_143, C_144]: (k7_subset_1(A_142, B_143, C_144)=k4_xboole_0(B_143, C_144) | ~m1_subset_1(B_143, k1_zfmisc_1(A_142)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.16/1.68  tff(c_1415, plain, (![C_145]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_145)=k4_xboole_0('#skF_3', C_145))), inference(resolution, [status(thm)], [c_24, c_1405])).
% 4.16/1.68  tff(c_1421, plain, (![C_145]: (m1_subset_1(k4_xboole_0('#skF_3', C_145), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_1415, c_10])).
% 4.16/1.68  tff(c_1429, plain, (![C_146]: (m1_subset_1(k4_xboole_0('#skF_3', C_146), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1421])).
% 4.16/1.68  tff(c_1443, plain, (![B_4]: (m1_subset_1(k3_xboole_0('#skF_3', B_4), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1429])).
% 4.16/1.68  tff(c_1581, plain, (![C_158, A_159, B_160]: (v2_tex_2(C_158, A_159) | ~v2_tex_2(B_160, A_159) | ~r1_tarski(C_158, B_160) | ~m1_subset_1(C_158, k1_zfmisc_1(u1_struct_0(A_159))) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.16/1.68  tff(c_2345, plain, (![A_207, B_208, A_209]: (v2_tex_2(k3_xboole_0(A_207, B_208), A_209) | ~v2_tex_2(A_207, A_209) | ~m1_subset_1(k3_xboole_0(A_207, B_208), k1_zfmisc_1(u1_struct_0(A_209))) | ~m1_subset_1(A_207, k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_pre_topc(A_209))), inference(resolution, [status(thm)], [c_2, c_1581])).
% 4.16/1.68  tff(c_2381, plain, (![B_4]: (v2_tex_2(k3_xboole_0('#skF_3', B_4), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_1443, c_2345])).
% 4.16/1.68  tff(c_2423, plain, (![B_4]: (v2_tex_2(k3_xboole_0('#skF_3', B_4), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_1207, c_2381])).
% 4.16/1.68  tff(c_1242, plain, (![A_123, B_124]: (k1_setfam_1(k2_tarski(A_123, B_124))=k3_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.16/1.68  tff(c_1257, plain, (![B_125, A_126]: (k1_setfam_1(k2_tarski(B_125, A_126))=k3_xboole_0(A_126, B_125))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1242])).
% 4.16/1.68  tff(c_1263, plain, (![B_125, A_126]: (k3_xboole_0(B_125, A_126)=k3_xboole_0(A_126, B_125))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_16])).
% 4.16/1.68  tff(c_1527, plain, (![A_153, B_154, C_155]: (k9_subset_1(A_153, B_154, C_155)=k3_xboole_0(B_154, C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(A_153)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.16/1.68  tff(c_1553, plain, (![B_154]: (k9_subset_1(u1_struct_0('#skF_1'), B_154, '#skF_3')=k3_xboole_0(B_154, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_1527])).
% 4.16/1.68  tff(c_1557, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1553, c_20])).
% 4.16/1.68  tff(c_1558, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1263, c_1557])).
% 4.16/1.68  tff(c_2426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2423, c_1558])).
% 4.16/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.68  
% 4.16/1.68  Inference rules
% 4.16/1.68  ----------------------
% 4.16/1.68  #Ref     : 0
% 4.16/1.68  #Sup     : 587
% 4.16/1.68  #Fact    : 0
% 4.16/1.68  #Define  : 0
% 4.16/1.68  #Split   : 1
% 4.16/1.68  #Chain   : 0
% 4.16/1.68  #Close   : 0
% 4.16/1.68  
% 4.16/1.68  Ordering : KBO
% 4.16/1.68  
% 4.16/1.68  Simplification rules
% 4.16/1.68  ----------------------
% 4.16/1.68  #Subsume      : 3
% 4.16/1.68  #Demod        : 204
% 4.16/1.68  #Tautology    : 181
% 4.16/1.68  #SimpNegUnit  : 0
% 4.16/1.68  #BackRed      : 4
% 4.16/1.68  
% 4.16/1.68  #Partial instantiations: 0
% 4.16/1.68  #Strategies tried      : 1
% 4.16/1.68  
% 4.16/1.68  Timing (in seconds)
% 4.16/1.68  ----------------------
% 4.16/1.69  Preprocessing        : 0.31
% 4.16/1.69  Parsing              : 0.17
% 4.16/1.69  CNF conversion       : 0.02
% 4.16/1.69  Main loop            : 0.61
% 4.16/1.69  Inferencing          : 0.19
% 4.16/1.69  Reduction            : 0.25
% 4.16/1.69  Demodulation         : 0.20
% 4.16/1.69  BG Simplification    : 0.03
% 4.16/1.69  Subsumption          : 0.08
% 4.16/1.69  Abstraction          : 0.04
% 4.16/1.69  MUC search           : 0.00
% 4.16/1.69  Cooper               : 0.00
% 4.16/1.69  Total                : 0.95
% 4.16/1.69  Index Insertion      : 0.00
% 4.16/1.69  Index Deletion       : 0.00
% 4.16/1.69  Index Matching       : 0.00
% 4.16/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
