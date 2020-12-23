%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:05 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   76 (  90 expanded)
%              Number of leaves         :   39 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 112 expanded)
%              Number of equality atoms :   36 (  41 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( H = k5_enumset1(A,B,C,D,E,F,G)
    <=> ! [I] :
          ( r2_hidden(I,H)
        <=> ~ ( I != A
              & I != B
              & I != C
              & I != D
              & I != E
              & I != F
              & I != G ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_82,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_179,plain,(
    ! [A_132,B_133] :
      ( u1_struct_0(k1_pre_topc(A_132,B_133)) = B_133
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_186,plain,
    ( u1_struct_0(k1_pre_topc('#skF_3','#skF_5')) = '#skF_5'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_179])).

tff(c_193,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_186])).

tff(c_149,plain,(
    ! [A_127,B_128,C_129] :
      ( k9_subset_1(A_127,B_128,C_129) = k3_xboole_0(B_128,C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_157,plain,(
    ! [B_128] : k9_subset_1(u1_struct_0('#skF_3'),B_128,'#skF_5') = k3_xboole_0(B_128,'#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_149])).

tff(c_70,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_76,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_113,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),u1_struct_0(k1_pre_topc('#skF_3','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_70,c_76])).

tff(c_159,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),u1_struct_0(k1_pre_topc('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_113])).

tff(c_211,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_159])).

tff(c_253,plain,(
    ! [A_139,C_140,B_141] :
      ( k9_subset_1(A_139,C_140,B_141) = k9_subset_1(A_139,B_141,C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(A_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_257,plain,(
    ! [B_141] : k9_subset_1(u1_struct_0('#skF_3'),B_141,'#skF_5') = k9_subset_1(u1_struct_0('#skF_3'),'#skF_5',B_141) ),
    inference(resolution,[status(thm)],[c_78,c_253])).

tff(c_265,plain,(
    ! [B_142] : k9_subset_1(u1_struct_0('#skF_3'),'#skF_5',B_142) = k3_xboole_0(B_142,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_257])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_158,plain,(
    ! [B_128] : k9_subset_1(u1_struct_0('#skF_3'),B_128,'#skF_4') = k3_xboole_0(B_128,'#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_149])).

tff(c_272,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_158])).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_enumset1(A_3,A_3,B_4,C_5) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k3_enumset1(A_6,A_6,B_7,C_8,D_9) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k4_enumset1(A_10,A_10,B_11,C_12,D_13,E_14) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_608,plain,(
    ! [C_171,G_173,D_172,B_174,A_177,E_176,F_175] : k6_enumset1(A_177,A_177,B_174,C_171,D_172,E_176,F_175,G_173) = k5_enumset1(A_177,B_174,C_171,D_172,E_176,F_175,G_173) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k6_enumset1(A_22,A_22,A_22,B_23,C_24,D_25,E_26,F_27) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_624,plain,(
    ! [G_182,C_180,D_178,F_183,E_179,B_181] : k5_enumset1(B_181,B_181,C_180,D_178,E_179,F_183,G_182) = k4_enumset1(B_181,C_180,D_178,E_179,F_183,G_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_12])).

tff(c_30,plain,(
    ! [C_33,B_32,F_36,E_35,G_37,D_34,I_41] : r2_hidden(I_41,k5_enumset1(I_41,B_32,C_33,D_34,E_35,F_36,G_37)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_654,plain,(
    ! [G_188,C_189,D_185,B_184,E_187,F_186] : r2_hidden(B_184,k4_enumset1(B_184,C_189,D_185,E_187,F_186,G_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_30])).

tff(c_668,plain,(
    ! [E_191,D_193,C_194,B_190,A_192] : r2_hidden(A_192,k3_enumset1(A_192,B_190,C_194,D_193,E_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_654])).

tff(c_696,plain,(
    ! [A_199,B_200,C_201,D_202] : r2_hidden(A_199,k2_enumset1(A_199,B_200,C_201,D_202)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_668])).

tff(c_710,plain,(
    ! [A_203,B_204,C_205] : r2_hidden(A_203,k1_enumset1(A_203,B_204,C_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_696])).

tff(c_724,plain,(
    ! [A_206,B_207] : r2_hidden(A_206,k2_tarski(A_206,B_207)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_710])).

tff(c_66,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_106,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(k1_setfam_1(B_64),A_65)
      | ~ r2_hidden(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_109,plain,(
    ! [A_45,B_46,A_65] :
      ( r1_tarski(k3_xboole_0(A_45,B_46),A_65)
      | ~ r2_hidden(A_65,k2_tarski(A_45,B_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_106])).

tff(c_741,plain,(
    ! [A_208,B_209] : r1_tarski(k3_xboole_0(A_208,B_209),A_208) ),
    inference(resolution,[status(thm)],[c_724,c_109])).

tff(c_755,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_741])).

tff(c_760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:52:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.44  
% 2.90/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.45  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.90/1.45  
% 2.90/1.45  %Foreground sorts:
% 2.90/1.45  
% 2.90/1.45  
% 2.90/1.45  %Background operators:
% 2.90/1.45  
% 2.90/1.45  
% 2.90/1.45  %Foreground operators:
% 2.90/1.45  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.90/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.90/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.90/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.90/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.90/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.90/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.45  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.90/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.90/1.45  
% 3.21/1.46  tff(f_100, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_2)).
% 3.21/1.46  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 3.21/1.46  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.21/1.46  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.21/1.46  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.21/1.46  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.21/1.46  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.21/1.46  tff(f_31, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.21/1.46  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.21/1.46  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.21/1.46  tff(f_37, axiom, (![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 3.21/1.46  tff(f_68, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 3.21/1.46  tff(f_74, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.21/1.46  tff(f_82, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.21/1.46  tff(c_82, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.46  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.46  tff(c_179, plain, (![A_132, B_133]: (u1_struct_0(k1_pre_topc(A_132, B_133))=B_133 | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.21/1.46  tff(c_186, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))='#skF_5' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_78, c_179])).
% 3.21/1.46  tff(c_193, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_186])).
% 3.21/1.46  tff(c_149, plain, (![A_127, B_128, C_129]: (k9_subset_1(A_127, B_128, C_129)=k3_xboole_0(B_128, C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.21/1.46  tff(c_157, plain, (![B_128]: (k9_subset_1(u1_struct_0('#skF_3'), B_128, '#skF_5')=k3_xboole_0(B_128, '#skF_5'))), inference(resolution, [status(thm)], [c_78, c_149])).
% 3.21/1.46  tff(c_70, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.21/1.46  tff(c_76, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.46  tff(c_113, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_70, c_76])).
% 3.21/1.46  tff(c_159, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_113])).
% 3.21/1.46  tff(c_211, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_159])).
% 3.21/1.46  tff(c_253, plain, (![A_139, C_140, B_141]: (k9_subset_1(A_139, C_140, B_141)=k9_subset_1(A_139, B_141, C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(A_139)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.21/1.46  tff(c_257, plain, (![B_141]: (k9_subset_1(u1_struct_0('#skF_3'), B_141, '#skF_5')=k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', B_141))), inference(resolution, [status(thm)], [c_78, c_253])).
% 3.21/1.46  tff(c_265, plain, (![B_142]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', B_142)=k3_xboole_0(B_142, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_257])).
% 3.21/1.46  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.46  tff(c_158, plain, (![B_128]: (k9_subset_1(u1_struct_0('#skF_3'), B_128, '#skF_4')=k3_xboole_0(B_128, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_149])).
% 3.21/1.46  tff(c_272, plain, (k3_xboole_0('#skF_5', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_265, c_158])).
% 3.21/1.46  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.46  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_enumset1(A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.21/1.46  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k3_enumset1(A_6, A_6, B_7, C_8, D_9)=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.46  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k4_enumset1(A_10, A_10, B_11, C_12, D_13, E_14)=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.21/1.46  tff(c_608, plain, (![C_171, G_173, D_172, B_174, A_177, E_176, F_175]: (k6_enumset1(A_177, A_177, B_174, C_171, D_172, E_176, F_175, G_173)=k5_enumset1(A_177, B_174, C_171, D_172, E_176, F_175, G_173))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.46  tff(c_12, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k6_enumset1(A_22, A_22, A_22, B_23, C_24, D_25, E_26, F_27)=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.46  tff(c_624, plain, (![G_182, C_180, D_178, F_183, E_179, B_181]: (k5_enumset1(B_181, B_181, C_180, D_178, E_179, F_183, G_182)=k4_enumset1(B_181, C_180, D_178, E_179, F_183, G_182))), inference(superposition, [status(thm), theory('equality')], [c_608, c_12])).
% 3.21/1.46  tff(c_30, plain, (![C_33, B_32, F_36, E_35, G_37, D_34, I_41]: (r2_hidden(I_41, k5_enumset1(I_41, B_32, C_33, D_34, E_35, F_36, G_37)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.21/1.46  tff(c_654, plain, (![G_188, C_189, D_185, B_184, E_187, F_186]: (r2_hidden(B_184, k4_enumset1(B_184, C_189, D_185, E_187, F_186, G_188)))), inference(superposition, [status(thm), theory('equality')], [c_624, c_30])).
% 3.21/1.46  tff(c_668, plain, (![E_191, D_193, C_194, B_190, A_192]: (r2_hidden(A_192, k3_enumset1(A_192, B_190, C_194, D_193, E_191)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_654])).
% 3.21/1.46  tff(c_696, plain, (![A_199, B_200, C_201, D_202]: (r2_hidden(A_199, k2_enumset1(A_199, B_200, C_201, D_202)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_668])).
% 3.21/1.46  tff(c_710, plain, (![A_203, B_204, C_205]: (r2_hidden(A_203, k1_enumset1(A_203, B_204, C_205)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_696])).
% 3.21/1.46  tff(c_724, plain, (![A_206, B_207]: (r2_hidden(A_206, k2_tarski(A_206, B_207)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_710])).
% 3.21/1.46  tff(c_66, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.21/1.46  tff(c_106, plain, (![B_64, A_65]: (r1_tarski(k1_setfam_1(B_64), A_65) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.21/1.46  tff(c_109, plain, (![A_45, B_46, A_65]: (r1_tarski(k3_xboole_0(A_45, B_46), A_65) | ~r2_hidden(A_65, k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_106])).
% 3.21/1.46  tff(c_741, plain, (![A_208, B_209]: (r1_tarski(k3_xboole_0(A_208, B_209), A_208))), inference(resolution, [status(thm)], [c_724, c_109])).
% 3.21/1.46  tff(c_755, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_272, c_741])).
% 3.21/1.46  tff(c_760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_755])).
% 3.21/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.46  
% 3.21/1.46  Inference rules
% 3.21/1.46  ----------------------
% 3.21/1.46  #Ref     : 0
% 3.21/1.46  #Sup     : 155
% 3.21/1.46  #Fact    : 0
% 3.21/1.46  #Define  : 0
% 3.21/1.46  #Split   : 2
% 3.21/1.46  #Chain   : 0
% 3.21/1.46  #Close   : 0
% 3.21/1.46  
% 3.21/1.46  Ordering : KBO
% 3.21/1.46  
% 3.21/1.46  Simplification rules
% 3.21/1.46  ----------------------
% 3.21/1.46  #Subsume      : 14
% 3.21/1.46  #Demod        : 35
% 3.21/1.46  #Tautology    : 64
% 3.21/1.46  #SimpNegUnit  : 1
% 3.21/1.46  #BackRed      : 2
% 3.21/1.46  
% 3.21/1.46  #Partial instantiations: 0
% 3.21/1.46  #Strategies tried      : 1
% 3.21/1.46  
% 3.21/1.46  Timing (in seconds)
% 3.21/1.46  ----------------------
% 3.24/1.46  Preprocessing        : 0.35
% 3.24/1.46  Parsing              : 0.17
% 3.24/1.46  CNF conversion       : 0.02
% 3.24/1.46  Main loop            : 0.33
% 3.24/1.46  Inferencing          : 0.11
% 3.24/1.46  Reduction            : 0.10
% 3.24/1.46  Demodulation         : 0.07
% 3.24/1.46  BG Simplification    : 0.03
% 3.24/1.46  Subsumption          : 0.08
% 3.24/1.46  Abstraction          : 0.03
% 3.24/1.47  MUC search           : 0.00
% 3.24/1.47  Cooper               : 0.00
% 3.24/1.47  Total                : 0.71
% 3.24/1.47  Index Insertion      : 0.00
% 3.24/1.47  Index Deletion       : 0.00
% 3.24/1.47  Index Matching       : 0.00
% 3.24/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
