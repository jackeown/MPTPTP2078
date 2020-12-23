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
% DateTime   : Thu Dec  3 10:23:05 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :   76 (  90 expanded)
%              Number of leaves         :   39 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 113 expanded)
%              Number of equality atoms :   36 (  41 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_81,axiom,(
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
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_88,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_84,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_287,plain,(
    ! [A_159,B_160] :
      ( u1_struct_0(k1_pre_topc(A_159,B_160)) = B_160
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_294,plain,
    ( u1_struct_0(k1_pre_topc('#skF_3','#skF_5')) = '#skF_5'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_287])).

tff(c_301,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_294])).

tff(c_146,plain,(
    ! [A_131,B_132,C_133] :
      ( k9_subset_1(A_131,B_132,C_133) = k3_xboole_0(B_132,C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(A_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_154,plain,(
    ! [B_132] : k9_subset_1(u1_struct_0('#skF_3'),B_132,'#skF_5') = k3_xboole_0(B_132,'#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_146])).

tff(c_76,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,k1_zfmisc_1(B_49))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_82,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_124,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),u1_struct_0(k1_pre_topc('#skF_3','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_76,c_82])).

tff(c_156,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),u1_struct_0(k1_pre_topc('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_124])).

tff(c_306,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_156])).

tff(c_202,plain,(
    ! [A_151,C_152,B_153] :
      ( k9_subset_1(A_151,C_152,B_153) = k9_subset_1(A_151,B_153,C_152)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_206,plain,(
    ! [B_153] : k9_subset_1(u1_struct_0('#skF_3'),B_153,'#skF_5') = k9_subset_1(u1_struct_0('#skF_3'),'#skF_5',B_153) ),
    inference(resolution,[status(thm)],[c_84,c_202])).

tff(c_214,plain,(
    ! [B_154] : k9_subset_1(u1_struct_0('#skF_3'),'#skF_5',B_154) = k3_xboole_0(B_154,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_206])).

tff(c_86,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_155,plain,(
    ! [B_132] : k9_subset_1(u1_struct_0('#skF_3'),B_132,'#skF_4') = k3_xboole_0(B_132,'#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_146])).

tff(c_221,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_155])).

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

tff(c_10,plain,(
    ! [B_16,A_15,D_18,E_19,F_20,C_17] : k5_enumset1(A_15,A_15,B_16,C_17,D_18,E_19,F_20) = k4_enumset1(A_15,B_16,C_17,D_18,E_19,F_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_578,plain,(
    ! [C_187,G_184,A_185,B_189,F_188,E_190,D_186] : k6_enumset1(A_185,A_185,B_189,C_187,D_186,E_190,F_188,G_184) = k5_enumset1(A_185,B_189,C_187,D_186,E_190,F_188,G_184) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [C_33,B_32,H_38,F_36,E_35,G_37,D_34,J_42] : r2_hidden(J_42,k6_enumset1(J_42,B_32,C_33,D_34,E_35,F_36,G_37,H_38)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_611,plain,(
    ! [C_196,A_192,E_194,F_191,B_193,D_197,G_195] : r2_hidden(A_192,k5_enumset1(A_192,B_193,C_196,D_197,E_194,F_191,G_195)) ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_32])).

tff(c_625,plain,(
    ! [B_200,D_199,A_203,C_198,F_201,E_202] : r2_hidden(A_203,k4_enumset1(A_203,B_200,C_198,D_199,E_202,F_201)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_611])).

tff(c_639,plain,(
    ! [E_205,B_204,A_206,D_207,C_208] : r2_hidden(A_206,k3_enumset1(A_206,B_204,C_208,D_207,E_205)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_625])).

tff(c_653,plain,(
    ! [A_209,B_210,C_211,D_212] : r2_hidden(A_209,k2_enumset1(A_209,B_210,C_211,D_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_639])).

tff(c_667,plain,(
    ! [A_213,B_214,C_215] : r2_hidden(A_213,k1_enumset1(A_213,B_214,C_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_653])).

tff(c_681,plain,(
    ! [A_216,B_217] : r2_hidden(A_216,k2_tarski(A_216,B_217)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_667])).

tff(c_72,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_125,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k1_setfam_1(B_67),A_68)
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_128,plain,(
    ! [A_46,B_47,A_68] :
      ( r1_tarski(k3_xboole_0(A_46,B_47),A_68)
      | ~ r2_hidden(A_68,k2_tarski(A_46,B_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_125])).

tff(c_698,plain,(
    ! [A_218,B_219] : r1_tarski(k3_xboole_0(A_218,B_219),A_218) ),
    inference(resolution,[status(thm)],[c_681,c_128])).

tff(c_709,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_698])).

tff(c_714,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_709])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/2.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/2.04  
% 4.20/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/2.05  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.20/2.05  
% 4.20/2.05  %Foreground sorts:
% 4.20/2.05  
% 4.20/2.05  
% 4.20/2.05  %Background operators:
% 4.20/2.05  
% 4.20/2.05  
% 4.20/2.05  %Foreground operators:
% 4.20/2.05  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 4.20/2.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/2.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.20/2.05  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.20/2.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.20/2.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.20/2.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.20/2.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.20/2.05  tff('#skF_5', type, '#skF_5': $i).
% 4.20/2.05  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.20/2.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.20/2.05  tff('#skF_3', type, '#skF_3': $i).
% 4.20/2.05  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.20/2.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/2.05  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.20/2.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/2.05  tff('#skF_4', type, '#skF_4': $i).
% 4.20/2.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/2.05  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.20/2.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.20/2.05  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.20/2.05  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.20/2.05  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.20/2.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/2.05  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.20/2.05  
% 4.20/2.07  tff(f_103, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_2)).
% 4.20/2.07  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 4.20/2.07  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.20/2.07  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.20/2.07  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.20/2.07  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.20/2.07  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.20/2.07  tff(f_31, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.20/2.07  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.20/2.07  tff(f_35, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.20/2.07  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.20/2.07  tff(f_71, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 4.20/2.07  tff(f_77, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.20/2.07  tff(f_85, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 4.20/2.07  tff(c_88, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/2.07  tff(c_84, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/2.07  tff(c_287, plain, (![A_159, B_160]: (u1_struct_0(k1_pre_topc(A_159, B_160))=B_160 | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.20/2.07  tff(c_294, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))='#skF_5' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_84, c_287])).
% 4.20/2.07  tff(c_301, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_294])).
% 4.20/2.07  tff(c_146, plain, (![A_131, B_132, C_133]: (k9_subset_1(A_131, B_132, C_133)=k3_xboole_0(B_132, C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(A_131)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.20/2.07  tff(c_154, plain, (![B_132]: (k9_subset_1(u1_struct_0('#skF_3'), B_132, '#skF_5')=k3_xboole_0(B_132, '#skF_5'))), inference(resolution, [status(thm)], [c_84, c_146])).
% 4.20/2.07  tff(c_76, plain, (![A_48, B_49]: (m1_subset_1(A_48, k1_zfmisc_1(B_49)) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.20/2.07  tff(c_82, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/2.07  tff(c_124, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_76, c_82])).
% 4.20/2.07  tff(c_156, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_124])).
% 4.20/2.07  tff(c_306, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_156])).
% 4.20/2.07  tff(c_202, plain, (![A_151, C_152, B_153]: (k9_subset_1(A_151, C_152, B_153)=k9_subset_1(A_151, B_153, C_152) | ~m1_subset_1(C_152, k1_zfmisc_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.20/2.07  tff(c_206, plain, (![B_153]: (k9_subset_1(u1_struct_0('#skF_3'), B_153, '#skF_5')=k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', B_153))), inference(resolution, [status(thm)], [c_84, c_202])).
% 4.20/2.07  tff(c_214, plain, (![B_154]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', B_154)=k3_xboole_0(B_154, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_206])).
% 4.20/2.07  tff(c_86, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.20/2.07  tff(c_155, plain, (![B_132]: (k9_subset_1(u1_struct_0('#skF_3'), B_132, '#skF_4')=k3_xboole_0(B_132, '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_146])).
% 4.20/2.07  tff(c_221, plain, (k3_xboole_0('#skF_5', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_214, c_155])).
% 4.20/2.07  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.20/2.07  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_enumset1(A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.20/2.07  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k3_enumset1(A_6, A_6, B_7, C_8, D_9)=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.20/2.07  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k4_enumset1(A_10, A_10, B_11, C_12, D_13, E_14)=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.20/2.07  tff(c_10, plain, (![B_16, A_15, D_18, E_19, F_20, C_17]: (k5_enumset1(A_15, A_15, B_16, C_17, D_18, E_19, F_20)=k4_enumset1(A_15, B_16, C_17, D_18, E_19, F_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.20/2.07  tff(c_578, plain, (![C_187, G_184, A_185, B_189, F_188, E_190, D_186]: (k6_enumset1(A_185, A_185, B_189, C_187, D_186, E_190, F_188, G_184)=k5_enumset1(A_185, B_189, C_187, D_186, E_190, F_188, G_184))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.20/2.07  tff(c_32, plain, (![C_33, B_32, H_38, F_36, E_35, G_37, D_34, J_42]: (r2_hidden(J_42, k6_enumset1(J_42, B_32, C_33, D_34, E_35, F_36, G_37, H_38)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.20/2.07  tff(c_611, plain, (![C_196, A_192, E_194, F_191, B_193, D_197, G_195]: (r2_hidden(A_192, k5_enumset1(A_192, B_193, C_196, D_197, E_194, F_191, G_195)))), inference(superposition, [status(thm), theory('equality')], [c_578, c_32])).
% 4.20/2.07  tff(c_625, plain, (![B_200, D_199, A_203, C_198, F_201, E_202]: (r2_hidden(A_203, k4_enumset1(A_203, B_200, C_198, D_199, E_202, F_201)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_611])).
% 4.20/2.07  tff(c_639, plain, (![E_205, B_204, A_206, D_207, C_208]: (r2_hidden(A_206, k3_enumset1(A_206, B_204, C_208, D_207, E_205)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_625])).
% 4.20/2.07  tff(c_653, plain, (![A_209, B_210, C_211, D_212]: (r2_hidden(A_209, k2_enumset1(A_209, B_210, C_211, D_212)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_639])).
% 4.20/2.07  tff(c_667, plain, (![A_213, B_214, C_215]: (r2_hidden(A_213, k1_enumset1(A_213, B_214, C_215)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_653])).
% 4.20/2.07  tff(c_681, plain, (![A_216, B_217]: (r2_hidden(A_216, k2_tarski(A_216, B_217)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_667])).
% 4.20/2.07  tff(c_72, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.20/2.07  tff(c_125, plain, (![B_67, A_68]: (r1_tarski(k1_setfam_1(B_67), A_68) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.20/2.07  tff(c_128, plain, (![A_46, B_47, A_68]: (r1_tarski(k3_xboole_0(A_46, B_47), A_68) | ~r2_hidden(A_68, k2_tarski(A_46, B_47)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_125])).
% 4.20/2.07  tff(c_698, plain, (![A_218, B_219]: (r1_tarski(k3_xboole_0(A_218, B_219), A_218))), inference(resolution, [status(thm)], [c_681, c_128])).
% 4.20/2.07  tff(c_709, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_221, c_698])).
% 4.20/2.07  tff(c_714, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_709])).
% 4.20/2.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.20/2.07  
% 4.20/2.07  Inference rules
% 4.20/2.07  ----------------------
% 4.20/2.07  #Ref     : 0
% 4.20/2.07  #Sup     : 141
% 4.20/2.07  #Fact    : 0
% 4.20/2.07  #Define  : 0
% 4.20/2.07  #Split   : 2
% 4.20/2.07  #Chain   : 0
% 4.20/2.07  #Close   : 0
% 4.20/2.07  
% 4.20/2.07  Ordering : KBO
% 4.20/2.07  
% 4.20/2.07  Simplification rules
% 4.20/2.07  ----------------------
% 4.20/2.07  #Subsume      : 6
% 4.20/2.07  #Demod        : 33
% 4.20/2.07  #Tautology    : 58
% 4.20/2.07  #SimpNegUnit  : 1
% 4.20/2.07  #BackRed      : 4
% 4.20/2.07  
% 4.20/2.07  #Partial instantiations: 0
% 4.20/2.07  #Strategies tried      : 1
% 4.20/2.07  
% 4.20/2.07  Timing (in seconds)
% 4.20/2.07  ----------------------
% 4.51/2.08  Preprocessing        : 0.57
% 4.51/2.08  Parsing              : 0.27
% 4.51/2.08  CNF conversion       : 0.04
% 4.51/2.08  Main loop            : 0.58
% 4.51/2.08  Inferencing          : 0.19
% 4.51/2.08  Reduction            : 0.16
% 4.51/2.08  Demodulation         : 0.12
% 4.51/2.08  BG Simplification    : 0.05
% 4.51/2.08  Subsumption          : 0.15
% 4.51/2.08  Abstraction          : 0.06
% 4.51/2.08  MUC search           : 0.00
% 4.51/2.08  Cooper               : 0.00
% 4.51/2.08  Total                : 1.21
% 4.51/2.08  Index Insertion      : 0.00
% 4.51/2.08  Index Deletion       : 0.00
% 4.51/2.08  Index Matching       : 0.00
% 4.51/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
