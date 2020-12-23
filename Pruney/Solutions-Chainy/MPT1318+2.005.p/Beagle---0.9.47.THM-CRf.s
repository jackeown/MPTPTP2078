%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:05 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   73 (  87 expanded)
%              Number of leaves         :   38 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 109 expanded)
%              Number of equality atoms :   33 (  38 expanded)
%              Maximal formula depth    :   20 (   4 average)
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
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

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

tff(c_449,plain,(
    ! [B_159,D_158,A_162,F_160,E_161,C_157] : k5_enumset1(A_162,A_162,B_159,C_157,D_158,E_161,F_160) = k4_enumset1(A_162,B_159,C_157,D_158,E_161,F_160) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [C_33,B_32,F_36,E_35,G_37,D_34,I_41] : r2_hidden(I_41,k5_enumset1(I_41,B_32,C_33,D_34,E_35,F_36,G_37)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_479,plain,(
    ! [D_166,E_163,F_168,C_167,A_164,B_165] : r2_hidden(A_164,k4_enumset1(A_164,B_165,C_167,D_166,E_163,F_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_30])).

tff(c_493,plain,(
    ! [D_172,A_171,E_170,C_173,B_169] : r2_hidden(A_171,k3_enumset1(A_171,B_169,C_173,D_172,E_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_479])).

tff(c_507,plain,(
    ! [A_174,B_175,C_176,D_177] : r2_hidden(A_174,k2_enumset1(A_174,B_175,C_176,D_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_493])).

tff(c_521,plain,(
    ! [A_178,B_179,C_180] : r2_hidden(A_178,k1_enumset1(A_178,B_179,C_180)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_507])).

tff(c_535,plain,(
    ! [A_181,B_182] : r2_hidden(A_181,k2_tarski(A_181,B_182)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_521])).

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

tff(c_552,plain,(
    ! [A_183,B_184] : r1_tarski(k3_xboole_0(A_183,B_184),A_183) ),
    inference(resolution,[status(thm)],[c_535,c_109])).

tff(c_563,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_552])).

tff(c_568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:20:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.41  
% 2.92/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.92/1.41  
% 2.92/1.41  %Foreground sorts:
% 2.92/1.41  
% 2.92/1.41  
% 2.92/1.41  %Background operators:
% 2.92/1.41  
% 2.92/1.41  
% 2.92/1.41  %Foreground operators:
% 2.92/1.41  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.92/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.92/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.92/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.92/1.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.92/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.92/1.41  
% 2.92/1.43  tff(f_100, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_2)).
% 2.92/1.43  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.92/1.43  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.92/1.43  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.92/1.43  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 2.92/1.43  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.92/1.43  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.92/1.43  tff(f_31, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.92/1.43  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.92/1.43  tff(f_35, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.92/1.43  tff(f_68, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 2.92/1.43  tff(f_74, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.92/1.43  tff(f_82, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.92/1.43  tff(c_82, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.92/1.43  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.92/1.43  tff(c_179, plain, (![A_132, B_133]: (u1_struct_0(k1_pre_topc(A_132, B_133))=B_133 | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.92/1.43  tff(c_186, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))='#skF_5' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_78, c_179])).
% 2.92/1.43  tff(c_193, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_186])).
% 2.92/1.43  tff(c_149, plain, (![A_127, B_128, C_129]: (k9_subset_1(A_127, B_128, C_129)=k3_xboole_0(B_128, C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.92/1.43  tff(c_157, plain, (![B_128]: (k9_subset_1(u1_struct_0('#skF_3'), B_128, '#skF_5')=k3_xboole_0(B_128, '#skF_5'))), inference(resolution, [status(thm)], [c_78, c_149])).
% 2.92/1.43  tff(c_70, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.92/1.43  tff(c_76, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.92/1.43  tff(c_113, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_70, c_76])).
% 2.92/1.43  tff(c_159, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_113])).
% 2.92/1.43  tff(c_211, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_159])).
% 2.92/1.43  tff(c_253, plain, (![A_139, C_140, B_141]: (k9_subset_1(A_139, C_140, B_141)=k9_subset_1(A_139, B_141, C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(A_139)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.43  tff(c_257, plain, (![B_141]: (k9_subset_1(u1_struct_0('#skF_3'), B_141, '#skF_5')=k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', B_141))), inference(resolution, [status(thm)], [c_78, c_253])).
% 2.92/1.43  tff(c_265, plain, (![B_142]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_5', B_142)=k3_xboole_0(B_142, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_257])).
% 2.92/1.43  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.92/1.43  tff(c_158, plain, (![B_128]: (k9_subset_1(u1_struct_0('#skF_3'), B_128, '#skF_4')=k3_xboole_0(B_128, '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_149])).
% 2.92/1.43  tff(c_272, plain, (k3_xboole_0('#skF_5', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_265, c_158])).
% 2.92/1.43  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.43  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_enumset1(A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.92/1.43  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k3_enumset1(A_6, A_6, B_7, C_8, D_9)=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.43  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k4_enumset1(A_10, A_10, B_11, C_12, D_13, E_14)=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.43  tff(c_449, plain, (![B_159, D_158, A_162, F_160, E_161, C_157]: (k5_enumset1(A_162, A_162, B_159, C_157, D_158, E_161, F_160)=k4_enumset1(A_162, B_159, C_157, D_158, E_161, F_160))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.43  tff(c_30, plain, (![C_33, B_32, F_36, E_35, G_37, D_34, I_41]: (r2_hidden(I_41, k5_enumset1(I_41, B_32, C_33, D_34, E_35, F_36, G_37)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.92/1.43  tff(c_479, plain, (![D_166, E_163, F_168, C_167, A_164, B_165]: (r2_hidden(A_164, k4_enumset1(A_164, B_165, C_167, D_166, E_163, F_168)))), inference(superposition, [status(thm), theory('equality')], [c_449, c_30])).
% 2.92/1.43  tff(c_493, plain, (![D_172, A_171, E_170, C_173, B_169]: (r2_hidden(A_171, k3_enumset1(A_171, B_169, C_173, D_172, E_170)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_479])).
% 2.92/1.43  tff(c_507, plain, (![A_174, B_175, C_176, D_177]: (r2_hidden(A_174, k2_enumset1(A_174, B_175, C_176, D_177)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_493])).
% 2.92/1.43  tff(c_521, plain, (![A_178, B_179, C_180]: (r2_hidden(A_178, k1_enumset1(A_178, B_179, C_180)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_507])).
% 2.92/1.43  tff(c_535, plain, (![A_181, B_182]: (r2_hidden(A_181, k2_tarski(A_181, B_182)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_521])).
% 2.92/1.43  tff(c_66, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.92/1.43  tff(c_106, plain, (![B_64, A_65]: (r1_tarski(k1_setfam_1(B_64), A_65) | ~r2_hidden(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.92/1.43  tff(c_109, plain, (![A_45, B_46, A_65]: (r1_tarski(k3_xboole_0(A_45, B_46), A_65) | ~r2_hidden(A_65, k2_tarski(A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_106])).
% 2.92/1.43  tff(c_552, plain, (![A_183, B_184]: (r1_tarski(k3_xboole_0(A_183, B_184), A_183))), inference(resolution, [status(thm)], [c_535, c_109])).
% 2.92/1.43  tff(c_563, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_272, c_552])).
% 2.92/1.43  tff(c_568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_563])).
% 2.92/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.43  
% 2.92/1.43  Inference rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Ref     : 0
% 2.92/1.43  #Sup     : 109
% 2.92/1.43  #Fact    : 0
% 2.92/1.43  #Define  : 0
% 2.92/1.43  #Split   : 1
% 2.92/1.43  #Chain   : 0
% 2.92/1.43  #Close   : 0
% 2.92/1.43  
% 2.92/1.43  Ordering : KBO
% 2.92/1.43  
% 2.92/1.43  Simplification rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Subsume      : 3
% 2.92/1.43  #Demod        : 26
% 2.92/1.43  #Tautology    : 42
% 2.92/1.43  #SimpNegUnit  : 1
% 2.92/1.43  #BackRed      : 2
% 2.92/1.43  
% 2.92/1.43  #Partial instantiations: 0
% 2.92/1.43  #Strategies tried      : 1
% 2.92/1.43  
% 2.92/1.43  Timing (in seconds)
% 2.92/1.43  ----------------------
% 2.92/1.43  Preprocessing        : 0.36
% 2.92/1.43  Parsing              : 0.17
% 2.92/1.43  CNF conversion       : 0.03
% 2.92/1.43  Main loop            : 0.30
% 2.92/1.43  Inferencing          : 0.09
% 2.92/1.43  Reduction            : 0.09
% 2.92/1.43  Demodulation         : 0.06
% 2.92/1.43  BG Simplification    : 0.03
% 2.92/1.43  Subsumption          : 0.08
% 2.92/1.43  Abstraction          : 0.03
% 2.92/1.43  MUC search           : 0.00
% 2.92/1.43  Cooper               : 0.00
% 2.92/1.43  Total                : 0.69
% 2.92/1.43  Index Insertion      : 0.00
% 2.92/1.43  Index Deletion       : 0.00
% 2.92/1.43  Index Matching       : 0.00
% 2.92/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
