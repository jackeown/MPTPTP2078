%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:05 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   60 (  64 expanded)
%              Number of leaves         :   34 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  72 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_67,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_enumset1(A_3,A_3,B_4,C_5) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k3_enumset1(A_6,A_6,B_7,C_8,D_9) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_285,plain,(
    ! [D_119,E_117,A_118,B_116,C_120] : k4_enumset1(A_118,A_118,B_116,C_120,D_119,E_117) = k3_enumset1(A_118,B_116,C_120,D_119,E_117) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [E_22,D_21,H_27,A_18,C_20,B_19] : r2_hidden(H_27,k4_enumset1(A_18,B_19,C_20,D_21,E_22,H_27)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_317,plain,(
    ! [A_122,B_125,D_121,E_123,C_124] : r2_hidden(E_123,k3_enumset1(A_122,B_125,C_124,D_121,E_123)) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_14])).

tff(c_350,plain,(
    ! [D_127,A_128,B_129,C_130] : r2_hidden(D_127,k2_enumset1(A_128,B_129,C_130,D_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_317])).

tff(c_354,plain,(
    ! [C_131,A_132,B_133] : r2_hidden(C_131,k1_enumset1(A_132,B_133,C_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_350])).

tff(c_358,plain,(
    ! [B_134,A_135] : r2_hidden(B_134,k2_tarski(A_135,B_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_354])).

tff(c_56,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_96,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(k1_setfam_1(B_50),A_51)
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_99,plain,(
    ! [A_31,B_32,A_51] :
      ( r1_tarski(k3_xboole_0(A_31,B_32),A_51)
      | ~ r2_hidden(A_51,k2_tarski(A_31,B_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_96])).

tff(c_362,plain,(
    ! [A_135,B_134] : r1_tarski(k3_xboole_0(A_135,B_134),B_134) ),
    inference(resolution,[status(thm)],[c_358,c_99])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_184,plain,(
    ! [A_108,B_109] :
      ( u1_struct_0(k1_pre_topc(A_108,B_109)) = B_109
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_191,plain,
    ( u1_struct_0(k1_pre_topc('#skF_3','#skF_5')) = '#skF_5'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_184])).

tff(c_198,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_191])).

tff(c_128,plain,(
    ! [A_93,B_94,C_95] :
      ( k9_subset_1(A_93,B_94,C_95) = k3_xboole_0(B_94,C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_136,plain,(
    ! [B_94] : k9_subset_1(u1_struct_0('#skF_3'),B_94,'#skF_5') = k3_xboole_0(B_94,'#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_128])).

tff(c_60,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,k1_zfmisc_1(B_34))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_103,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),u1_struct_0(k1_pre_topc('#skF_3','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_60,c_66])).

tff(c_138,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),u1_struct_0(k1_pre_topc('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_103])).

tff(c_203,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_138])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:36 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.31  
% 2.28/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.28/1.31  
% 2.28/1.31  %Foreground sorts:
% 2.28/1.31  
% 2.28/1.31  
% 2.28/1.31  %Background operators:
% 2.28/1.31  
% 2.28/1.31  
% 2.28/1.31  %Foreground operators:
% 2.28/1.31  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.28/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.28/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.28/1.31  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.28/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.28/1.31  
% 2.28/1.32  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.28/1.32  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.28/1.32  tff(f_31, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.28/1.32  tff(f_33, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.28/1.32  tff(f_61, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 2.28/1.32  tff(f_67, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.28/1.32  tff(f_75, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.28/1.32  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_2)).
% 2.28/1.32  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.28/1.32  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.28/1.32  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.28/1.32  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.32  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_enumset1(A_3, A_3, B_4, C_5)=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.32  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k3_enumset1(A_6, A_6, B_7, C_8, D_9)=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.32  tff(c_285, plain, (![D_119, E_117, A_118, B_116, C_120]: (k4_enumset1(A_118, A_118, B_116, C_120, D_119, E_117)=k3_enumset1(A_118, B_116, C_120, D_119, E_117))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.32  tff(c_14, plain, (![E_22, D_21, H_27, A_18, C_20, B_19]: (r2_hidden(H_27, k4_enumset1(A_18, B_19, C_20, D_21, E_22, H_27)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.28/1.32  tff(c_317, plain, (![A_122, B_125, D_121, E_123, C_124]: (r2_hidden(E_123, k3_enumset1(A_122, B_125, C_124, D_121, E_123)))), inference(superposition, [status(thm), theory('equality')], [c_285, c_14])).
% 2.28/1.32  tff(c_350, plain, (![D_127, A_128, B_129, C_130]: (r2_hidden(D_127, k2_enumset1(A_128, B_129, C_130, D_127)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_317])).
% 2.28/1.32  tff(c_354, plain, (![C_131, A_132, B_133]: (r2_hidden(C_131, k1_enumset1(A_132, B_133, C_131)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_350])).
% 2.28/1.32  tff(c_358, plain, (![B_134, A_135]: (r2_hidden(B_134, k2_tarski(A_135, B_134)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_354])).
% 2.28/1.32  tff(c_56, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.28/1.32  tff(c_96, plain, (![B_50, A_51]: (r1_tarski(k1_setfam_1(B_50), A_51) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.28/1.32  tff(c_99, plain, (![A_31, B_32, A_51]: (r1_tarski(k3_xboole_0(A_31, B_32), A_51) | ~r2_hidden(A_51, k2_tarski(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_96])).
% 2.28/1.32  tff(c_362, plain, (![A_135, B_134]: (r1_tarski(k3_xboole_0(A_135, B_134), B_134))), inference(resolution, [status(thm)], [c_358, c_99])).
% 2.28/1.32  tff(c_72, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.28/1.32  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.28/1.32  tff(c_184, plain, (![A_108, B_109]: (u1_struct_0(k1_pre_topc(A_108, B_109))=B_109 | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.28/1.32  tff(c_191, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))='#skF_5' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_68, c_184])).
% 2.28/1.32  tff(c_198, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_191])).
% 2.28/1.32  tff(c_128, plain, (![A_93, B_94, C_95]: (k9_subset_1(A_93, B_94, C_95)=k3_xboole_0(B_94, C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.28/1.32  tff(c_136, plain, (![B_94]: (k9_subset_1(u1_struct_0('#skF_3'), B_94, '#skF_5')=k3_xboole_0(B_94, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_128])).
% 2.28/1.32  tff(c_60, plain, (![A_33, B_34]: (m1_subset_1(A_33, k1_zfmisc_1(B_34)) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.28/1.32  tff(c_66, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.28/1.32  tff(c_103, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_60, c_66])).
% 2.28/1.32  tff(c_138, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_103])).
% 2.28/1.32  tff(c_203, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_138])).
% 2.28/1.32  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_362, c_203])).
% 2.28/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.32  
% 2.28/1.32  Inference rules
% 2.28/1.32  ----------------------
% 2.28/1.32  #Ref     : 0
% 2.28/1.32  #Sup     : 68
% 2.28/1.32  #Fact    : 0
% 2.28/1.32  #Define  : 0
% 2.28/1.32  #Split   : 0
% 2.28/1.32  #Chain   : 0
% 2.28/1.32  #Close   : 0
% 2.28/1.32  
% 2.28/1.32  Ordering : KBO
% 2.28/1.32  
% 2.28/1.32  Simplification rules
% 2.28/1.32  ----------------------
% 2.28/1.32  #Subsume      : 2
% 2.28/1.32  #Demod        : 18
% 2.28/1.32  #Tautology    : 36
% 2.28/1.32  #SimpNegUnit  : 0
% 2.28/1.32  #BackRed      : 5
% 2.28/1.32  
% 2.28/1.32  #Partial instantiations: 0
% 2.28/1.32  #Strategies tried      : 1
% 2.28/1.32  
% 2.28/1.32  Timing (in seconds)
% 2.28/1.32  ----------------------
% 2.28/1.33  Preprocessing        : 0.33
% 2.28/1.33  Parsing              : 0.16
% 2.28/1.33  CNF conversion       : 0.02
% 2.28/1.33  Main loop            : 0.23
% 2.28/1.33  Inferencing          : 0.07
% 2.28/1.33  Reduction            : 0.07
% 2.28/1.33  Demodulation         : 0.05
% 2.28/1.33  BG Simplification    : 0.02
% 2.28/1.33  Subsumption          : 0.06
% 2.28/1.33  Abstraction          : 0.02
% 2.28/1.33  MUC search           : 0.00
% 2.28/1.33  Cooper               : 0.00
% 2.28/1.33  Total                : 0.59
% 2.28/1.33  Index Insertion      : 0.00
% 2.28/1.33  Index Deletion       : 0.00
% 2.28/1.33  Index Matching       : 0.00
% 2.28/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
