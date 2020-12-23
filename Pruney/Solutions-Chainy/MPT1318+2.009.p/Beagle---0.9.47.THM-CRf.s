%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:05 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  77 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_178,plain,(
    ! [A_41,B_42] :
      ( u1_struct_0(k1_pre_topc(A_41,B_42)) = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_185,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_178])).

tff(c_192,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_185])).

tff(c_51,plain,(
    ! [A_28,B_29,C_30] :
      ( k9_subset_1(A_28,B_29,C_30) = k3_xboole_0(B_29,C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [B_29] : k9_subset_1(u1_struct_0('#skF_1'),B_29,'#skF_3') = k3_xboole_0(B_29,'#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_51])).

tff(c_81,plain,(
    ! [A_33,C_34,B_35] :
      ( k9_subset_1(A_33,C_34,B_35) = k9_subset_1(A_33,B_35,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [B_35] : k9_subset_1(u1_struct_0('#skF_1'),B_35,'#skF_3') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_35) ),
    inference(resolution,[status(thm)],[c_18,c_81])).

tff(c_93,plain,(
    ! [B_36] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_3',B_36) = k3_xboole_0(B_36,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_85])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    ! [B_29] : k9_subset_1(u1_struct_0('#skF_1'),B_29,'#skF_2') = k3_xboole_0(B_29,'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_100,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_60])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_12,c_16])).

tff(c_61,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_50])).

tff(c_120,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_61])).

tff(c_196,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_120])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:32:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.25  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.25  
% 1.99/1.25  %Foreground sorts:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Background operators:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Foreground operators:
% 1.99/1.25  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.99/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.25  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 1.99/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.99/1.25  
% 1.99/1.26  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.99/1.26  tff(f_59, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_2)).
% 1.99/1.26  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 1.99/1.26  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.99/1.26  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 1.99/1.26  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.99/1.26  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.26  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.26  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.26  tff(c_178, plain, (![A_41, B_42]: (u1_struct_0(k1_pre_topc(A_41, B_42))=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.99/1.26  tff(c_185, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_178])).
% 1.99/1.26  tff(c_192, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_185])).
% 1.99/1.26  tff(c_51, plain, (![A_28, B_29, C_30]: (k9_subset_1(A_28, B_29, C_30)=k3_xboole_0(B_29, C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.26  tff(c_59, plain, (![B_29]: (k9_subset_1(u1_struct_0('#skF_1'), B_29, '#skF_3')=k3_xboole_0(B_29, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_51])).
% 1.99/1.26  tff(c_81, plain, (![A_33, C_34, B_35]: (k9_subset_1(A_33, C_34, B_35)=k9_subset_1(A_33, B_35, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.26  tff(c_85, plain, (![B_35]: (k9_subset_1(u1_struct_0('#skF_1'), B_35, '#skF_3')=k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_35))), inference(resolution, [status(thm)], [c_18, c_81])).
% 1.99/1.26  tff(c_93, plain, (![B_36]: (k9_subset_1(u1_struct_0('#skF_1'), '#skF_3', B_36)=k3_xboole_0(B_36, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_85])).
% 1.99/1.26  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.26  tff(c_60, plain, (![B_29]: (k9_subset_1(u1_struct_0('#skF_1'), B_29, '#skF_2')=k3_xboole_0(B_29, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_51])).
% 1.99/1.26  tff(c_100, plain, (k3_xboole_0('#skF_2', '#skF_3')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_60])).
% 1.99/1.26  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.26  tff(c_16, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.26  tff(c_50, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_12, c_16])).
% 1.99/1.26  tff(c_61, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_50])).
% 1.99/1.26  tff(c_120, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_61])).
% 1.99/1.26  tff(c_196, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_120])).
% 1.99/1.26  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_196])).
% 1.99/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.26  
% 1.99/1.26  Inference rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Ref     : 0
% 1.99/1.26  #Sup     : 39
% 1.99/1.26  #Fact    : 0
% 1.99/1.26  #Define  : 0
% 1.99/1.26  #Split   : 0
% 1.99/1.26  #Chain   : 0
% 1.99/1.26  #Close   : 0
% 1.99/1.26  
% 1.99/1.26  Ordering : KBO
% 1.99/1.26  
% 1.99/1.26  Simplification rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Subsume      : 1
% 1.99/1.26  #Demod        : 16
% 1.99/1.26  #Tautology    : 22
% 1.99/1.26  #SimpNegUnit  : 0
% 1.99/1.26  #BackRed      : 5
% 1.99/1.26  
% 1.99/1.26  #Partial instantiations: 0
% 1.99/1.26  #Strategies tried      : 1
% 1.99/1.26  
% 1.99/1.26  Timing (in seconds)
% 1.99/1.26  ----------------------
% 1.99/1.26  Preprocessing        : 0.30
% 1.99/1.26  Parsing              : 0.17
% 1.99/1.26  CNF conversion       : 0.02
% 1.99/1.26  Main loop            : 0.14
% 1.99/1.26  Inferencing          : 0.06
% 1.99/1.26  Reduction            : 0.05
% 1.99/1.26  Demodulation         : 0.04
% 1.99/1.26  BG Simplification    : 0.01
% 1.99/1.26  Subsumption          : 0.02
% 1.99/1.26  Abstraction          : 0.01
% 1.99/1.26  MUC search           : 0.00
% 1.99/1.26  Cooper               : 0.00
% 1.99/1.26  Total                : 0.47
% 1.99/1.26  Index Insertion      : 0.00
% 1.99/1.26  Index Deletion       : 0.00
% 1.99/1.26  Index Matching       : 0.00
% 1.99/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
