%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:06 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  58 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_21,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_42,plain,(
    ! [A_25,B_26,C_27] :
      ( k9_subset_1(A_25,B_26,C_27) = k3_xboole_0(B_26,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55,plain,(
    ! [A_28,B_29] : k9_subset_1(A_28,B_29,A_28) = k3_xboole_0(B_29,A_28) ),
    inference(resolution,[status(thm)],[c_21,c_42])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k9_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61,plain,(
    ! [B_29,A_28] :
      ( m1_subset_1(k3_xboole_0(B_29,A_28),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(A_28,k1_zfmisc_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_6])).

tff(c_67,plain,(
    ! [B_29,A_28] : m1_subset_1(k3_xboole_0(B_29,A_28),k1_zfmisc_1(A_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_61])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_110,plain,(
    ! [A_36,B_37] :
      ( u1_struct_0(k1_pre_topc(A_36,B_37)) = B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_127,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_110])).

tff(c_145,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_52,plain,(
    ! [B_26] : k9_subset_1(u1_struct_0('#skF_1'),B_26,'#skF_3') = k3_xboole_0(B_26,'#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_42])).

tff(c_14,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_91,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_14])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_145,c_91])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.16  %$ m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.86/1.16  
% 1.86/1.16  %Foreground sorts:
% 1.86/1.16  
% 1.86/1.16  
% 1.86/1.16  %Background operators:
% 1.86/1.16  
% 1.86/1.16  
% 1.86/1.16  %Foreground operators:
% 1.86/1.16  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.86/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.86/1.16  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.86/1.16  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 1.86/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.16  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.86/1.16  
% 1.86/1.17  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.86/1.17  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.86/1.17  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.86/1.17  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 1.86/1.17  tff(f_57, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_2)).
% 1.86/1.17  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 1.86/1.17  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.17  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.17  tff(c_21, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.86/1.17  tff(c_42, plain, (![A_25, B_26, C_27]: (k9_subset_1(A_25, B_26, C_27)=k3_xboole_0(B_26, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.86/1.17  tff(c_55, plain, (![A_28, B_29]: (k9_subset_1(A_28, B_29, A_28)=k3_xboole_0(B_29, A_28))), inference(resolution, [status(thm)], [c_21, c_42])).
% 1.86/1.17  tff(c_6, plain, (![A_3, B_4, C_5]: (m1_subset_1(k9_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(C_5, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.17  tff(c_61, plain, (![B_29, A_28]: (m1_subset_1(k3_xboole_0(B_29, A_28), k1_zfmisc_1(A_28)) | ~m1_subset_1(A_28, k1_zfmisc_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_55, c_6])).
% 1.86/1.17  tff(c_67, plain, (![B_29, A_28]: (m1_subset_1(k3_xboole_0(B_29, A_28), k1_zfmisc_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_21, c_61])).
% 1.86/1.17  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.86/1.17  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.86/1.17  tff(c_110, plain, (![A_36, B_37]: (u1_struct_0(k1_pre_topc(A_36, B_37))=B_37 | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.86/1.17  tff(c_127, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_16, c_110])).
% 1.86/1.17  tff(c_145, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_127])).
% 1.86/1.17  tff(c_52, plain, (![B_26]: (k9_subset_1(u1_struct_0('#skF_1'), B_26, '#skF_3')=k3_xboole_0(B_26, '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_42])).
% 1.86/1.17  tff(c_14, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.86/1.17  tff(c_91, plain, (~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_14])).
% 1.86/1.17  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_145, c_91])).
% 1.86/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  Inference rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Ref     : 0
% 1.86/1.17  #Sup     : 33
% 1.86/1.17  #Fact    : 0
% 1.86/1.17  #Define  : 0
% 1.86/1.17  #Split   : 0
% 1.86/1.17  #Chain   : 0
% 1.86/1.17  #Close   : 0
% 1.86/1.17  
% 1.86/1.17  Ordering : KBO
% 1.86/1.17  
% 1.86/1.17  Simplification rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Subsume      : 0
% 1.86/1.17  #Demod        : 11
% 1.86/1.17  #Tautology    : 14
% 1.86/1.17  #SimpNegUnit  : 0
% 1.86/1.17  #BackRed      : 1
% 1.86/1.17  
% 1.86/1.17  #Partial instantiations: 0
% 1.86/1.17  #Strategies tried      : 1
% 1.86/1.17  
% 1.86/1.17  Timing (in seconds)
% 1.86/1.17  ----------------------
% 1.86/1.17  Preprocessing        : 0.28
% 1.86/1.17  Parsing              : 0.15
% 1.86/1.17  CNF conversion       : 0.02
% 1.86/1.17  Main loop            : 0.13
% 1.86/1.17  Inferencing          : 0.05
% 1.86/1.17  Reduction            : 0.04
% 1.86/1.17  Demodulation         : 0.03
% 1.86/1.17  BG Simplification    : 0.01
% 1.86/1.17  Subsumption          : 0.02
% 1.86/1.17  Abstraction          : 0.01
% 1.86/1.17  MUC search           : 0.00
% 1.86/1.17  Cooper               : 0.00
% 1.86/1.17  Total                : 0.43
% 1.86/1.17  Index Insertion      : 0.00
% 1.86/1.17  Index Deletion       : 0.00
% 1.86/1.17  Index Matching       : 0.00
% 1.86/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
