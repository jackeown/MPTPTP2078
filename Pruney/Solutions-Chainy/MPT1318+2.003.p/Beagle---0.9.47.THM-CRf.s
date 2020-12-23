%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:05 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   52 (  56 expanded)
%              Number of leaves         :   30 (  33 expanded)
%              Depth                    :    5
%              Number of atoms          :   51 (  64 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

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
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_2,plain,(
    ! [A_1,B_2] : k1_enumset1(A_1,A_1,B_2) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_101,plain,(
    ! [A_59,B_60,C_61] : k2_enumset1(A_59,A_59,B_60,C_61) = k1_enumset1(A_59,B_60,C_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [F_16,A_9,B_10,C_11] : r2_hidden(F_16,k2_enumset1(A_9,B_10,C_11,F_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    ! [C_62,A_63,B_64] : r2_hidden(C_62,k1_enumset1(A_63,B_64,C_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_10])).

tff(c_125,plain,(
    ! [B_2,A_1] : r2_hidden(B_2,k2_tarski(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_122])).

tff(c_88,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_setfam_1(B_25),A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_138,plain,(
    ! [A_75,B_76,A_77] :
      ( r1_tarski(k3_xboole_0(A_75,B_76),A_77)
      | ~ r2_hidden(A_77,k2_tarski(A_75,B_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_46])).

tff(c_146,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),B_2) ),
    inference(resolution,[status(thm)],[c_125,c_138])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_471,plain,(
    ! [A_110,B_111] :
      ( u1_struct_0(k1_pre_topc(A_110,B_111)) = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_478,plain,
    ( u1_struct_0(k1_pre_topc('#skF_3','#skF_5')) = '#skF_5'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_471])).

tff(c_485,plain,(
    u1_struct_0(k1_pre_topc('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_478])).

tff(c_148,plain,(
    ! [A_80,B_81,C_82] :
      ( k9_subset_1(A_80,B_81,C_82) = k3_xboole_0(B_81,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [B_81] : k9_subset_1(u1_struct_0('#skF_3'),B_81,'#skF_5') = k3_xboole_0(B_81,'#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_148])).

tff(c_44,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3','#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_76,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_5'),u1_struct_0(k1_pre_topc('#skF_3','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_159,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),u1_struct_0(k1_pre_topc('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_76])).

tff(c_513,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_159])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n022.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 19:02:40 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.40  
% 2.44/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.44/1.41  
% 2.44/1.41  %Foreground sorts:
% 2.44/1.41  
% 2.44/1.41  
% 2.44/1.41  %Background operators:
% 2.44/1.41  
% 2.44/1.41  
% 2.44/1.41  %Foreground operators:
% 2.44/1.41  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.44/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.44/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.44/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.44/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.44/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.44/1.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.44/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.44/1.41  
% 2.44/1.42  tff(f_27, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.44/1.42  tff(f_29, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.44/1.42  tff(f_51, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.44/1.42  tff(f_57, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.44/1.42  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.44/1.42  tff(f_83, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_2)).
% 2.44/1.42  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.44/1.42  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.44/1.42  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.44/1.42  tff(c_2, plain, (![A_1, B_2]: (k1_enumset1(A_1, A_1, B_2)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.44/1.42  tff(c_101, plain, (![A_59, B_60, C_61]: (k2_enumset1(A_59, A_59, B_60, C_61)=k1_enumset1(A_59, B_60, C_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.44/1.42  tff(c_10, plain, (![F_16, A_9, B_10, C_11]: (r2_hidden(F_16, k2_enumset1(A_9, B_10, C_11, F_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.44/1.42  tff(c_122, plain, (![C_62, A_63, B_64]: (r2_hidden(C_62, k1_enumset1(A_63, B_64, C_62)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_10])).
% 2.44/1.42  tff(c_125, plain, (![B_2, A_1]: (r2_hidden(B_2, k2_tarski(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_122])).
% 2.44/1.42  tff(c_88, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.44/1.42  tff(c_46, plain, (![B_25, A_24]: (r1_tarski(k1_setfam_1(B_25), A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.44/1.42  tff(c_138, plain, (![A_75, B_76, A_77]: (r1_tarski(k3_xboole_0(A_75, B_76), A_77) | ~r2_hidden(A_77, k2_tarski(A_75, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_46])).
% 2.44/1.42  tff(c_146, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), B_2))), inference(resolution, [status(thm)], [c_125, c_138])).
% 2.44/1.42  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.44/1.42  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.44/1.42  tff(c_471, plain, (![A_110, B_111]: (u1_struct_0(k1_pre_topc(A_110, B_111))=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.44/1.42  tff(c_478, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))='#skF_5' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_471])).
% 2.44/1.42  tff(c_485, plain, (u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_478])).
% 2.44/1.42  tff(c_148, plain, (![A_80, B_81, C_82]: (k9_subset_1(A_80, B_81, C_82)=k3_xboole_0(B_81, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.44/1.42  tff(c_156, plain, (![B_81]: (k9_subset_1(u1_struct_0('#skF_3'), B_81, '#skF_5')=k3_xboole_0(B_81, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_148])).
% 2.44/1.42  tff(c_44, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.44/1.42  tff(c_50, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_3', '#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.44/1.42  tff(c_76, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_5'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_44, c_50])).
% 2.44/1.42  tff(c_159, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), u1_struct_0(k1_pre_topc('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_76])).
% 2.44/1.42  tff(c_513, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_485, c_159])).
% 2.44/1.42  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_146, c_513])).
% 2.44/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.42  
% 2.44/1.42  Inference rules
% 2.44/1.42  ----------------------
% 2.44/1.42  #Ref     : 0
% 2.44/1.42  #Sup     : 105
% 2.44/1.42  #Fact    : 0
% 2.44/1.42  #Define  : 0
% 2.44/1.42  #Split   : 0
% 2.44/1.42  #Chain   : 0
% 2.44/1.42  #Close   : 0
% 2.44/1.42  
% 2.44/1.42  Ordering : KBO
% 2.44/1.42  
% 2.44/1.42  Simplification rules
% 2.44/1.42  ----------------------
% 2.44/1.42  #Subsume      : 1
% 2.44/1.42  #Demod        : 32
% 2.44/1.42  #Tautology    : 52
% 2.44/1.42  #SimpNegUnit  : 0
% 2.44/1.42  #BackRed      : 4
% 2.44/1.42  
% 2.44/1.42  #Partial instantiations: 0
% 2.44/1.42  #Strategies tried      : 1
% 2.44/1.42  
% 2.44/1.42  Timing (in seconds)
% 2.44/1.42  ----------------------
% 2.44/1.42  Preprocessing        : 0.31
% 2.44/1.42  Parsing              : 0.15
% 2.44/1.42  CNF conversion       : 0.02
% 2.44/1.42  Main loop            : 0.25
% 2.44/1.42  Inferencing          : 0.09
% 2.44/1.42  Reduction            : 0.08
% 2.44/1.42  Demodulation         : 0.06
% 2.44/1.42  BG Simplification    : 0.02
% 2.44/1.42  Subsumption          : 0.04
% 2.44/1.42  Abstraction          : 0.02
% 2.44/1.42  MUC search           : 0.00
% 2.44/1.42  Cooper               : 0.00
% 2.44/1.42  Total                : 0.59
% 2.44/1.42  Index Insertion      : 0.00
% 2.44/1.42  Index Deletion       : 0.00
% 2.44/1.42  Index Matching       : 0.00
% 2.44/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
