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
% DateTime   : Thu Dec  3 10:23:06 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   44 (  57 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  79 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [A_29,B_30,C_31] :
      ( k9_subset_1(A_29,B_30,C_31) = k3_xboole_0(B_30,C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [B_34,B_35,A_36] :
      ( k9_subset_1(B_34,B_35,A_36) = k3_xboole_0(B_35,A_36)
      | ~ r1_tarski(A_36,B_34) ) ),
    inference(resolution,[status(thm)],[c_16,c_71])).

tff(c_116,plain,(
    ! [B_2,B_35] : k9_subset_1(B_2,B_35,B_2) = k3_xboole_0(B_35,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_126,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k9_subset_1(A_39,B_40,C_41),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_256,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(k9_subset_1(A_50,B_51,C_52),A_50)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_126,c_14])).

tff(c_276,plain,(
    ! [B_53,B_54] :
      ( r1_tarski(k3_xboole_0(B_53,B_54),B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(B_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_256])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_155,plain,(
    ! [A_43,B_44] :
      ( u1_struct_0(k1_pre_topc(A_43,B_44)) = B_44
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_169,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_155])).

tff(c_180,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_169])).

tff(c_79,plain,(
    ! [B_30] : k9_subset_1(u1_struct_0('#skF_1'),B_30,'#skF_3') = k3_xboole_0(B_30,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_20,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_55,plain,(
    ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_16,c_20])).

tff(c_104,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),u1_struct_0(k1_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_55])).

tff(c_184,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_104])).

tff(c_284,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_276,c_184])).

tff(c_289,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_284])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.35  
% 2.18/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.36  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.18/1.36  
% 2.18/1.36  %Foreground sorts:
% 2.18/1.36  
% 2.18/1.36  
% 2.18/1.36  %Background operators:
% 2.18/1.36  
% 2.18/1.36  
% 2.18/1.36  %Foreground operators:
% 2.18/1.36  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.18/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.36  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.18/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.18/1.36  
% 2.18/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.18/1.37  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.18/1.37  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.18/1.37  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 2.18/1.37  tff(f_63, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_tops_2)).
% 2.18/1.37  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.18/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.37  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.37  tff(c_71, plain, (![A_29, B_30, C_31]: (k9_subset_1(A_29, B_30, C_31)=k3_xboole_0(B_30, C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.37  tff(c_105, plain, (![B_34, B_35, A_36]: (k9_subset_1(B_34, B_35, A_36)=k3_xboole_0(B_35, A_36) | ~r1_tarski(A_36, B_34))), inference(resolution, [status(thm)], [c_16, c_71])).
% 2.18/1.37  tff(c_116, plain, (![B_2, B_35]: (k9_subset_1(B_2, B_35, B_2)=k3_xboole_0(B_35, B_2))), inference(resolution, [status(thm)], [c_6, c_105])).
% 2.18/1.37  tff(c_126, plain, (![A_39, B_40, C_41]: (m1_subset_1(k9_subset_1(A_39, B_40, C_41), k1_zfmisc_1(A_39)) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.37  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.37  tff(c_256, plain, (![A_50, B_51, C_52]: (r1_tarski(k9_subset_1(A_50, B_51, C_52), A_50) | ~m1_subset_1(C_52, k1_zfmisc_1(A_50)))), inference(resolution, [status(thm)], [c_126, c_14])).
% 2.18/1.37  tff(c_276, plain, (![B_53, B_54]: (r1_tarski(k3_xboole_0(B_53, B_54), B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(B_54)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_256])).
% 2.18/1.37  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.18/1.37  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.18/1.37  tff(c_155, plain, (![A_43, B_44]: (u1_struct_0(k1_pre_topc(A_43, B_44))=B_44 | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.18/1.37  tff(c_169, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_155])).
% 2.18/1.37  tff(c_180, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_169])).
% 2.18/1.37  tff(c_79, plain, (![B_30]: (k9_subset_1(u1_struct_0('#skF_1'), B_30, '#skF_3')=k3_xboole_0(B_30, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_71])).
% 2.18/1.37  tff(c_20, plain, (~m1_subset_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.18/1.37  tff(c_55, plain, (~r1_tarski(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_16, c_20])).
% 2.18/1.37  tff(c_104, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), u1_struct_0(k1_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_55])).
% 2.18/1.37  tff(c_184, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_104])).
% 2.18/1.37  tff(c_284, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_276, c_184])).
% 2.18/1.37  tff(c_289, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_284])).
% 2.18/1.37  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_289])).
% 2.18/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.37  
% 2.18/1.37  Inference rules
% 2.18/1.37  ----------------------
% 2.18/1.37  #Ref     : 0
% 2.18/1.37  #Sup     : 63
% 2.18/1.37  #Fact    : 0
% 2.18/1.37  #Define  : 0
% 2.18/1.37  #Split   : 2
% 2.18/1.37  #Chain   : 0
% 2.18/1.37  #Close   : 0
% 2.18/1.37  
% 2.18/1.37  Ordering : KBO
% 2.18/1.37  
% 2.18/1.37  Simplification rules
% 2.18/1.37  ----------------------
% 2.18/1.37  #Subsume      : 2
% 2.18/1.37  #Demod        : 19
% 2.18/1.37  #Tautology    : 23
% 2.18/1.37  #SimpNegUnit  : 0
% 2.18/1.37  #BackRed      : 3
% 2.18/1.37  
% 2.18/1.37  #Partial instantiations: 0
% 2.18/1.37  #Strategies tried      : 1
% 2.18/1.37  
% 2.18/1.37  Timing (in seconds)
% 2.18/1.37  ----------------------
% 2.18/1.37  Preprocessing        : 0.28
% 2.18/1.37  Parsing              : 0.15
% 2.18/1.37  CNF conversion       : 0.02
% 2.18/1.37  Main loop            : 0.27
% 2.18/1.37  Inferencing          : 0.09
% 2.18/1.37  Reduction            : 0.09
% 2.18/1.37  Demodulation         : 0.07
% 2.18/1.37  BG Simplification    : 0.01
% 2.18/1.37  Subsumption          : 0.05
% 2.18/1.37  Abstraction          : 0.02
% 2.18/1.37  MUC search           : 0.00
% 2.18/1.37  Cooper               : 0.00
% 2.18/1.37  Total                : 0.59
% 2.18/1.37  Index Insertion      : 0.00
% 2.18/1.37  Index Deletion       : 0.00
% 2.18/1.37  Index Matching       : 0.00
% 2.18/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
