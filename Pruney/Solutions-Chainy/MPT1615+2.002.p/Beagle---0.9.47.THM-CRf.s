%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:34 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   40 (  52 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  82 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_pre_topc > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_22,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_8] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_8))
      | ~ l1_pre_topc(A_8)
      | ~ v2_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_41,plain,(
    ! [A_18] :
      ( k3_yellow_0(k2_yellow_1(A_18)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1'))
    | v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_18])).

tff(c_54,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_57,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_54])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_57])).

tff(c_62,plain,(
    v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    r2_hidden(k1_xboole_0,u1_pre_topc('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [C_19,B_20,A_21] :
      ( ~ v1_xboole_0(C_19)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(C_19))
      | ~ r2_hidden(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [B_22,A_23,A_24] :
      ( ~ v1_xboole_0(B_22)
      | ~ r2_hidden(A_23,A_24)
      | ~ r1_tarski(A_24,B_22) ) ),
    inference(resolution,[status(thm)],[c_10,c_64])).

tff(c_75,plain,(
    ! [B_25] :
      ( ~ v1_xboole_0(B_25)
      | ~ r1_tarski(u1_pre_topc('#skF_1'),B_25) ) ),
    inference(resolution,[status(thm)],[c_63,c_68])).

tff(c_79,plain,(
    ~ v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_83,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:30:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  
% 1.63/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.14  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > #nlpp > u1_pre_topc > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1
% 1.63/1.14  
% 1.63/1.14  %Foreground sorts:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Background operators:
% 1.63/1.14  
% 1.63/1.14  
% 1.63/1.14  %Foreground operators:
% 1.63/1.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.63/1.14  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.14  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.63/1.14  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.63/1.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.63/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.63/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.63/1.14  
% 1.63/1.16  tff(f_65, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_1)).
% 1.63/1.16  tff(f_48, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => r2_hidden(k1_xboole_0, u1_pre_topc(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_pre_topc)).
% 1.63/1.16  tff(f_55, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.63/1.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.63/1.16  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.63/1.16  tff(f_42, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 1.63/1.16  tff(c_22, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.63/1.16  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.63/1.16  tff(c_14, plain, (![A_8]: (r2_hidden(k1_xboole_0, u1_pre_topc(A_8)) | ~l1_pre_topc(A_8) | ~v2_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.63/1.16  tff(c_41, plain, (![A_18]: (k3_yellow_0(k2_yellow_1(A_18))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.63/1.16  tff(c_18, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_1')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.63/1.16  tff(c_52, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1')) | v1_xboole_0(u1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_41, c_18])).
% 1.63/1.16  tff(c_54, plain, (~r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 1.63/1.16  tff(c_57, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_54])).
% 1.63/1.16  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_57])).
% 1.63/1.16  tff(c_62, plain, (v1_xboole_0(u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_52])).
% 1.63/1.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.16  tff(c_63, plain, (r2_hidden(k1_xboole_0, u1_pre_topc('#skF_1'))), inference(splitRight, [status(thm)], [c_52])).
% 1.63/1.16  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.16  tff(c_64, plain, (![C_19, B_20, A_21]: (~v1_xboole_0(C_19) | ~m1_subset_1(B_20, k1_zfmisc_1(C_19)) | ~r2_hidden(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.63/1.16  tff(c_68, plain, (![B_22, A_23, A_24]: (~v1_xboole_0(B_22) | ~r2_hidden(A_23, A_24) | ~r1_tarski(A_24, B_22))), inference(resolution, [status(thm)], [c_10, c_64])).
% 1.63/1.16  tff(c_75, plain, (![B_25]: (~v1_xboole_0(B_25) | ~r1_tarski(u1_pre_topc('#skF_1'), B_25))), inference(resolution, [status(thm)], [c_63, c_68])).
% 1.63/1.16  tff(c_79, plain, (~v1_xboole_0(u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_75])).
% 1.63/1.16  tff(c_83, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_79])).
% 1.63/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.16  
% 1.63/1.16  Inference rules
% 1.63/1.16  ----------------------
% 1.63/1.16  #Ref     : 0
% 1.63/1.16  #Sup     : 10
% 1.63/1.16  #Fact    : 0
% 1.63/1.16  #Define  : 0
% 1.63/1.16  #Split   : 1
% 1.63/1.16  #Chain   : 0
% 1.63/1.16  #Close   : 0
% 1.63/1.16  
% 1.63/1.16  Ordering : KBO
% 1.63/1.16  
% 1.63/1.16  Simplification rules
% 1.63/1.16  ----------------------
% 1.63/1.16  #Subsume      : 0
% 1.63/1.16  #Demod        : 5
% 1.63/1.16  #Tautology    : 5
% 1.63/1.16  #SimpNegUnit  : 0
% 1.63/1.16  #BackRed      : 0
% 1.63/1.16  
% 1.63/1.16  #Partial instantiations: 0
% 1.63/1.16  #Strategies tried      : 1
% 1.63/1.16  
% 1.63/1.16  Timing (in seconds)
% 1.63/1.16  ----------------------
% 1.63/1.16  Preprocessing        : 0.26
% 1.63/1.16  Parsing              : 0.14
% 1.63/1.16  CNF conversion       : 0.02
% 1.63/1.16  Main loop            : 0.11
% 1.63/1.16  Inferencing          : 0.05
% 1.63/1.16  Reduction            : 0.03
% 1.63/1.16  Demodulation         : 0.02
% 1.63/1.16  BG Simplification    : 0.01
% 1.63/1.16  Subsumption          : 0.02
% 1.63/1.16  Abstraction          : 0.00
% 1.63/1.16  MUC search           : 0.00
% 1.63/1.16  Cooper               : 0.00
% 1.63/1.16  Total                : 0.39
% 1.63/1.16  Index Insertion      : 0.00
% 1.63/1.16  Index Deletion       : 0.00
% 1.63/1.16  Index Matching       : 0.00
% 1.63/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
