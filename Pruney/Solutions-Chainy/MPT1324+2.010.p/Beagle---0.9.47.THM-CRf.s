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
% DateTime   : Thu Dec  3 10:23:08 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  60 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( r1_tarski(B,k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)))
                 => r1_tarski(B,k5_setfam_1(u1_struct_0(A),C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A,B)),k1_tops_2(A,B,C)),k5_setfam_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_8,plain,(
    ~ r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1','#skF_2')),k1_tops_2('#skF_1','#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    ! [A_30,B_31,C_32] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_30,B_31)),k1_tops_2(A_30,B_31,C_32)),k5_setfam_1(u1_struct_0(A_30),C_32))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30))))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_20,C_3,B_21] :
      ( r1_tarski(A_20,C_3)
      | ~ r1_tarski(B_21,C_3)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2])).

tff(c_61,plain,(
    ! [A_33,A_34,C_35,B_36] :
      ( r1_tarski(A_33,k5_setfam_1(u1_struct_0(A_34),C_35))
      | ~ r1_tarski(A_33,k5_setfam_1(u1_struct_0(k1_pre_topc(A_34,B_36)),k1_tops_2(A_34,B_36,C_35)))
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34))))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_54,c_24])).

tff(c_71,plain,
    ( r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_61])).

tff(c_78,plain,(
    r1_tarski('#skF_2',k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_71])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:21:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.18  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k1_tops_2 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.72/1.18  
% 1.72/1.18  %Foreground sorts:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Background operators:
% 1.72/1.18  
% 1.72/1.18  
% 1.72/1.18  %Foreground operators:
% 1.72/1.18  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.72/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.18  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.72/1.18  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.72/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.18  
% 1.96/1.19  tff(f_56, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C))) => r1_tarski(B, k5_setfam_1(u1_struct_0(A), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_tops_2)).
% 1.96/1.19  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A, B)), k1_tops_2(A, B, C)), k5_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_2)).
% 1.96/1.19  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.96/1.19  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.96/1.19  tff(c_8, plain, (~r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.19  tff(c_16, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.19  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.19  tff(c_12, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.19  tff(c_10, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0(k1_pre_topc('#skF_1', '#skF_2')), k1_tops_2('#skF_1', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.19  tff(c_54, plain, (![A_30, B_31, C_32]: (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(A_30, B_31)), k1_tops_2(A_30, B_31, C_32)), k5_setfam_1(u1_struct_0(A_30), C_32)) | ~m1_subset_1(C_32, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_30)))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.19  tff(c_18, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.19  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.19  tff(c_24, plain, (![A_20, C_3, B_21]: (r1_tarski(A_20, C_3) | ~r1_tarski(B_21, C_3) | ~r1_tarski(A_20, B_21))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2])).
% 1.96/1.19  tff(c_61, plain, (![A_33, A_34, C_35, B_36]: (r1_tarski(A_33, k5_setfam_1(u1_struct_0(A_34), C_35)) | ~r1_tarski(A_33, k5_setfam_1(u1_struct_0(k1_pre_topc(A_34, B_36)), k1_tops_2(A_34, B_36, C_35))) | ~m1_subset_1(C_35, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_34)))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_54, c_24])).
% 1.96/1.19  tff(c_71, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_10, c_61])).
% 1.96/1.19  tff(c_78, plain, (r1_tarski('#skF_2', k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_12, c_71])).
% 1.96/1.19  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_78])).
% 1.96/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.19  
% 1.96/1.19  Inference rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Ref     : 0
% 1.96/1.19  #Sup     : 14
% 1.96/1.19  #Fact    : 0
% 1.96/1.19  #Define  : 0
% 1.96/1.19  #Split   : 0
% 1.96/1.19  #Chain   : 0
% 1.96/1.19  #Close   : 0
% 1.96/1.19  
% 1.96/1.19  Ordering : KBO
% 1.96/1.19  
% 1.96/1.19  Simplification rules
% 1.96/1.19  ----------------------
% 1.96/1.19  #Subsume      : 2
% 1.96/1.19  #Demod        : 7
% 1.96/1.19  #Tautology    : 3
% 1.96/1.19  #SimpNegUnit  : 1
% 1.96/1.19  #BackRed      : 0
% 1.96/1.19  
% 1.96/1.19  #Partial instantiations: 0
% 1.96/1.19  #Strategies tried      : 1
% 1.96/1.19  
% 1.96/1.19  Timing (in seconds)
% 1.96/1.19  ----------------------
% 1.96/1.19  Preprocessing        : 0.28
% 1.96/1.19  Parsing              : 0.16
% 1.96/1.19  CNF conversion       : 0.02
% 1.96/1.19  Main loop            : 0.13
% 1.96/1.19  Inferencing          : 0.05
% 1.96/1.19  Reduction            : 0.04
% 1.96/1.19  Demodulation         : 0.03
% 1.96/1.19  BG Simplification    : 0.01
% 1.96/1.19  Subsumption          : 0.03
% 1.96/1.19  Abstraction          : 0.01
% 1.96/1.19  MUC search           : 0.00
% 1.96/1.19  Cooper               : 0.00
% 1.96/1.19  Total                : 0.44
% 1.96/1.19  Index Insertion      : 0.00
% 1.96/1.19  Index Deletion       : 0.00
% 1.96/1.19  Index Matching       : 0.00
% 1.96/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
