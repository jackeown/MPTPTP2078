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
% DateTime   : Thu Dec  3 10:22:55 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  85 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tops_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_22,B_23,C_24] :
      ( k7_subset_1(A_22,B_23,C_24) = k4_xboole_0(B_23,C_24)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [C_24] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_24) = k4_xboole_0('#skF_2',C_24) ),
    inference(resolution,[status(thm)],[c_16,c_20])).

tff(c_46,plain,(
    ! [A_27,B_28,C_29] :
      ( m1_subset_1(k7_subset_1(A_27,B_28,C_29),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [C_24] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_46])).

tff(c_57,plain,(
    ! [C_24] : m1_subset_1(k4_xboole_0('#skF_2',C_24),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_51])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [B_36,A_37,C_38] :
      ( v2_tops_2(B_36,A_37)
      | ~ v2_tops_2(C_38,A_37)
      | ~ r1_tarski(B_36,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_178,plain,(
    ! [A_59,B_60,A_61] :
      ( v2_tops_2(k4_xboole_0(A_59,B_60),A_61)
      | ~ v2_tops_2(A_59,A_61)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ m1_subset_1(k4_xboole_0(A_59,B_60),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_2,c_86])).

tff(c_196,plain,(
    ! [C_24] :
      ( v2_tops_2(k4_xboole_0('#skF_2',C_24),'#skF_1')
      | ~ v2_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_57,c_178])).

tff(c_214,plain,(
    ! [C_24] : v2_tops_2(k4_xboole_0('#skF_2',C_24),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_12,c_196])).

tff(c_10,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ~ v2_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:10:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.20  
% 2.02/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.21  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.21  
% 2.02/1.21  %Foreground sorts:
% 2.02/1.21  
% 2.02/1.21  
% 2.02/1.21  %Background operators:
% 2.02/1.21  
% 2.02/1.21  
% 2.02/1.21  %Foreground operators:
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.02/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.21  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.02/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.21  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.02/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.21  
% 2.02/1.21  tff(f_62, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tops_2)).
% 2.02/1.21  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.02/1.21  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 2.02/1.21  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.02/1.21  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 2.02/1.21  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.21  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.21  tff(c_12, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.21  tff(c_20, plain, (![A_22, B_23, C_24]: (k7_subset_1(A_22, B_23, C_24)=k4_xboole_0(B_23, C_24) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.21  tff(c_26, plain, (![C_24]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_24)=k4_xboole_0('#skF_2', C_24))), inference(resolution, [status(thm)], [c_16, c_20])).
% 2.02/1.21  tff(c_46, plain, (![A_27, B_28, C_29]: (m1_subset_1(k7_subset_1(A_27, B_28, C_29), k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.21  tff(c_51, plain, (![C_24]: (m1_subset_1(k4_xboole_0('#skF_2', C_24), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_46])).
% 2.02/1.21  tff(c_57, plain, (![C_24]: (m1_subset_1(k4_xboole_0('#skF_2', C_24), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_51])).
% 2.02/1.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.21  tff(c_86, plain, (![B_36, A_37, C_38]: (v2_tops_2(B_36, A_37) | ~v2_tops_2(C_38, A_37) | ~r1_tarski(B_36, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.21  tff(c_178, plain, (![A_59, B_60, A_61]: (v2_tops_2(k4_xboole_0(A_59, B_60), A_61) | ~v2_tops_2(A_59, A_61) | ~m1_subset_1(A_59, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~m1_subset_1(k4_xboole_0(A_59, B_60), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_2, c_86])).
% 2.02/1.21  tff(c_196, plain, (![C_24]: (v2_tops_2(k4_xboole_0('#skF_2', C_24), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_57, c_178])).
% 2.02/1.21  tff(c_214, plain, (![C_24]: (v2_tops_2(k4_xboole_0('#skF_2', C_24), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_12, c_196])).
% 2.02/1.21  tff(c_10, plain, (~v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.02/1.21  tff(c_36, plain, (~v2_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 2.02/1.21  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_36])).
% 2.02/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.21  
% 2.02/1.21  Inference rules
% 2.02/1.21  ----------------------
% 2.02/1.21  #Ref     : 0
% 2.02/1.21  #Sup     : 43
% 2.02/1.22  #Fact    : 0
% 2.02/1.22  #Define  : 0
% 2.02/1.22  #Split   : 0
% 2.02/1.22  #Chain   : 0
% 2.02/1.22  #Close   : 0
% 2.02/1.22  
% 2.02/1.22  Ordering : KBO
% 2.02/1.22  
% 2.02/1.22  Simplification rules
% 2.02/1.22  ----------------------
% 2.02/1.22  #Subsume      : 0
% 2.02/1.22  #Demod        : 33
% 2.02/1.22  #Tautology    : 16
% 2.02/1.22  #SimpNegUnit  : 0
% 2.02/1.22  #BackRed      : 2
% 2.02/1.22  
% 2.02/1.22  #Partial instantiations: 0
% 2.02/1.22  #Strategies tried      : 1
% 2.02/1.22  
% 2.02/1.22  Timing (in seconds)
% 2.02/1.22  ----------------------
% 2.02/1.22  Preprocessing        : 0.28
% 2.02/1.22  Parsing              : 0.15
% 2.02/1.22  CNF conversion       : 0.02
% 2.02/1.22  Main loop            : 0.19
% 2.02/1.22  Inferencing          : 0.07
% 2.02/1.22  Reduction            : 0.07
% 2.02/1.22  Demodulation         : 0.05
% 2.02/1.22  BG Simplification    : 0.01
% 2.02/1.22  Subsumption          : 0.02
% 2.02/1.22  Abstraction          : 0.02
% 2.02/1.22  MUC search           : 0.00
% 2.02/1.22  Cooper               : 0.00
% 2.02/1.22  Total                : 0.49
% 2.02/1.22  Index Insertion      : 0.00
% 2.02/1.22  Index Deletion       : 0.00
% 2.02/1.22  Index Matching       : 0.00
% 2.02/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
