%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:50 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.32s
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
%$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

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
               => ( v1_tops_2(B,A)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tops_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

tff(c_18,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    v1_tops_2('#skF_2','#skF_1') ),
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
      ( v1_tops_2(B_36,A_37)
      | ~ v1_tops_2(C_38,A_37)
      | ~ r1_tarski(B_36,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_178,plain,(
    ! [A_59,B_60,A_61] :
      ( v1_tops_2(k4_xboole_0(A_59,B_60),A_61)
      | ~ v1_tops_2(A_59,A_61)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ m1_subset_1(k4_xboole_0(A_59,B_60),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61))))
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_2,c_86])).

tff(c_196,plain,(
    ! [C_24] :
      ( v1_tops_2(k4_xboole_0('#skF_2',C_24),'#skF_1')
      | ~ v1_tops_2('#skF_2','#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_57,c_178])).

tff(c_214,plain,(
    ! [C_24] : v1_tops_2(k4_xboole_0('#skF_2',C_24),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_12,c_196])).

tff(c_10,plain,(
    ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    ~ v1_tops_2(k4_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:00 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.36  
% 2.13/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.36  %$ v1_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.36  
% 2.13/1.36  %Foreground sorts:
% 2.13/1.36  
% 2.13/1.36  
% 2.13/1.36  %Background operators:
% 2.13/1.36  
% 2.13/1.36  
% 2.13/1.36  %Foreground operators:
% 2.13/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.36  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.13/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.13/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.36  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.13/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.13/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.36  
% 2.32/1.37  tff(f_62, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tops_2)).
% 2.32/1.37  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.32/1.37  tff(f_31, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 2.32/1.37  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.32/1.37  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tops_2)).
% 2.32/1.37  tff(c_18, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.32/1.37  tff(c_16, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.32/1.37  tff(c_12, plain, (v1_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.32/1.37  tff(c_20, plain, (![A_22, B_23, C_24]: (k7_subset_1(A_22, B_23, C_24)=k4_xboole_0(B_23, C_24) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.37  tff(c_26, plain, (![C_24]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_24)=k4_xboole_0('#skF_2', C_24))), inference(resolution, [status(thm)], [c_16, c_20])).
% 2.32/1.37  tff(c_46, plain, (![A_27, B_28, C_29]: (m1_subset_1(k7_subset_1(A_27, B_28, C_29), k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.32/1.37  tff(c_51, plain, (![C_24]: (m1_subset_1(k4_xboole_0('#skF_2', C_24), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_46])).
% 2.32/1.37  tff(c_57, plain, (![C_24]: (m1_subset_1(k4_xboole_0('#skF_2', C_24), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_51])).
% 2.32/1.37  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.32/1.37  tff(c_86, plain, (![B_36, A_37, C_38]: (v1_tops_2(B_36, A_37) | ~v1_tops_2(C_38, A_37) | ~r1_tarski(B_36, C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.32/1.37  tff(c_178, plain, (![A_59, B_60, A_61]: (v1_tops_2(k4_xboole_0(A_59, B_60), A_61) | ~v1_tops_2(A_59, A_61) | ~m1_subset_1(A_59, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~m1_subset_1(k4_xboole_0(A_59, B_60), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_61)))) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_2, c_86])).
% 2.32/1.37  tff(c_196, plain, (![C_24]: (v1_tops_2(k4_xboole_0('#skF_2', C_24), '#skF_1') | ~v1_tops_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_57, c_178])).
% 2.32/1.37  tff(c_214, plain, (![C_24]: (v1_tops_2(k4_xboole_0('#skF_2', C_24), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_12, c_196])).
% 2.32/1.37  tff(c_10, plain, (~v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.32/1.37  tff(c_36, plain, (~v1_tops_2(k4_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 2.32/1.37  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_36])).
% 2.32/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.37  
% 2.32/1.37  Inference rules
% 2.32/1.37  ----------------------
% 2.32/1.37  #Ref     : 0
% 2.32/1.37  #Sup     : 43
% 2.32/1.37  #Fact    : 0
% 2.32/1.37  #Define  : 0
% 2.32/1.37  #Split   : 0
% 2.32/1.37  #Chain   : 0
% 2.32/1.37  #Close   : 0
% 2.32/1.37  
% 2.32/1.37  Ordering : KBO
% 2.32/1.37  
% 2.32/1.37  Simplification rules
% 2.32/1.37  ----------------------
% 2.32/1.37  #Subsume      : 0
% 2.32/1.37  #Demod        : 33
% 2.32/1.37  #Tautology    : 16
% 2.32/1.37  #SimpNegUnit  : 0
% 2.32/1.37  #BackRed      : 2
% 2.32/1.37  
% 2.32/1.37  #Partial instantiations: 0
% 2.32/1.37  #Strategies tried      : 1
% 2.32/1.37  
% 2.32/1.37  Timing (in seconds)
% 2.32/1.37  ----------------------
% 2.32/1.38  Preprocessing        : 0.34
% 2.32/1.38  Parsing              : 0.17
% 2.32/1.38  CNF conversion       : 0.02
% 2.32/1.38  Main loop            : 0.21
% 2.32/1.38  Inferencing          : 0.08
% 2.32/1.38  Reduction            : 0.07
% 2.32/1.38  Demodulation         : 0.06
% 2.32/1.38  BG Simplification    : 0.01
% 2.32/1.38  Subsumption          : 0.03
% 2.32/1.38  Abstraction          : 0.02
% 2.32/1.38  MUC search           : 0.00
% 2.32/1.38  Cooper               : 0.00
% 2.32/1.38  Total                : 0.57
% 2.32/1.38  Index Insertion      : 0.00
% 2.32/1.38  Index Deletion       : 0.00
% 2.32/1.38  Index Matching       : 0.00
% 2.32/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
