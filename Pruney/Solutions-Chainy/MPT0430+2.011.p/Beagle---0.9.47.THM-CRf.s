%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:12 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   42 (  59 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 117 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ( v3_setfam_1(B,A)
                & r1_tarski(C,B) )
             => v3_setfam_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ~ v3_setfam_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_101,plain,(
    ! [B_33,A_34] :
      ( v3_setfam_1(B_33,A_34)
      | r2_hidden(A_34,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_111,plain,
    ( v3_setfam_1('#skF_3','#skF_1')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_117,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_111])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,(
    ! [C_20,B_21,A_22] :
      ( ~ v1_xboole_0(C_20)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(C_20))
      | ~ r2_hidden(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_47,plain,(
    ! [B_6,A_22,A_5] :
      ( ~ v1_xboole_0(B_6)
      | ~ r2_hidden(A_22,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_40])).

tff(c_125,plain,(
    ! [B_35] :
      ( ~ v1_xboole_0(B_35)
      | ~ r1_tarski('#skF_3',B_35) ) ),
    inference(resolution,[status(thm)],[c_117,c_47])).

tff(c_133,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_125])).

tff(c_55,plain,(
    ! [A_26,C_27,B_28] :
      ( m1_subset_1(A_26,C_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(C_27))
      | ~ r2_hidden(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_141,plain,(
    ! [A_37,B_38,A_39] :
      ( m1_subset_1(A_37,B_38)
      | ~ r2_hidden(A_37,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_148,plain,(
    ! [B_40] :
      ( m1_subset_1('#skF_1',B_40)
      | ~ r1_tarski('#skF_3',B_40) ) ),
    inference(resolution,[status(thm)],[c_117,c_141])).

tff(c_161,plain,(
    m1_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_148])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    v3_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_173,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden(A_41,B_42)
      | ~ v3_setfam_1(B_42,A_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_180,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | ~ v3_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_173])).

tff(c_187,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_180])).

tff(c_193,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_196,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_193])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.27  
% 2.02/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.27  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.27  
% 2.02/1.27  %Foreground sorts:
% 2.02/1.27  
% 2.02/1.27  
% 2.02/1.27  %Background operators:
% 2.02/1.27  
% 2.02/1.27  
% 2.02/1.27  %Foreground operators:
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.27  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 2.02/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.27  
% 2.02/1.28  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_setfam_1)).
% 2.02/1.28  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 2.02/1.28  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.02/1.28  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.02/1.28  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.02/1.28  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.02/1.28  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.28  tff(c_16, plain, (~v3_setfam_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.28  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.28  tff(c_101, plain, (![B_33, A_34]: (v3_setfam_1(B_33, A_34) | r2_hidden(A_34, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.28  tff(c_111, plain, (v3_setfam_1('#skF_3', '#skF_1') | r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_101])).
% 2.02/1.28  tff(c_117, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_16, c_111])).
% 2.02/1.28  tff(c_10, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.02/1.28  tff(c_40, plain, (![C_20, B_21, A_22]: (~v1_xboole_0(C_20) | ~m1_subset_1(B_21, k1_zfmisc_1(C_20)) | ~r2_hidden(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.02/1.28  tff(c_47, plain, (![B_6, A_22, A_5]: (~v1_xboole_0(B_6) | ~r2_hidden(A_22, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_10, c_40])).
% 2.02/1.28  tff(c_125, plain, (![B_35]: (~v1_xboole_0(B_35) | ~r1_tarski('#skF_3', B_35))), inference(resolution, [status(thm)], [c_117, c_47])).
% 2.02/1.28  tff(c_133, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_125])).
% 2.02/1.28  tff(c_55, plain, (![A_26, C_27, B_28]: (m1_subset_1(A_26, C_27) | ~m1_subset_1(B_28, k1_zfmisc_1(C_27)) | ~r2_hidden(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.02/1.28  tff(c_141, plain, (![A_37, B_38, A_39]: (m1_subset_1(A_37, B_38) | ~r2_hidden(A_37, A_39) | ~r1_tarski(A_39, B_38))), inference(resolution, [status(thm)], [c_10, c_55])).
% 2.02/1.28  tff(c_148, plain, (![B_40]: (m1_subset_1('#skF_1', B_40) | ~r1_tarski('#skF_3', B_40))), inference(resolution, [status(thm)], [c_117, c_141])).
% 2.02/1.28  tff(c_161, plain, (m1_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_148])).
% 2.02/1.28  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.02/1.28  tff(c_20, plain, (v3_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.28  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.28  tff(c_173, plain, (![A_41, B_42]: (~r2_hidden(A_41, B_42) | ~v3_setfam_1(B_42, A_41) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.28  tff(c_180, plain, (~r2_hidden('#skF_1', '#skF_2') | ~v3_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_173])).
% 2.02/1.28  tff(c_187, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_180])).
% 2.02/1.28  tff(c_193, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_187])).
% 2.02/1.28  tff(c_196, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_193])).
% 2.02/1.28  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_196])).
% 2.02/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.28  
% 2.02/1.28  Inference rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Ref     : 0
% 2.02/1.28  #Sup     : 38
% 2.02/1.28  #Fact    : 0
% 2.02/1.28  #Define  : 0
% 2.02/1.28  #Split   : 3
% 2.02/1.28  #Chain   : 0
% 2.02/1.28  #Close   : 0
% 2.02/1.28  
% 2.02/1.28  Ordering : KBO
% 2.02/1.28  
% 2.02/1.28  Simplification rules
% 2.02/1.28  ----------------------
% 2.02/1.28  #Subsume      : 6
% 2.02/1.28  #Demod        : 5
% 2.02/1.28  #Tautology    : 3
% 2.02/1.28  #SimpNegUnit  : 3
% 2.02/1.28  #BackRed      : 0
% 2.02/1.28  
% 2.02/1.28  #Partial instantiations: 0
% 2.02/1.28  #Strategies tried      : 1
% 2.02/1.28  
% 2.02/1.28  Timing (in seconds)
% 2.02/1.28  ----------------------
% 2.02/1.29  Preprocessing        : 0.29
% 2.02/1.29  Parsing              : 0.17
% 2.02/1.29  CNF conversion       : 0.02
% 2.02/1.29  Main loop            : 0.19
% 2.02/1.29  Inferencing          : 0.08
% 2.02/1.29  Reduction            : 0.05
% 2.02/1.29  Demodulation         : 0.03
% 2.02/1.29  BG Simplification    : 0.01
% 2.02/1.29  Subsumption          : 0.03
% 2.02/1.29  Abstraction          : 0.01
% 2.02/1.29  MUC search           : 0.00
% 2.02/1.29  Cooper               : 0.00
% 2.02/1.29  Total                : 0.51
% 2.02/1.29  Index Insertion      : 0.00
% 2.02/1.29  Index Deletion       : 0.00
% 2.02/1.29  Index Matching       : 0.00
% 2.02/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
