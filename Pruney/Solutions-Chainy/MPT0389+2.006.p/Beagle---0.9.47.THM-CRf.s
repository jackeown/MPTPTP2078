%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:13 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  74 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ( A = k1_xboole_0
          | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(B,C) )
     => ( A = k1_xboole_0
        | r1_tarski(B,k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(c_16,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_1'(A_10,B_11),A_10)
      | r1_tarski(B_11,k1_setfam_1(A_10))
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_tarski(A_6),B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_27,plain,(
    ! [A_17,B_18] :
      ( k2_xboole_0(A_17,B_18) = B_18
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(k1_tarski(A_26),B_27) = B_27
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(resolution,[status(thm)],[c_8,c_27])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(k1_tarski(A_30),C_31)
      | ~ r1_tarski(B_32,C_31)
      | ~ r2_hidden(A_30,B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_2])).

tff(c_97,plain,(
    ! [A_35] :
      ( r1_tarski(k1_tarski(A_35),'#skF_3')
      | ~ r2_hidden(A_35,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_83])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | ~ r1_tarski(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [A_36] :
      ( r2_hidden(A_36,'#skF_3')
      | ~ r2_hidden(A_36,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_97,c_6])).

tff(c_113,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_1'('#skF_2',B_11),'#skF_3')
      | r1_tarski(B_11,k1_setfam_1('#skF_2'))
      | k1_xboole_0 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_14,c_109])).

tff(c_116,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_1'('#skF_2',B_11),'#skF_3')
      | r1_tarski(B_11,k1_setfam_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_113])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_setfam_1(B_9),A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_203,plain,(
    ! [B_46,A_47] :
      ( ~ r1_tarski(B_46,'#skF_1'(A_47,B_46))
      | r1_tarski(B_46,k1_setfam_1(A_47))
      | k1_xboole_0 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_375,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(k1_setfam_1(B_81),k1_setfam_1(A_82))
      | k1_xboole_0 = A_82
      | ~ r2_hidden('#skF_1'(A_82,k1_setfam_1(B_81)),B_81) ) ),
    inference(resolution,[status(thm)],[c_10,c_203])).

tff(c_383,plain,
    ( k1_xboole_0 = '#skF_2'
    | r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_116,c_375])).

tff(c_394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_18,c_16,c_383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.30  % Computer   : n019.cluster.edu
% 0.12/0.30  % Model      : x86_64 x86_64
% 0.12/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.30  % Memory     : 8042.1875MB
% 0.12/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.30  % CPULimit   : 60
% 0.12/0.30  % DateTime   : Tue Dec  1 18:08:52 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.35  
% 2.41/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.36  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.41/1.36  
% 2.41/1.36  %Foreground sorts:
% 2.41/1.36  
% 2.41/1.36  
% 2.41/1.36  %Background operators:
% 2.41/1.36  
% 2.41/1.36  
% 2.41/1.36  %Foreground operators:
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.41/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.41/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.41/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.41/1.36  
% 2.41/1.37  tff(f_57, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.41/1.37  tff(f_50, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(B, C))) => ((A = k1_xboole_0) | r1_tarski(B, k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 2.41/1.37  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.41/1.37  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.41/1.37  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.41/1.37  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.41/1.37  tff(c_16, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.41/1.37  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.41/1.37  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_1'(A_10, B_11), A_10) | r1_tarski(B_11, k1_setfam_1(A_10)) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.37  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.41/1.37  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k1_tarski(A_6), B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.41/1.37  tff(c_27, plain, (![A_17, B_18]: (k2_xboole_0(A_17, B_18)=B_18 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.37  tff(c_59, plain, (![A_26, B_27]: (k2_xboole_0(k1_tarski(A_26), B_27)=B_27 | ~r2_hidden(A_26, B_27))), inference(resolution, [status(thm)], [c_8, c_27])).
% 2.41/1.37  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.37  tff(c_83, plain, (![A_30, C_31, B_32]: (r1_tarski(k1_tarski(A_30), C_31) | ~r1_tarski(B_32, C_31) | ~r2_hidden(A_30, B_32))), inference(superposition, [status(thm), theory('equality')], [c_59, c_2])).
% 2.41/1.37  tff(c_97, plain, (![A_35]: (r1_tarski(k1_tarski(A_35), '#skF_3') | ~r2_hidden(A_35, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_83])).
% 2.41/1.37  tff(c_6, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | ~r1_tarski(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.41/1.37  tff(c_109, plain, (![A_36]: (r2_hidden(A_36, '#skF_3') | ~r2_hidden(A_36, '#skF_2'))), inference(resolution, [status(thm)], [c_97, c_6])).
% 2.41/1.37  tff(c_113, plain, (![B_11]: (r2_hidden('#skF_1'('#skF_2', B_11), '#skF_3') | r1_tarski(B_11, k1_setfam_1('#skF_2')) | k1_xboole_0='#skF_2')), inference(resolution, [status(thm)], [c_14, c_109])).
% 2.41/1.37  tff(c_116, plain, (![B_11]: (r2_hidden('#skF_1'('#skF_2', B_11), '#skF_3') | r1_tarski(B_11, k1_setfam_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_18, c_113])).
% 2.41/1.37  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_setfam_1(B_9), A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.41/1.37  tff(c_203, plain, (![B_46, A_47]: (~r1_tarski(B_46, '#skF_1'(A_47, B_46)) | r1_tarski(B_46, k1_setfam_1(A_47)) | k1_xboole_0=A_47)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.37  tff(c_375, plain, (![B_81, A_82]: (r1_tarski(k1_setfam_1(B_81), k1_setfam_1(A_82)) | k1_xboole_0=A_82 | ~r2_hidden('#skF_1'(A_82, k1_setfam_1(B_81)), B_81))), inference(resolution, [status(thm)], [c_10, c_203])).
% 2.41/1.37  tff(c_383, plain, (k1_xboole_0='#skF_2' | r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(resolution, [status(thm)], [c_116, c_375])).
% 2.41/1.37  tff(c_394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_18, c_16, c_383])).
% 2.41/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.37  
% 2.41/1.37  Inference rules
% 2.41/1.37  ----------------------
% 2.41/1.37  #Ref     : 0
% 2.41/1.37  #Sup     : 86
% 2.41/1.37  #Fact    : 0
% 2.41/1.37  #Define  : 0
% 2.41/1.37  #Split   : 1
% 2.41/1.37  #Chain   : 0
% 2.41/1.37  #Close   : 0
% 2.41/1.37  
% 2.41/1.37  Ordering : KBO
% 2.41/1.37  
% 2.41/1.37  Simplification rules
% 2.41/1.37  ----------------------
% 2.41/1.37  #Subsume      : 4
% 2.41/1.37  #Demod        : 0
% 2.41/1.37  #Tautology    : 27
% 2.41/1.37  #SimpNegUnit  : 4
% 2.41/1.37  #BackRed      : 0
% 2.41/1.37  
% 2.41/1.37  #Partial instantiations: 0
% 2.41/1.37  #Strategies tried      : 1
% 2.41/1.37  
% 2.41/1.37  Timing (in seconds)
% 2.41/1.37  ----------------------
% 2.41/1.37  Preprocessing        : 0.31
% 2.41/1.37  Parsing              : 0.17
% 2.41/1.37  CNF conversion       : 0.02
% 2.41/1.37  Main loop            : 0.30
% 2.41/1.37  Inferencing          : 0.12
% 2.41/1.37  Reduction            : 0.07
% 2.41/1.37  Demodulation         : 0.04
% 2.41/1.37  BG Simplification    : 0.02
% 2.41/1.37  Subsumption          : 0.08
% 2.41/1.37  Abstraction          : 0.01
% 2.41/1.37  MUC search           : 0.00
% 2.41/1.37  Cooper               : 0.00
% 2.41/1.37  Total                : 0.64
% 2.41/1.37  Index Insertion      : 0.00
% 2.41/1.37  Index Deletion       : 0.00
% 2.41/1.37  Index Matching       : 0.00
% 2.41/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
