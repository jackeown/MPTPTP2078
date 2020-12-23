%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:42 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  44 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k6_subset_1 > k4_xboole_0 > k4_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k4_setfam_1,type,(
    k4_setfam_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k4_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k6_subset_1(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(k4_setfam_1(A,A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_setfam_1)).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_setfam_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_17,B_18,D_44] :
      ( r2_hidden('#skF_7'(A_17,B_18,k4_setfam_1(A_17,B_18),D_44),A_17)
      | ~ r2_hidden(D_44,k4_setfam_1(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_17,B_18,D_44] :
      ( k6_subset_1('#skF_7'(A_17,B_18,k4_setfam_1(A_17,B_18),D_44),'#skF_8'(A_17,B_18,k4_setfam_1(A_17,B_18),D_44)) = D_44
      | ~ r2_hidden(D_44,k4_setfam_1(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_82,plain,(
    ! [A_92,B_93,D_94] :
      ( k4_xboole_0('#skF_7'(A_92,B_93,k4_setfam_1(A_92,B_93),D_94),'#skF_8'(A_92,B_93,k4_setfam_1(A_92,B_93),D_94)) = D_94
      | ~ r2_hidden(D_94,k4_setfam_1(A_92,B_93)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_97,plain,(
    ! [D_95,A_96,B_97] :
      ( r1_tarski(D_95,'#skF_7'(A_96,B_97,k4_setfam_1(A_96,B_97),D_95))
      | ~ r2_hidden(D_95,k4_setfam_1(A_96,B_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2])).

tff(c_10,plain,(
    ! [A_5,B_6,D_14] :
      ( ~ r1_tarski('#skF_1'(A_5,B_6),D_14)
      | ~ r2_hidden(D_14,B_6)
      | r1_setfam_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,(
    ! [A_98,B_99,A_100,B_101] :
      ( ~ r2_hidden('#skF_7'(A_98,B_99,k4_setfam_1(A_98,B_99),'#skF_1'(A_100,B_101)),B_101)
      | r1_setfam_1(A_100,B_101)
      | ~ r2_hidden('#skF_1'(A_100,B_101),k4_setfam_1(A_98,B_99)) ) ),
    inference(resolution,[status(thm)],[c_97,c_10])).

tff(c_109,plain,(
    ! [A_102,A_103,B_104] :
      ( r1_setfam_1(A_102,A_103)
      | ~ r2_hidden('#skF_1'(A_102,A_103),k4_setfam_1(A_103,B_104)) ) ),
    inference(resolution,[status(thm)],[c_20,c_103])).

tff(c_114,plain,(
    ! [B_6,B_104] : r1_setfam_1(k4_setfam_1(B_6,B_104),B_6) ),
    inference(resolution,[status(thm)],[c_12,c_109])).

tff(c_38,plain,(
    ~ r1_setfam_1(k4_setfam_1('#skF_9','#skF_9'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.16  
% 1.82/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.17  %$ r2_hidden > r1_tarski > r1_setfam_1 > k6_subset_1 > k4_xboole_0 > k4_setfam_1 > #nlpp > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_1
% 1.82/1.17  
% 1.82/1.17  %Foreground sorts:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Background operators:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Foreground operators:
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.17  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.82/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.17  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.82/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.82/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.17  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 1.82/1.17  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.82/1.17  tff(k4_setfam_1, type, k4_setfam_1: ($i * $i) > $i).
% 1.82/1.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.82/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.82/1.17  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 1.82/1.17  tff('#skF_9', type, '#skF_9': $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.17  
% 1.82/1.18  tff(f_41, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.82/1.18  tff(f_53, axiom, (![A, B, C]: ((C = k4_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k6_subset_1(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_setfam_1)).
% 1.82/1.18  tff(f_29, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.82/1.18  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.82/1.18  tff(f_56, negated_conjecture, ~(![A]: r1_setfam_1(k4_setfam_1(A, A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_setfam_1)).
% 1.82/1.18  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_setfam_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.82/1.18  tff(c_20, plain, (![A_17, B_18, D_44]: (r2_hidden('#skF_7'(A_17, B_18, k4_setfam_1(A_17, B_18), D_44), A_17) | ~r2_hidden(D_44, k4_setfam_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.82/1.18  tff(c_4, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.18  tff(c_16, plain, (![A_17, B_18, D_44]: (k6_subset_1('#skF_7'(A_17, B_18, k4_setfam_1(A_17, B_18), D_44), '#skF_8'(A_17, B_18, k4_setfam_1(A_17, B_18), D_44))=D_44 | ~r2_hidden(D_44, k4_setfam_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.82/1.18  tff(c_82, plain, (![A_92, B_93, D_94]: (k4_xboole_0('#skF_7'(A_92, B_93, k4_setfam_1(A_92, B_93), D_94), '#skF_8'(A_92, B_93, k4_setfam_1(A_92, B_93), D_94))=D_94 | ~r2_hidden(D_94, k4_setfam_1(A_92, B_93)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16])).
% 1.82/1.18  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.18  tff(c_97, plain, (![D_95, A_96, B_97]: (r1_tarski(D_95, '#skF_7'(A_96, B_97, k4_setfam_1(A_96, B_97), D_95)) | ~r2_hidden(D_95, k4_setfam_1(A_96, B_97)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_2])).
% 1.82/1.18  tff(c_10, plain, (![A_5, B_6, D_14]: (~r1_tarski('#skF_1'(A_5, B_6), D_14) | ~r2_hidden(D_14, B_6) | r1_setfam_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.82/1.18  tff(c_103, plain, (![A_98, B_99, A_100, B_101]: (~r2_hidden('#skF_7'(A_98, B_99, k4_setfam_1(A_98, B_99), '#skF_1'(A_100, B_101)), B_101) | r1_setfam_1(A_100, B_101) | ~r2_hidden('#skF_1'(A_100, B_101), k4_setfam_1(A_98, B_99)))), inference(resolution, [status(thm)], [c_97, c_10])).
% 1.82/1.18  tff(c_109, plain, (![A_102, A_103, B_104]: (r1_setfam_1(A_102, A_103) | ~r2_hidden('#skF_1'(A_102, A_103), k4_setfam_1(A_103, B_104)))), inference(resolution, [status(thm)], [c_20, c_103])).
% 1.82/1.18  tff(c_114, plain, (![B_6, B_104]: (r1_setfam_1(k4_setfam_1(B_6, B_104), B_6))), inference(resolution, [status(thm)], [c_12, c_109])).
% 1.82/1.18  tff(c_38, plain, (~r1_setfam_1(k4_setfam_1('#skF_9', '#skF_9'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.82/1.18  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_38])).
% 1.82/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.18  
% 1.82/1.18  Inference rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Ref     : 0
% 1.82/1.18  #Sup     : 12
% 1.82/1.18  #Fact    : 0
% 1.82/1.18  #Define  : 0
% 1.82/1.18  #Split   : 0
% 1.82/1.18  #Chain   : 0
% 1.82/1.18  #Close   : 0
% 1.82/1.18  
% 1.82/1.18  Ordering : KBO
% 1.82/1.18  
% 1.82/1.18  Simplification rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Subsume      : 0
% 1.82/1.18  #Demod        : 9
% 1.82/1.18  #Tautology    : 5
% 1.82/1.18  #SimpNegUnit  : 0
% 1.82/1.18  #BackRed      : 1
% 1.82/1.18  
% 1.82/1.18  #Partial instantiations: 0
% 1.82/1.18  #Strategies tried      : 1
% 1.82/1.18  
% 1.82/1.18  Timing (in seconds)
% 1.82/1.18  ----------------------
% 1.82/1.18  Preprocessing        : 0.29
% 1.82/1.18  Parsing              : 0.14
% 1.82/1.18  CNF conversion       : 0.02
% 1.82/1.18  Main loop            : 0.14
% 1.82/1.18  Inferencing          : 0.05
% 1.82/1.18  Reduction            : 0.04
% 1.82/1.18  Demodulation         : 0.03
% 1.82/1.18  BG Simplification    : 0.02
% 1.82/1.18  Subsumption          : 0.02
% 1.82/1.18  Abstraction          : 0.01
% 1.82/1.18  MUC search           : 0.00
% 1.82/1.18  Cooper               : 0.00
% 1.82/1.18  Total                : 0.45
% 1.82/1.18  Index Insertion      : 0.00
% 1.82/1.18  Index Deletion       : 0.00
% 1.82/1.18  Index Matching       : 0.00
% 1.82/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
