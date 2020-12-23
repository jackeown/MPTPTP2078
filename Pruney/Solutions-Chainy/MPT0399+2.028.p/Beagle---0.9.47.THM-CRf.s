%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:35 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_208,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_3'(A_70,B_71,C_72),B_71)
      | ~ r2_hidden(C_72,A_70)
      | ~ r1_setfam_1(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_107,plain,(
    ! [A_46] : k4_xboole_0(A_46,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_103])).

tff(c_18,plain,(
    ! [C_16,B_15] : ~ r2_hidden(C_16,k4_xboole_0(B_15,k1_tarski(C_16))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_112,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_18])).

tff(c_268,plain,(
    ! [C_76,A_77] :
      ( ~ r2_hidden(C_76,A_77)
      | ~ r1_setfam_1(A_77,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_208,c_112])).

tff(c_293,plain,(
    ! [A_78] :
      ( ~ r1_setfam_1(A_78,k1_xboole_0)
      | k1_xboole_0 = A_78 ) ),
    inference(resolution,[status(thm)],[c_4,c_268])).

tff(c_304,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_293])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:40:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.20  
% 2.03/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.20  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 2.03/1.20  
% 2.03/1.20  %Foreground sorts:
% 2.03/1.20  
% 2.03/1.20  
% 2.03/1.20  %Background operators:
% 2.03/1.20  
% 2.03/1.20  
% 2.03/1.20  %Foreground operators:
% 2.03/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.20  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.03/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.03/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.03/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.03/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.03/1.20  
% 2.03/1.21  tff(f_71, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.03/1.21  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.03/1.21  tff(f_64, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.03/1.21  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.03/1.21  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.03/1.21  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.03/1.21  tff(f_52, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.03/1.21  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.21  tff(c_34, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.21  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.21  tff(c_208, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_3'(A_70, B_71, C_72), B_71) | ~r2_hidden(C_72, A_70) | ~r1_setfam_1(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.03/1.21  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.21  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.21  tff(c_94, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.03/1.21  tff(c_103, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_94])).
% 2.03/1.21  tff(c_107, plain, (![A_46]: (k4_xboole_0(A_46, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_103])).
% 2.03/1.21  tff(c_18, plain, (![C_16, B_15]: (~r2_hidden(C_16, k4_xboole_0(B_15, k1_tarski(C_16))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.03/1.21  tff(c_112, plain, (![C_16]: (~r2_hidden(C_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_107, c_18])).
% 2.03/1.21  tff(c_268, plain, (![C_76, A_77]: (~r2_hidden(C_76, A_77) | ~r1_setfam_1(A_77, k1_xboole_0))), inference(resolution, [status(thm)], [c_208, c_112])).
% 2.03/1.21  tff(c_293, plain, (![A_78]: (~r1_setfam_1(A_78, k1_xboole_0) | k1_xboole_0=A_78)), inference(resolution, [status(thm)], [c_4, c_268])).
% 2.03/1.21  tff(c_304, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_293])).
% 2.03/1.21  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_304])).
% 2.03/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.21  
% 2.03/1.21  Inference rules
% 2.03/1.21  ----------------------
% 2.03/1.21  #Ref     : 0
% 2.03/1.21  #Sup     : 58
% 2.03/1.21  #Fact    : 0
% 2.03/1.21  #Define  : 0
% 2.03/1.21  #Split   : 0
% 2.03/1.21  #Chain   : 0
% 2.03/1.21  #Close   : 0
% 2.03/1.21  
% 2.03/1.21  Ordering : KBO
% 2.03/1.21  
% 2.03/1.21  Simplification rules
% 2.03/1.21  ----------------------
% 2.03/1.21  #Subsume      : 4
% 2.03/1.21  #Demod        : 4
% 2.03/1.21  #Tautology    : 29
% 2.03/1.21  #SimpNegUnit  : 5
% 2.03/1.21  #BackRed      : 0
% 2.03/1.21  
% 2.03/1.21  #Partial instantiations: 0
% 2.03/1.21  #Strategies tried      : 1
% 2.03/1.21  
% 2.03/1.21  Timing (in seconds)
% 2.03/1.21  ----------------------
% 2.03/1.22  Preprocessing        : 0.29
% 2.03/1.22  Parsing              : 0.15
% 2.03/1.22  CNF conversion       : 0.02
% 2.03/1.22  Main loop            : 0.17
% 2.03/1.22  Inferencing          : 0.07
% 2.03/1.22  Reduction            : 0.05
% 2.03/1.22  Demodulation         : 0.03
% 2.03/1.22  BG Simplification    : 0.01
% 2.03/1.22  Subsumption          : 0.02
% 2.03/1.22  Abstraction          : 0.01
% 2.03/1.22  MUC search           : 0.00
% 2.03/1.22  Cooper               : 0.00
% 2.03/1.22  Total                : 0.48
% 2.03/1.22  Index Insertion      : 0.00
% 2.03/1.22  Index Deletion       : 0.00
% 2.03/1.22  Index Matching       : 0.00
% 2.03/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
