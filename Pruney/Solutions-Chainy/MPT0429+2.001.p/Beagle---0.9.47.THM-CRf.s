%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:06 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  35 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_58,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    ! [B_23,A_24] : r1_tarski(B_23,k2_xboole_0(A_24,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_274,plain,(
    ! [A_47,B_48] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A_47),k1_zfmisc_1(B_48)),k1_zfmisc_1(k2_xboole_0(A_47,B_48))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_294,plain,(
    ! [A_5] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A_5),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_274])).

tff(c_306,plain,(
    ! [A_49] : r1_tarski(k2_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_49)),k1_zfmisc_1(A_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20,c_294])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_311,plain,(
    ! [A_49] :
      ( k2_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_49)) = k1_zfmisc_1(A_49)
      | ~ r1_tarski(k1_zfmisc_1(A_49),k2_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_49))) ) ),
    inference(resolution,[status(thm)],[c_306,c_4])).

tff(c_326,plain,(
    ! [A_50] : k2_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_50)) = k1_zfmisc_1(A_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_311])).

tff(c_344,plain,(
    ! [A_50] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(A_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_12])).

tff(c_182,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(A_31,k1_zfmisc_1(B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_189,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_182,c_28])).

tff(c_360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.31  
% 1.95/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.32  %$ r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 1.95/1.32  
% 1.95/1.32  %Foreground sorts:
% 1.95/1.32  
% 1.95/1.32  
% 1.95/1.32  %Background operators:
% 1.95/1.32  
% 1.95/1.32  
% 1.95/1.32  %Foreground operators:
% 1.95/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.32  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.32  
% 1.95/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.95/1.33  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.95/1.33  tff(f_44, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 1.95/1.33  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.95/1.33  tff(f_46, axiom, (![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 1.95/1.33  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.95/1.33  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.95/1.33  tff(f_53, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.95/1.33  tff(c_58, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.33  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.33  tff(c_76, plain, (![B_23, A_24]: (r1_tarski(B_23, k2_xboole_0(A_24, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_12])).
% 1.95/1.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.33  tff(c_20, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.33  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.33  tff(c_274, plain, (![A_47, B_48]: (r1_tarski(k2_xboole_0(k1_zfmisc_1(A_47), k1_zfmisc_1(B_48)), k1_zfmisc_1(k2_xboole_0(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.33  tff(c_294, plain, (![A_5]: (r1_tarski(k2_xboole_0(k1_zfmisc_1(A_5), k1_zfmisc_1(k1_xboole_0)), k1_zfmisc_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_274])).
% 1.95/1.33  tff(c_306, plain, (![A_49]: (r1_tarski(k2_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_49)), k1_zfmisc_1(A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20, c_294])).
% 1.95/1.33  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.33  tff(c_311, plain, (![A_49]: (k2_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_49))=k1_zfmisc_1(A_49) | ~r1_tarski(k1_zfmisc_1(A_49), k2_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_49))))), inference(resolution, [status(thm)], [c_306, c_4])).
% 1.95/1.33  tff(c_326, plain, (![A_50]: (k2_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_50))=k1_zfmisc_1(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_311])).
% 1.95/1.33  tff(c_344, plain, (![A_50]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(A_50)))), inference(superposition, [status(thm), theory('equality')], [c_326, c_12])).
% 1.95/1.33  tff(c_182, plain, (![A_31, B_32]: (m1_subset_1(A_31, k1_zfmisc_1(B_32)) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.95/1.33  tff(c_28, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.33  tff(c_189, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_182, c_28])).
% 1.95/1.33  tff(c_360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_189])).
% 1.95/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.33  
% 1.95/1.33  Inference rules
% 1.95/1.33  ----------------------
% 1.95/1.33  #Ref     : 0
% 1.95/1.33  #Sup     : 78
% 1.95/1.33  #Fact    : 0
% 1.95/1.33  #Define  : 0
% 1.95/1.33  #Split   : 0
% 1.95/1.33  #Chain   : 0
% 1.95/1.33  #Close   : 0
% 1.95/1.33  
% 1.95/1.33  Ordering : KBO
% 1.95/1.33  
% 1.95/1.33  Simplification rules
% 2.23/1.33  ----------------------
% 2.23/1.33  #Subsume      : 2
% 2.23/1.33  #Demod        : 38
% 2.23/1.33  #Tautology    : 48
% 2.23/1.33  #SimpNegUnit  : 0
% 2.23/1.33  #BackRed      : 2
% 2.23/1.33  
% 2.23/1.33  #Partial instantiations: 0
% 2.23/1.33  #Strategies tried      : 1
% 2.23/1.33  
% 2.23/1.33  Timing (in seconds)
% 2.23/1.33  ----------------------
% 2.23/1.33  Preprocessing        : 0.32
% 2.23/1.33  Parsing              : 0.16
% 2.23/1.33  CNF conversion       : 0.02
% 2.23/1.33  Main loop            : 0.20
% 2.23/1.33  Inferencing          : 0.07
% 2.23/1.33  Reduction            : 0.07
% 2.23/1.33  Demodulation         : 0.06
% 2.23/1.33  BG Simplification    : 0.01
% 2.23/1.33  Subsumption          : 0.04
% 2.23/1.33  Abstraction          : 0.01
% 2.23/1.33  MUC search           : 0.00
% 2.23/1.33  Cooper               : 0.00
% 2.23/1.33  Total                : 0.54
% 2.23/1.33  Index Insertion      : 0.00
% 2.23/1.33  Index Deletion       : 0.00
% 2.23/1.33  Index Matching       : 0.00
% 2.23/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
