%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:10 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_zfmisc_1(A_19),k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_49,plain,(
    ! [B_20] :
      ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_20))
      | ~ r1_tarski(k1_xboole_0,B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_54,plain,(
    ! [B_20] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_49])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [A_22,C_23,B_24] :
      ( r2_hidden(A_22,C_23)
      | ~ r1_tarski(k2_tarski(A_22,B_24),C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [A_28,C_29] :
      ( r2_hidden(A_28,C_29)
      | ~ r1_tarski(k1_tarski(A_28),C_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_58])).

tff(c_74,plain,(
    ! [B_20] : r2_hidden(k1_xboole_0,k1_zfmisc_1(B_20)) ),
    inference(resolution,[status(thm)],[c_54,c_66])).

tff(c_79,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k1_tarski(A_31),k1_zfmisc_1(B_32))
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_82,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_79,c_22])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:17:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.18  
% 1.76/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.18  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 1.76/1.18  
% 1.76/1.18  %Foreground sorts:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Background operators:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Foreground operators:
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.76/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.76/1.18  
% 1.76/1.19  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.76/1.19  tff(f_34, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 1.76/1.19  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.76/1.19  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.76/1.19  tff(f_40, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.76/1.19  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.76/1.19  tff(f_51, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.76/1.19  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.76/1.19  tff(c_10, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.19  tff(c_46, plain, (![A_19, B_20]: (r1_tarski(k1_zfmisc_1(A_19), k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.76/1.19  tff(c_49, plain, (![B_20]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_20)) | ~r1_tarski(k1_xboole_0, B_20))), inference(superposition, [status(thm), theory('equality')], [c_10, c_46])).
% 1.76/1.19  tff(c_54, plain, (![B_20]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_20)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_49])).
% 1.76/1.19  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.76/1.19  tff(c_58, plain, (![A_22, C_23, B_24]: (r2_hidden(A_22, C_23) | ~r1_tarski(k2_tarski(A_22, B_24), C_23))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.76/1.19  tff(c_66, plain, (![A_28, C_29]: (r2_hidden(A_28, C_29) | ~r1_tarski(k1_tarski(A_28), C_29))), inference(superposition, [status(thm), theory('equality')], [c_4, c_58])).
% 1.76/1.19  tff(c_74, plain, (![B_20]: (r2_hidden(k1_xboole_0, k1_zfmisc_1(B_20)))), inference(resolution, [status(thm)], [c_54, c_66])).
% 1.76/1.19  tff(c_79, plain, (![A_31, B_32]: (m1_subset_1(k1_tarski(A_31), k1_zfmisc_1(B_32)) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.76/1.19  tff(c_22, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.76/1.19  tff(c_82, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_79, c_22])).
% 1.76/1.19  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_82])).
% 1.76/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.19  
% 1.76/1.19  Inference rules
% 1.76/1.19  ----------------------
% 1.76/1.19  #Ref     : 0
% 1.76/1.19  #Sup     : 16
% 1.76/1.19  #Fact    : 0
% 1.76/1.19  #Define  : 0
% 1.76/1.19  #Split   : 0
% 1.76/1.19  #Chain   : 0
% 1.76/1.19  #Close   : 0
% 1.76/1.19  
% 1.76/1.19  Ordering : KBO
% 1.76/1.19  
% 1.76/1.19  Simplification rules
% 1.76/1.19  ----------------------
% 1.76/1.19  #Subsume      : 1
% 1.76/1.19  #Demod        : 3
% 1.76/1.19  #Tautology    : 7
% 1.76/1.19  #SimpNegUnit  : 0
% 1.76/1.19  #BackRed      : 0
% 1.76/1.19  
% 1.76/1.19  #Partial instantiations: 0
% 1.76/1.19  #Strategies tried      : 1
% 1.76/1.19  
% 1.76/1.19  Timing (in seconds)
% 1.76/1.19  ----------------------
% 1.76/1.19  Preprocessing        : 0.29
% 1.76/1.19  Parsing              : 0.16
% 1.76/1.19  CNF conversion       : 0.02
% 1.76/1.19  Main loop            : 0.10
% 1.76/1.19  Inferencing          : 0.04
% 1.76/1.19  Reduction            : 0.03
% 1.76/1.19  Demodulation         : 0.02
% 1.76/1.20  BG Simplification    : 0.01
% 1.76/1.20  Subsumption          : 0.01
% 1.76/1.20  Abstraction          : 0.01
% 1.76/1.20  MUC search           : 0.00
% 1.76/1.20  Cooper               : 0.00
% 1.76/1.20  Total                : 0.42
% 1.76/1.20  Index Insertion      : 0.00
% 1.76/1.20  Index Deletion       : 0.00
% 1.76/1.20  Index Matching       : 0.00
% 1.76/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
