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
% DateTime   : Thu Dec  3 09:58:06 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_57,plain,(
    ! [B_25,A_26] : k2_xboole_0(B_25,A_26) = k2_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    ! [A_29] : k2_xboole_0(k1_xboole_0,A_29) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_4])).

tff(c_6,plain,(
    ! [A_4,B_5] : r1_tarski(A_4,k2_xboole_0(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [A_29] : r1_tarski(k1_xboole_0,A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_6])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_204,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k1_tarski(A_41),k1_zfmisc_1(B_42))
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_215,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_204,c_26])).

tff(c_218,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_215])).

tff(c_221,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_218])).

tff(c_233,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_221])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.24  
% 1.78/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.25  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 1.78/1.25  
% 1.78/1.25  %Foreground sorts:
% 1.78/1.25  
% 1.78/1.25  
% 1.78/1.25  %Background operators:
% 1.78/1.25  
% 1.78/1.25  
% 1.78/1.25  %Foreground operators:
% 1.78/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.78/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.78/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.78/1.25  
% 1.78/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.78/1.26  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.78/1.26  tff(f_31, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.78/1.26  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.78/1.26  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.78/1.26  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.78/1.26  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.78/1.26  tff(f_58, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 1.78/1.26  tff(c_57, plain, (![B_25, A_26]: (k2_xboole_0(B_25, A_26)=k2_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.26  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.26  tff(c_114, plain, (![A_29]: (k2_xboole_0(k1_xboole_0, A_29)=A_29)), inference(superposition, [status(thm), theory('equality')], [c_57, c_4])).
% 1.78/1.26  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(A_4, k2_xboole_0(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.26  tff(c_126, plain, (![A_29]: (r1_tarski(k1_xboole_0, A_29))), inference(superposition, [status(thm), theory('equality')], [c_114, c_6])).
% 1.78/1.26  tff(c_24, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.78/1.26  tff(c_16, plain, (![A_12]: (~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.78/1.26  tff(c_20, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.78/1.26  tff(c_204, plain, (![A_41, B_42]: (m1_subset_1(k1_tarski(A_41), k1_zfmisc_1(B_42)) | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.26  tff(c_26, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.78/1.26  tff(c_215, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_204, c_26])).
% 1.78/1.26  tff(c_218, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_215])).
% 1.78/1.26  tff(c_221, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_16, c_218])).
% 1.78/1.26  tff(c_233, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_24, c_221])).
% 1.78/1.26  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_233])).
% 1.78/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.26  
% 1.78/1.26  Inference rules
% 1.78/1.26  ----------------------
% 1.78/1.26  #Ref     : 0
% 1.78/1.26  #Sup     : 49
% 1.78/1.26  #Fact    : 0
% 1.78/1.26  #Define  : 0
% 1.78/1.26  #Split   : 0
% 1.78/1.26  #Chain   : 0
% 1.78/1.26  #Close   : 0
% 1.78/1.26  
% 1.78/1.26  Ordering : KBO
% 1.78/1.26  
% 1.78/1.26  Simplification rules
% 1.78/1.26  ----------------------
% 1.78/1.26  #Subsume      : 0
% 1.78/1.26  #Demod        : 13
% 1.78/1.26  #Tautology    : 36
% 1.78/1.26  #SimpNegUnit  : 1
% 1.78/1.26  #BackRed      : 0
% 1.78/1.26  
% 1.78/1.26  #Partial instantiations: 0
% 1.78/1.26  #Strategies tried      : 1
% 1.78/1.26  
% 1.78/1.26  Timing (in seconds)
% 1.78/1.26  ----------------------
% 1.78/1.26  Preprocessing        : 0.31
% 1.78/1.26  Parsing              : 0.16
% 1.78/1.26  CNF conversion       : 0.02
% 1.78/1.26  Main loop            : 0.15
% 1.78/1.26  Inferencing          : 0.06
% 1.78/1.26  Reduction            : 0.05
% 1.78/1.26  Demodulation         : 0.04
% 1.78/1.26  BG Simplification    : 0.01
% 1.78/1.26  Subsumption          : 0.02
% 1.78/1.26  Abstraction          : 0.01
% 1.78/1.26  MUC search           : 0.00
% 1.78/1.26  Cooper               : 0.00
% 1.78/1.26  Total                : 0.49
% 1.78/1.26  Index Insertion      : 0.00
% 1.78/1.26  Index Deletion       : 0.00
% 1.78/1.26  Index Matching       : 0.00
% 1.78/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
