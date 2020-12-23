%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:08 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_41,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_120,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_75,plain,(
    ! [B_28,A_29] :
      ( ~ r2_hidden(B_28,A_29)
      | k4_xboole_0(A_29,k1_tarski(B_28)) != A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    ! [B_28] : ~ r2_hidden(B_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_130,plain,(
    ! [B_39] : r1_tarski(k1_xboole_0,B_39) ),
    inference(resolution,[status(thm)],[c_120,c_80])).

tff(c_16,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_zfmisc_1(A_34),k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_91,plain,(
    ! [B_35] :
      ( r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_35))
      | ~ r1_tarski(k1_xboole_0,B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_88])).

tff(c_134,plain,(
    ! [B_35] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_91])).

tff(c_58,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_28])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.37  
% 1.94/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.94/1.38  
% 1.94/1.38  %Foreground sorts:
% 1.94/1.38  
% 1.94/1.38  
% 1.94/1.38  %Background operators:
% 1.94/1.38  
% 1.94/1.38  
% 1.94/1.38  %Foreground operators:
% 1.94/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.94/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.38  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.38  
% 2.11/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.11/1.38  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.11/1.38  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.11/1.38  tff(f_41, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.11/1.38  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.11/1.38  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.11/1.38  tff(f_57, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.11/1.38  tff(c_120, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.11/1.38  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.11/1.38  tff(c_75, plain, (![B_28, A_29]: (~r2_hidden(B_28, A_29) | k4_xboole_0(A_29, k1_tarski(B_28))!=A_29)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.38  tff(c_80, plain, (![B_28]: (~r2_hidden(B_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_75])).
% 2.11/1.38  tff(c_130, plain, (![B_39]: (r1_tarski(k1_xboole_0, B_39))), inference(resolution, [status(thm)], [c_120, c_80])).
% 2.11/1.38  tff(c_16, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.38  tff(c_88, plain, (![A_34, B_35]: (r1_tarski(k1_zfmisc_1(A_34), k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.38  tff(c_91, plain, (![B_35]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_35)) | ~r1_tarski(k1_xboole_0, B_35))), inference(superposition, [status(thm), theory('equality')], [c_16, c_88])).
% 2.11/1.38  tff(c_134, plain, (![B_35]: (r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_35)))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_91])).
% 2.11/1.38  tff(c_58, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.11/1.38  tff(c_28, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.11/1.38  tff(c_65, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_28])).
% 2.11/1.38  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_65])).
% 2.11/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.38  
% 2.11/1.38  Inference rules
% 2.11/1.38  ----------------------
% 2.11/1.38  #Ref     : 0
% 2.11/1.38  #Sup     : 23
% 2.11/1.38  #Fact    : 0
% 2.11/1.38  #Define  : 0
% 2.11/1.38  #Split   : 0
% 2.11/1.38  #Chain   : 0
% 2.11/1.38  #Close   : 0
% 2.11/1.38  
% 2.11/1.38  Ordering : KBO
% 2.11/1.38  
% 2.11/1.38  Simplification rules
% 2.11/1.38  ----------------------
% 2.11/1.38  #Subsume      : 0
% 2.11/1.38  #Demod        : 2
% 2.11/1.38  #Tautology    : 15
% 2.11/1.38  #SimpNegUnit  : 2
% 2.11/1.38  #BackRed      : 1
% 2.11/1.38  
% 2.11/1.38  #Partial instantiations: 0
% 2.11/1.38  #Strategies tried      : 1
% 2.11/1.38  
% 2.11/1.38  Timing (in seconds)
% 2.11/1.38  ----------------------
% 2.11/1.39  Preprocessing        : 0.36
% 2.11/1.39  Parsing              : 0.19
% 2.11/1.39  CNF conversion       : 0.02
% 2.11/1.39  Main loop            : 0.13
% 2.11/1.39  Inferencing          : 0.06
% 2.11/1.39  Reduction            : 0.04
% 2.11/1.39  Demodulation         : 0.02
% 2.11/1.39  BG Simplification    : 0.01
% 2.11/1.39  Subsumption          : 0.02
% 2.11/1.39  Abstraction          : 0.01
% 2.11/1.39  MUC search           : 0.00
% 2.11/1.39  Cooper               : 0.00
% 2.11/1.39  Total                : 0.52
% 2.11/1.39  Index Insertion      : 0.00
% 2.11/1.39  Index Deletion       : 0.00
% 2.11/1.39  Index Matching       : 0.00
% 2.11/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
