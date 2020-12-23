%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:07 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   43 (  44 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  40 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden('#skF_1'(A_67,B_68),B_68)
      | r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_36,plain,(
    ! [A_39] : k2_zfmisc_1(A_39,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_72,plain,(
    ! [A_52,B_53] : ~ r2_hidden(A_52,k2_zfmisc_1(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [A_39] : ~ r2_hidden(A_39,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_72])).

tff(c_42,plain,(
    ! [A_43] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_159,plain,(
    ! [B_79,A_80] :
      ( m1_subset_1(k1_tarski(B_79),k1_zfmisc_1(A_80))
      | k1_xboole_0 = A_80
      | ~ m1_subset_1(B_79,A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_164,plain,
    ( k1_zfmisc_1('#skF_4') = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_159,c_48])).

tff(c_168,plain,(
    k1_zfmisc_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_164])).

tff(c_24,plain,(
    ! [C_38,A_34] :
      ( r2_hidden(C_38,k1_zfmisc_1(A_34))
      | ~ r1_tarski(C_38,A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_181,plain,(
    ! [C_38] :
      ( r2_hidden(C_38,k1_xboole_0)
      | ~ r1_tarski(C_38,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_24])).

tff(c_188,plain,(
    ! [C_81] : ~ r1_tarski(C_81,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_181])).

tff(c_196,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_136,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.20  
% 2.01/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.01/1.20  
% 2.01/1.20  %Foreground sorts:
% 2.01/1.20  
% 2.01/1.20  
% 2.01/1.20  %Background operators:
% 2.01/1.20  
% 2.01/1.20  
% 2.01/1.20  %Foreground operators:
% 2.01/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.20  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.01/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.01/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.01/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.21  
% 2.01/1.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.01/1.21  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.01/1.21  tff(f_62, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.01/1.21  tff(f_64, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.01/1.21  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.01/1.21  tff(f_80, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.01/1.21  tff(f_53, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.01/1.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.01/1.21  tff(c_127, plain, (![A_67, B_68]: (~r2_hidden('#skF_1'(A_67, B_68), B_68) | r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.01/1.21  tff(c_136, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_127])).
% 2.01/1.21  tff(c_36, plain, (![A_39]: (k2_zfmisc_1(A_39, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.01/1.21  tff(c_72, plain, (![A_52, B_53]: (~r2_hidden(A_52, k2_zfmisc_1(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.01/1.21  tff(c_75, plain, (![A_39]: (~r2_hidden(A_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_72])).
% 2.01/1.21  tff(c_42, plain, (![A_43]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.01/1.21  tff(c_159, plain, (![B_79, A_80]: (m1_subset_1(k1_tarski(B_79), k1_zfmisc_1(A_80)) | k1_xboole_0=A_80 | ~m1_subset_1(B_79, A_80))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.01/1.21  tff(c_48, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.01/1.21  tff(c_164, plain, (k1_zfmisc_1('#skF_4')=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_159, c_48])).
% 2.01/1.21  tff(c_168, plain, (k1_zfmisc_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_164])).
% 2.01/1.21  tff(c_24, plain, (![C_38, A_34]: (r2_hidden(C_38, k1_zfmisc_1(A_34)) | ~r1_tarski(C_38, A_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.21  tff(c_181, plain, (![C_38]: (r2_hidden(C_38, k1_xboole_0) | ~r1_tarski(C_38, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_24])).
% 2.01/1.21  tff(c_188, plain, (![C_81]: (~r1_tarski(C_81, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_75, c_181])).
% 2.01/1.21  tff(c_196, plain, $false, inference(resolution, [status(thm)], [c_136, c_188])).
% 2.01/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.21  
% 2.01/1.21  Inference rules
% 2.01/1.21  ----------------------
% 2.01/1.21  #Ref     : 0
% 2.01/1.21  #Sup     : 35
% 2.01/1.21  #Fact    : 0
% 2.01/1.21  #Define  : 0
% 2.01/1.21  #Split   : 0
% 2.01/1.21  #Chain   : 0
% 2.01/1.21  #Close   : 0
% 2.01/1.21  
% 2.01/1.21  Ordering : KBO
% 2.01/1.21  
% 2.01/1.21  Simplification rules
% 2.01/1.21  ----------------------
% 2.01/1.21  #Subsume      : 3
% 2.01/1.21  #Demod        : 2
% 2.01/1.21  #Tautology    : 17
% 2.01/1.21  #SimpNegUnit  : 1
% 2.01/1.21  #BackRed      : 1
% 2.01/1.21  
% 2.01/1.21  #Partial instantiations: 0
% 2.01/1.21  #Strategies tried      : 1
% 2.01/1.21  
% 2.01/1.21  Timing (in seconds)
% 2.01/1.21  ----------------------
% 2.01/1.22  Preprocessing        : 0.32
% 2.01/1.22  Parsing              : 0.17
% 2.01/1.22  CNF conversion       : 0.02
% 2.01/1.22  Main loop            : 0.13
% 2.01/1.22  Inferencing          : 0.04
% 2.01/1.22  Reduction            : 0.04
% 2.01/1.22  Demodulation         : 0.03
% 2.01/1.22  BG Simplification    : 0.01
% 2.01/1.22  Subsumption          : 0.02
% 2.01/1.22  Abstraction          : 0.01
% 2.01/1.22  MUC search           : 0.00
% 2.01/1.22  Cooper               : 0.00
% 2.01/1.22  Total                : 0.47
% 2.01/1.22  Index Insertion      : 0.00
% 2.01/1.22  Index Deletion       : 0.00
% 2.01/1.22  Index Matching       : 0.00
% 2.01/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
