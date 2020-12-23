%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:05 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  58 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_32,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_35,plain,(
    ! [B_25,A_26] :
      ( ~ r2_hidden(B_25,A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_35])).

tff(c_74,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(B_35,A_36)
      | ~ r2_hidden(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_80,plain,
    ( m1_subset_1('#skF_2','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_74])).

tff(c_84,plain,(
    m1_subset_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_80])).

tff(c_123,plain,(
    ! [B_46,A_47] :
      ( m1_subset_1(k1_tarski(B_46),k1_zfmisc_1(A_47))
      | k1_xboole_0 = A_47
      | ~ m1_subset_1(B_46,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_129,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_30])).

tff(c_133,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_129])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [B_40,A_41] :
      ( ~ r1_xboole_0(B_40,A_41)
      | ~ r1_tarski(B_40,A_41)
      | v1_xboole_0(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [A_42] :
      ( ~ r1_tarski(A_42,k1_xboole_0)
      | v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_113,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_135,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_113])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.20  
% 1.83/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.20  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.83/1.20  
% 1.83/1.20  %Foreground sorts:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Background operators:
% 1.83/1.20  
% 1.83/1.20  
% 1.83/1.20  %Foreground operators:
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.83/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.83/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.83/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.83/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.83/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.83/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.83/1.20  
% 1.83/1.21  tff(f_76, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 1.83/1.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.83/1.21  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.83/1.21  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.83/1.21  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.83/1.21  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.83/1.21  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.83/1.21  tff(c_32, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.21  tff(c_35, plain, (![B_25, A_26]: (~r2_hidden(B_25, A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.21  tff(c_39, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_35])).
% 1.83/1.21  tff(c_74, plain, (![B_35, A_36]: (m1_subset_1(B_35, A_36) | ~r2_hidden(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.83/1.21  tff(c_80, plain, (m1_subset_1('#skF_2', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_74])).
% 1.83/1.21  tff(c_84, plain, (m1_subset_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_39, c_80])).
% 1.83/1.21  tff(c_123, plain, (![B_46, A_47]: (m1_subset_1(k1_tarski(B_46), k1_zfmisc_1(A_47)) | k1_xboole_0=A_47 | ~m1_subset_1(B_46, A_47))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.83/1.21  tff(c_30, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.83/1.21  tff(c_129, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_123, c_30])).
% 1.83/1.21  tff(c_133, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_129])).
% 1.83/1.21  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.21  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.21  tff(c_103, plain, (![B_40, A_41]: (~r1_xboole_0(B_40, A_41) | ~r1_tarski(B_40, A_41) | v1_xboole_0(B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.83/1.21  tff(c_108, plain, (![A_42]: (~r1_tarski(A_42, k1_xboole_0) | v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_8, c_103])).
% 1.83/1.21  tff(c_113, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_108])).
% 1.83/1.21  tff(c_135, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_113])).
% 1.83/1.21  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_135])).
% 1.83/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.21  
% 1.83/1.21  Inference rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Ref     : 0
% 1.83/1.21  #Sup     : 20
% 1.83/1.21  #Fact    : 0
% 1.83/1.21  #Define  : 0
% 1.83/1.21  #Split   : 1
% 1.83/1.21  #Chain   : 0
% 1.83/1.21  #Close   : 0
% 1.83/1.21  
% 1.83/1.21  Ordering : KBO
% 1.83/1.21  
% 1.83/1.21  Simplification rules
% 1.83/1.21  ----------------------
% 1.83/1.21  #Subsume      : 1
% 1.83/1.21  #Demod        : 6
% 1.83/1.21  #Tautology    : 11
% 1.83/1.21  #SimpNegUnit  : 2
% 1.83/1.21  #BackRed      : 5
% 1.83/1.21  
% 1.83/1.21  #Partial instantiations: 0
% 1.83/1.21  #Strategies tried      : 1
% 1.83/1.21  
% 1.83/1.21  Timing (in seconds)
% 1.83/1.21  ----------------------
% 1.83/1.21  Preprocessing        : 0.29
% 1.83/1.21  Parsing              : 0.15
% 1.83/1.21  CNF conversion       : 0.02
% 1.83/1.21  Main loop            : 0.13
% 1.83/1.21  Inferencing          : 0.05
% 1.83/1.21  Reduction            : 0.04
% 1.83/1.21  Demodulation         : 0.02
% 1.83/1.21  BG Simplification    : 0.01
% 1.83/1.21  Subsumption          : 0.02
% 1.83/1.21  Abstraction          : 0.01
% 1.83/1.21  MUC search           : 0.00
% 1.83/1.21  Cooper               : 0.00
% 1.83/1.21  Total                : 0.44
% 1.83/1.21  Index Insertion      : 0.00
% 1.83/1.21  Index Deletion       : 0.00
% 1.83/1.21  Index Matching       : 0.00
% 1.83/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
