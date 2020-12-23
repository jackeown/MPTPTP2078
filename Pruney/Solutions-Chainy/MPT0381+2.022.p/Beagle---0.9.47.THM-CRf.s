%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:04 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  62 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_38,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [B_27,A_28] :
      ( ~ r2_hidden(B_27,A_28)
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_40])).

tff(c_141,plain,(
    ! [B_49,A_50] :
      ( m1_subset_1(B_49,A_50)
      | ~ r2_hidden(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_150,plain,
    ( m1_subset_1('#skF_2','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_141])).

tff(c_155,plain,(
    m1_subset_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_150])).

tff(c_184,plain,(
    ! [B_57,A_58] :
      ( m1_subset_1(k1_tarski(B_57),k1_zfmisc_1(A_58))
      | k1_xboole_0 = A_58
      | ~ m1_subset_1(B_57,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_190,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_184,c_36])).

tff(c_194,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_190])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_74])).

tff(c_120,plain,(
    ! [B_46,A_47] :
      ( ~ r2_hidden(B_46,A_47)
      | k4_xboole_0(A_47,k1_tarski(B_46)) != A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_130,plain,(
    ! [B_48] : ~ r2_hidden(B_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_120])).

tff(c_140,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_196,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_140])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:47:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.25  
% 2.01/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.25  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.01/1.25  
% 2.01/1.25  %Foreground sorts:
% 2.01/1.25  
% 2.01/1.25  
% 2.01/1.25  %Background operators:
% 2.01/1.25  
% 2.01/1.25  
% 2.01/1.25  %Foreground operators:
% 2.01/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.01/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.01/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.25  
% 2.01/1.26  tff(f_77, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.01/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.01/1.26  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.01/1.26  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.01/1.26  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.01/1.26  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.01/1.26  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.01/1.26  tff(c_38, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.01/1.26  tff(c_40, plain, (![B_27, A_28]: (~r2_hidden(B_27, A_28) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.26  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_40])).
% 2.01/1.26  tff(c_141, plain, (![B_49, A_50]: (m1_subset_1(B_49, A_50) | ~r2_hidden(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.01/1.26  tff(c_150, plain, (m1_subset_1('#skF_2', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_141])).
% 2.01/1.26  tff(c_155, plain, (m1_subset_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_44, c_150])).
% 2.01/1.26  tff(c_184, plain, (![B_57, A_58]: (m1_subset_1(k1_tarski(B_57), k1_zfmisc_1(A_58)) | k1_xboole_0=A_58 | ~m1_subset_1(B_57, A_58))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.01/1.26  tff(c_36, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.01/1.26  tff(c_190, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_184, c_36])).
% 2.01/1.26  tff(c_194, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_190])).
% 2.01/1.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.26  tff(c_12, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.01/1.26  tff(c_74, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.26  tff(c_78, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_74])).
% 2.01/1.26  tff(c_120, plain, (![B_46, A_47]: (~r2_hidden(B_46, A_47) | k4_xboole_0(A_47, k1_tarski(B_46))!=A_47)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.01/1.26  tff(c_130, plain, (![B_48]: (~r2_hidden(B_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_120])).
% 2.01/1.26  tff(c_140, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_130])).
% 2.01/1.26  tff(c_196, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_140])).
% 2.01/1.26  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_196])).
% 2.01/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.26  
% 2.01/1.26  Inference rules
% 2.01/1.26  ----------------------
% 2.01/1.26  #Ref     : 0
% 2.01/1.26  #Sup     : 32
% 2.01/1.26  #Fact    : 0
% 2.01/1.26  #Define  : 0
% 2.01/1.26  #Split   : 1
% 2.01/1.26  #Chain   : 0
% 2.01/1.26  #Close   : 0
% 2.01/1.26  
% 2.01/1.26  Ordering : KBO
% 2.01/1.26  
% 2.01/1.26  Simplification rules
% 2.01/1.26  ----------------------
% 2.01/1.26  #Subsume      : 1
% 2.01/1.26  #Demod        : 10
% 2.01/1.26  #Tautology    : 22
% 2.01/1.26  #SimpNegUnit  : 2
% 2.01/1.26  #BackRed      : 7
% 2.01/1.26  
% 2.01/1.26  #Partial instantiations: 0
% 2.01/1.26  #Strategies tried      : 1
% 2.01/1.26  
% 2.01/1.26  Timing (in seconds)
% 2.01/1.26  ----------------------
% 2.01/1.27  Preprocessing        : 0.32
% 2.01/1.27  Parsing              : 0.17
% 2.01/1.27  CNF conversion       : 0.02
% 2.01/1.27  Main loop            : 0.16
% 2.01/1.27  Inferencing          : 0.06
% 2.01/1.27  Reduction            : 0.05
% 2.01/1.27  Demodulation         : 0.03
% 2.01/1.27  BG Simplification    : 0.01
% 2.01/1.27  Subsumption          : 0.03
% 2.01/1.27  Abstraction          : 0.01
% 2.01/1.27  MUC search           : 0.00
% 2.01/1.27  Cooper               : 0.00
% 2.01/1.27  Total                : 0.51
% 2.01/1.27  Index Insertion      : 0.00
% 2.01/1.27  Index Deletion       : 0.00
% 2.01/1.27  Index Matching       : 0.00
% 2.01/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
