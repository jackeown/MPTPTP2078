%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:05 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  50 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_59,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_61,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(c_34,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_52,plain,(
    ! [B_39,A_40] :
      ( ~ v1_xboole_0(B_39)
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_82,plain,(
    ! [B_49,A_50] :
      ( m1_subset_1(B_49,A_50)
      | ~ r2_hidden(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_88,plain,
    ( m1_subset_1('#skF_1','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_82])).

tff(c_92,plain,(
    m1_subset_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_88])).

tff(c_106,plain,(
    ! [B_54,A_55] :
      ( m1_subset_1(k1_tarski(B_54),k1_zfmisc_1(A_55))
      | k1_xboole_0 = A_55
      | ~ m1_subset_1(B_54,A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ~ m1_subset_1(k1_tarski('#skF_1'),k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_112,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ m1_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_106,c_32])).

tff(c_116,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_112])).

tff(c_26,plain,(
    ! [A_33] : k1_subset_1(A_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_34] : v1_xboole_0(k1_subset_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_119,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_35])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:55:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.95/1.18  
% 1.95/1.18  %Foreground sorts:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Background operators:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Foreground operators:
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.18  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.95/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.95/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.18  
% 2.07/1.19  tff(f_73, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.07/1.19  tff(f_30, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.07/1.19  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.07/1.19  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.07/1.19  tff(f_59, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.07/1.19  tff(f_61, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 2.07/1.19  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.07/1.19  tff(c_52, plain, (![B_39, A_40]: (~v1_xboole_0(B_39) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.07/1.19  tff(c_56, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_52])).
% 2.07/1.19  tff(c_82, plain, (![B_49, A_50]: (m1_subset_1(B_49, A_50) | ~r2_hidden(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.07/1.19  tff(c_88, plain, (m1_subset_1('#skF_1', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_82])).
% 2.07/1.19  tff(c_92, plain, (m1_subset_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_88])).
% 2.07/1.19  tff(c_106, plain, (![B_54, A_55]: (m1_subset_1(k1_tarski(B_54), k1_zfmisc_1(A_55)) | k1_xboole_0=A_55 | ~m1_subset_1(B_54, A_55))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.19  tff(c_32, plain, (~m1_subset_1(k1_tarski('#skF_1'), k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.07/1.19  tff(c_112, plain, (k1_xboole_0='#skF_2' | ~m1_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_106, c_32])).
% 2.07/1.19  tff(c_116, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_112])).
% 2.07/1.19  tff(c_26, plain, (![A_33]: (k1_subset_1(A_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.07/1.19  tff(c_28, plain, (![A_34]: (v1_xboole_0(k1_subset_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.19  tff(c_35, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 2.07/1.19  tff(c_119, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_35])).
% 2.07/1.19  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_119])).
% 2.07/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.19  
% 2.07/1.19  Inference rules
% 2.07/1.19  ----------------------
% 2.07/1.19  #Ref     : 0
% 2.07/1.19  #Sup     : 17
% 2.07/1.19  #Fact    : 0
% 2.07/1.19  #Define  : 0
% 2.07/1.19  #Split   : 1
% 2.07/1.19  #Chain   : 0
% 2.07/1.19  #Close   : 0
% 2.07/1.19  
% 2.07/1.19  Ordering : KBO
% 2.07/1.19  
% 2.07/1.19  Simplification rules
% 2.07/1.19  ----------------------
% 2.07/1.19  #Subsume      : 1
% 2.07/1.19  #Demod        : 5
% 2.07/1.19  #Tautology    : 11
% 2.07/1.19  #SimpNegUnit  : 2
% 2.07/1.19  #BackRed      : 3
% 2.07/1.19  
% 2.07/1.19  #Partial instantiations: 0
% 2.07/1.19  #Strategies tried      : 1
% 2.07/1.19  
% 2.07/1.19  Timing (in seconds)
% 2.07/1.19  ----------------------
% 2.07/1.20  Preprocessing        : 0.32
% 2.07/1.20  Parsing              : 0.17
% 2.07/1.20  CNF conversion       : 0.02
% 2.07/1.20  Main loop            : 0.13
% 2.07/1.20  Inferencing          : 0.05
% 2.07/1.20  Reduction            : 0.04
% 2.07/1.20  Demodulation         : 0.03
% 2.07/1.20  BG Simplification    : 0.02
% 2.07/1.20  Subsumption          : 0.02
% 2.07/1.20  Abstraction          : 0.01
% 2.07/1.20  MUC search           : 0.00
% 2.07/1.20  Cooper               : 0.00
% 2.07/1.20  Total                : 0.47
% 2.07/1.20  Index Insertion      : 0.00
% 2.07/1.20  Index Deletion       : 0.00
% 2.07/1.20  Index Matching       : 0.00
% 2.07/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
