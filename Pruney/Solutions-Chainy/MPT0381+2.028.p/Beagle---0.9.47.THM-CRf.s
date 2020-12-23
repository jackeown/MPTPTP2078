%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:05 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 120 expanded)
%              Number of leaves         :   26 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 ( 195 expanded)
%              Number of equality atoms :    7 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_40,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_46,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    ! [B_42,A_43] :
      ( ~ r2_hidden(B_42,A_43)
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [B_52,A_53] :
      ( m1_subset_1(B_52,A_53)
      | ~ r2_hidden(B_52,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_101,plain,
    ( m1_subset_1('#skF_2','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_95])).

tff(c_105,plain,(
    m1_subset_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101])).

tff(c_133,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(k1_tarski(B_60),k1_zfmisc_1(A_61))
      | k1_xboole_0 = A_61
      | ~ m1_subset_1(B_60,A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_139,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_44])).

tff(c_143,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_139])).

tff(c_18,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_145,plain,(
    ! [A_8] : k5_xboole_0(A_8,'#skF_3') = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_18])).

tff(c_180,plain,(
    ! [A_69,B_70,C_71] :
      ( r2_hidden(A_69,B_70)
      | ~ r2_hidden(A_69,C_71)
      | r2_hidden(A_69,k5_xboole_0(B_70,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_192,plain,(
    ! [A_72,A_73] :
      ( r2_hidden(A_72,A_73)
      | ~ r2_hidden(A_72,'#skF_3')
      | r2_hidden(A_72,A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_180])).

tff(c_198,plain,(
    ! [A_73] :
      ( r2_hidden('#skF_1'('#skF_3'),A_73)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4,c_192])).

tff(c_206,plain,(
    ! [A_73] : r2_hidden('#skF_1'('#skF_3'),A_73) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_198])).

tff(c_358,plain,(
    ! [A_98,C_99,B_100] :
      ( ~ r2_hidden(A_98,C_99)
      | ~ r2_hidden(A_98,B_100)
      | ~ r2_hidden(A_98,k5_xboole_0(B_100,C_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_370,plain,(
    ! [C_99,B_100] :
      ( ~ r2_hidden('#skF_1'('#skF_3'),C_99)
      | ~ r2_hidden('#skF_1'('#skF_3'),B_100) ) ),
    inference(resolution,[status(thm)],[c_206,c_358])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_206,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:50:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.38  
% 2.44/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.38  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.44/1.38  
% 2.44/1.38  %Foreground sorts:
% 2.44/1.38  
% 2.44/1.38  
% 2.44/1.38  %Background operators:
% 2.44/1.38  
% 2.44/1.38  
% 2.44/1.38  %Foreground operators:
% 2.44/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.44/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.44/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.44/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.44/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.38  
% 2.44/1.39  tff(f_79, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.44/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.44/1.39  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.44/1.39  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.44/1.39  tff(f_40, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.44/1.39  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.44/1.39  tff(c_46, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.44/1.39  tff(c_56, plain, (![B_42, A_43]: (~r2_hidden(B_42, A_43) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.39  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_56])).
% 2.44/1.39  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.44/1.39  tff(c_95, plain, (![B_52, A_53]: (m1_subset_1(B_52, A_53) | ~r2_hidden(B_52, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.44/1.39  tff(c_101, plain, (m1_subset_1('#skF_2', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_95])).
% 2.44/1.39  tff(c_105, plain, (m1_subset_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_101])).
% 2.44/1.39  tff(c_133, plain, (![B_60, A_61]: (m1_subset_1(k1_tarski(B_60), k1_zfmisc_1(A_61)) | k1_xboole_0=A_61 | ~m1_subset_1(B_60, A_61))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.44/1.39  tff(c_44, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.44/1.39  tff(c_139, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_133, c_44])).
% 2.44/1.39  tff(c_143, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_139])).
% 2.44/1.39  tff(c_18, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.44/1.39  tff(c_145, plain, (![A_8]: (k5_xboole_0(A_8, '#skF_3')=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_18])).
% 2.44/1.39  tff(c_180, plain, (![A_69, B_70, C_71]: (r2_hidden(A_69, B_70) | ~r2_hidden(A_69, C_71) | r2_hidden(A_69, k5_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.39  tff(c_192, plain, (![A_72, A_73]: (r2_hidden(A_72, A_73) | ~r2_hidden(A_72, '#skF_3') | r2_hidden(A_72, A_73))), inference(superposition, [status(thm), theory('equality')], [c_145, c_180])).
% 2.44/1.39  tff(c_198, plain, (![A_73]: (r2_hidden('#skF_1'('#skF_3'), A_73) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_192])).
% 2.44/1.39  tff(c_206, plain, (![A_73]: (r2_hidden('#skF_1'('#skF_3'), A_73))), inference(negUnitSimplification, [status(thm)], [c_60, c_198])).
% 2.44/1.39  tff(c_358, plain, (![A_98, C_99, B_100]: (~r2_hidden(A_98, C_99) | ~r2_hidden(A_98, B_100) | ~r2_hidden(A_98, k5_xboole_0(B_100, C_99)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.39  tff(c_370, plain, (![C_99, B_100]: (~r2_hidden('#skF_1'('#skF_3'), C_99) | ~r2_hidden('#skF_1'('#skF_3'), B_100))), inference(resolution, [status(thm)], [c_206, c_358])).
% 2.44/1.39  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_206, c_370])).
% 2.44/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.39  
% 2.44/1.39  Inference rules
% 2.44/1.39  ----------------------
% 2.44/1.39  #Ref     : 0
% 2.44/1.39  #Sup     : 71
% 2.44/1.39  #Fact    : 0
% 2.44/1.39  #Define  : 0
% 2.44/1.39  #Split   : 1
% 2.44/1.39  #Chain   : 0
% 2.44/1.39  #Close   : 0
% 2.44/1.39  
% 2.44/1.39  Ordering : KBO
% 2.44/1.39  
% 2.44/1.39  Simplification rules
% 2.44/1.39  ----------------------
% 2.44/1.39  #Subsume      : 12
% 2.44/1.39  #Demod        : 20
% 2.44/1.39  #Tautology    : 39
% 2.44/1.39  #SimpNegUnit  : 9
% 2.44/1.39  #BackRed      : 6
% 2.44/1.39  
% 2.44/1.39  #Partial instantiations: 0
% 2.44/1.39  #Strategies tried      : 1
% 2.44/1.39  
% 2.44/1.39  Timing (in seconds)
% 2.44/1.39  ----------------------
% 2.44/1.39  Preprocessing        : 0.34
% 2.44/1.39  Parsing              : 0.18
% 2.44/1.39  CNF conversion       : 0.02
% 2.44/1.39  Main loop            : 0.23
% 2.44/1.39  Inferencing          : 0.09
% 2.44/1.39  Reduction            : 0.06
% 2.44/1.39  Demodulation         : 0.04
% 2.44/1.39  BG Simplification    : 0.02
% 2.44/1.39  Subsumption          : 0.05
% 2.44/1.39  Abstraction          : 0.02
% 2.44/1.39  MUC search           : 0.00
% 2.44/1.40  Cooper               : 0.00
% 2.44/1.40  Total                : 0.60
% 2.44/1.40  Index Insertion      : 0.00
% 2.44/1.40  Index Deletion       : 0.00
% 2.44/1.40  Index Matching       : 0.00
% 2.44/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
