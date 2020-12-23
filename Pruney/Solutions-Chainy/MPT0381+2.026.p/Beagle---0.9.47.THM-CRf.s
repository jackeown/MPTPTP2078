%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:04 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  57 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_80,plain,(
    ! [B_47,A_48] :
      ( ~ r2_hidden(B_47,A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_115,plain,(
    ! [B_56,A_57] :
      ( m1_subset_1(B_56,A_57)
      | ~ r2_hidden(B_56,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_121,plain,
    ( m1_subset_1('#skF_2','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_125,plain,(
    m1_subset_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_121])).

tff(c_189,plain,(
    ! [B_68,A_69] :
      ( m1_subset_1(k1_tarski(B_68),k1_zfmisc_1(A_69))
      | k1_xboole_0 = A_69
      | ~ m1_subset_1(B_68,A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_195,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_189,c_38])).

tff(c_199,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_195])).

tff(c_85,plain,(
    ! [A_49] :
      ( v1_xboole_0(A_49)
      | r2_hidden('#skF_1'(A_49),A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_33] : k2_zfmisc_1(A_33,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_63,plain,(
    ! [A_43,B_44] : ~ r2_hidden(A_43,k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_66,plain,(
    ! [A_33] : ~ r2_hidden(A_33,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_94,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_85,c_66])).

tff(c_211,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_94])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  
% 2.02/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.02/1.29  
% 2.02/1.29  %Foreground sorts:
% 2.02/1.29  
% 2.02/1.29  
% 2.02/1.29  %Background operators:
% 2.02/1.29  
% 2.02/1.29  
% 2.02/1.29  %Foreground operators:
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.29  
% 2.02/1.30  tff(f_79, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.02/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.02/1.30  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.02/1.30  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 2.02/1.30  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.02/1.30  tff(f_54, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.02/1.30  tff(c_40, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.02/1.30  tff(c_80, plain, (![B_47, A_48]: (~r2_hidden(B_47, A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.30  tff(c_84, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_80])).
% 2.02/1.30  tff(c_115, plain, (![B_56, A_57]: (m1_subset_1(B_56, A_57) | ~r2_hidden(B_56, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.30  tff(c_121, plain, (m1_subset_1('#skF_2', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_115])).
% 2.02/1.30  tff(c_125, plain, (m1_subset_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_84, c_121])).
% 2.02/1.30  tff(c_189, plain, (![B_68, A_69]: (m1_subset_1(k1_tarski(B_68), k1_zfmisc_1(A_69)) | k1_xboole_0=A_69 | ~m1_subset_1(B_68, A_69))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.02/1.30  tff(c_38, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.02/1.30  tff(c_195, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_189, c_38])).
% 2.02/1.30  tff(c_199, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_195])).
% 2.02/1.30  tff(c_85, plain, (![A_49]: (v1_xboole_0(A_49) | r2_hidden('#skF_1'(A_49), A_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.30  tff(c_22, plain, (![A_33]: (k2_zfmisc_1(A_33, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.02/1.30  tff(c_63, plain, (![A_43, B_44]: (~r2_hidden(A_43, k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.02/1.30  tff(c_66, plain, (![A_33]: (~r2_hidden(A_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_63])).
% 2.02/1.30  tff(c_94, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_85, c_66])).
% 2.02/1.30  tff(c_211, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_94])).
% 2.02/1.30  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_211])).
% 2.02/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.30  
% 2.02/1.30  Inference rules
% 2.02/1.30  ----------------------
% 2.02/1.30  #Ref     : 0
% 2.02/1.30  #Sup     : 36
% 2.02/1.30  #Fact    : 0
% 2.02/1.30  #Define  : 0
% 2.02/1.30  #Split   : 1
% 2.02/1.30  #Chain   : 0
% 2.02/1.30  #Close   : 0
% 2.02/1.30  
% 2.02/1.30  Ordering : KBO
% 2.02/1.30  
% 2.02/1.30  Simplification rules
% 2.02/1.30  ----------------------
% 2.02/1.30  #Subsume      : 2
% 2.02/1.30  #Demod        : 16
% 2.02/1.30  #Tautology    : 25
% 2.02/1.30  #SimpNegUnit  : 2
% 2.02/1.30  #BackRed      : 6
% 2.02/1.30  
% 2.02/1.30  #Partial instantiations: 0
% 2.02/1.30  #Strategies tried      : 1
% 2.02/1.30  
% 2.02/1.30  Timing (in seconds)
% 2.02/1.30  ----------------------
% 2.02/1.30  Preprocessing        : 0.35
% 2.02/1.30  Parsing              : 0.18
% 2.02/1.30  CNF conversion       : 0.02
% 2.02/1.30  Main loop            : 0.15
% 2.02/1.30  Inferencing          : 0.05
% 2.02/1.30  Reduction            : 0.05
% 2.02/1.30  Demodulation         : 0.03
% 2.02/1.30  BG Simplification    : 0.02
% 2.02/1.30  Subsumption          : 0.03
% 2.02/1.30  Abstraction          : 0.01
% 2.02/1.30  MUC search           : 0.00
% 2.02/1.30  Cooper               : 0.00
% 2.02/1.30  Total                : 0.52
% 2.02/1.30  Index Insertion      : 0.00
% 2.02/1.30  Index Deletion       : 0.00
% 2.02/1.30  Index Matching       : 0.00
% 2.02/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
