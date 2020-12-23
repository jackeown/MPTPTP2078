%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:06 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   31 (  82 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 ( 191 expanded)
%              Number of equality atoms :   16 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => k5_partfun1(A,A,k3_partfun1(B,A,A)) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k5_partfun1(A,B,k3_partfun1(C,A,B)) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_2)).

tff(c_10,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [B_12,A_13,C_14] :
      ( k1_xboole_0 = B_12
      | k5_partfun1(A_13,B_12,k3_partfun1(C_14,A_13,B_12)) = k1_tarski(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_13,B_12)))
      | ~ v1_funct_2(C_14,A_13,B_12)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_1'
    | k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) = k1_tarski('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_36])).

tff(c_41,plain,
    ( k1_xboole_0 = '#skF_1'
    | k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_38])).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_41])).

tff(c_6,plain,(
    ! [B_5,C_6] :
      ( k5_partfun1(k1_xboole_0,B_5,k3_partfun1(C_6,k1_xboole_0,B_5)) = k1_tarski(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_2(C_6,k1_xboole_0,B_5)
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [B_15,C_16] :
      ( k5_partfun1('#skF_1',B_15,k3_partfun1(C_16,'#skF_1',B_15)) = k1_tarski(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_15)))
      | ~ v1_funct_2(C_16,'#skF_1',B_15)
      | ~ v1_funct_1(C_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_42,c_42,c_6])).

tff(c_51,plain,
    ( k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) = k1_tarski('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_49])).

tff(c_54,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_51])).

tff(c_56,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:12:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.17  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.75/1.17  
% 1.75/1.17  %Foreground sorts:
% 1.75/1.17  
% 1.75/1.17  
% 1.75/1.17  %Background operators:
% 1.75/1.17  
% 1.75/1.17  
% 1.75/1.17  %Foreground operators:
% 1.75/1.17  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 1.75/1.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.75/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.75/1.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.75/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.75/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.75/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.75/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.17  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 1.75/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.75/1.17  
% 1.75/1.18  tff(f_50, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k5_partfun1(A, A, k3_partfun1(B, A, A)) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_2)).
% 1.75/1.18  tff(f_41, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k5_partfun1(A, B, k3_partfun1(C, A, B)) = k1_tarski(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t161_funct_2)).
% 1.75/1.18  tff(c_10, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.18  tff(c_16, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.18  tff(c_14, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.18  tff(c_12, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.75/1.18  tff(c_36, plain, (![B_12, A_13, C_14]: (k1_xboole_0=B_12 | k5_partfun1(A_13, B_12, k3_partfun1(C_14, A_13, B_12))=k1_tarski(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_13, B_12))) | ~v1_funct_2(C_14, A_13, B_12) | ~v1_funct_1(C_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.75/1.18  tff(c_38, plain, (k1_xboole_0='#skF_1' | k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))=k1_tarski('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_36])).
% 1.75/1.18  tff(c_41, plain, (k1_xboole_0='#skF_1' | k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_38])).
% 1.75/1.18  tff(c_42, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_10, c_41])).
% 1.75/1.18  tff(c_6, plain, (![B_5, C_6]: (k5_partfun1(k1_xboole_0, B_5, k3_partfun1(C_6, k1_xboole_0, B_5))=k1_tarski(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_5))) | ~v1_funct_2(C_6, k1_xboole_0, B_5) | ~v1_funct_1(C_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.75/1.18  tff(c_49, plain, (![B_15, C_16]: (k5_partfun1('#skF_1', B_15, k3_partfun1(C_16, '#skF_1', B_15))=k1_tarski(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_15))) | ~v1_funct_2(C_16, '#skF_1', B_15) | ~v1_funct_1(C_16))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_42, c_42, c_6])).
% 1.75/1.18  tff(c_51, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))=k1_tarski('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_49])).
% 1.75/1.18  tff(c_54, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_51])).
% 1.75/1.18  tff(c_56, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_54])).
% 1.75/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.18  
% 1.75/1.18  Inference rules
% 1.75/1.18  ----------------------
% 1.75/1.18  #Ref     : 0
% 1.75/1.18  #Sup     : 8
% 1.75/1.18  #Fact    : 0
% 1.75/1.18  #Define  : 0
% 1.75/1.18  #Split   : 0
% 1.75/1.18  #Chain   : 0
% 1.75/1.18  #Close   : 0
% 1.75/1.18  
% 1.75/1.18  Ordering : KBO
% 1.75/1.18  
% 1.75/1.18  Simplification rules
% 1.75/1.18  ----------------------
% 1.75/1.18  #Subsume      : 0
% 1.75/1.18  #Demod        : 9
% 1.75/1.18  #Tautology    : 6
% 1.75/1.18  #SimpNegUnit  : 2
% 1.75/1.18  #BackRed      : 2
% 1.75/1.18  
% 1.75/1.18  #Partial instantiations: 0
% 1.75/1.18  #Strategies tried      : 1
% 1.75/1.18  
% 1.75/1.18  Timing (in seconds)
% 1.75/1.18  ----------------------
% 1.75/1.19  Preprocessing        : 0.29
% 1.75/1.19  Parsing              : 0.16
% 1.75/1.19  CNF conversion       : 0.02
% 1.75/1.19  Main loop            : 0.08
% 1.75/1.19  Inferencing          : 0.03
% 1.75/1.19  Reduction            : 0.03
% 1.75/1.19  Demodulation         : 0.02
% 1.75/1.19  BG Simplification    : 0.01
% 1.75/1.19  Subsumption          : 0.01
% 1.75/1.19  Abstraction          : 0.01
% 1.75/1.19  MUC search           : 0.00
% 1.75/1.19  Cooper               : 0.00
% 1.75/1.19  Total                : 0.39
% 1.75/1.19  Index Insertion      : 0.00
% 1.75/1.19  Index Deletion       : 0.00
% 1.75/1.19  Index Matching       : 0.00
% 1.75/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
