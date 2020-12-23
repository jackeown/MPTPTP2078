%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:24 EST 2020

% Result     : Theorem 6.48s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  62 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4])).

tff(c_1277,plain,(
    ! [D_1212,C_1213,B_1214,A_1215] :
      ( r2_hidden(k1_funct_1(D_1212,C_1213),B_1214)
      | k1_xboole_0 = B_1214
      | ~ r2_hidden(C_1213,A_1215)
      | ~ m1_subset_1(D_1212,k1_zfmisc_1(k2_zfmisc_1(A_1215,B_1214)))
      | ~ v1_funct_2(D_1212,A_1215,B_1214)
      | ~ v1_funct_1(D_1212) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7766,plain,(
    ! [D_2923,A_2924,B_2925] :
      ( r2_hidden(k1_funct_1(D_2923,A_2924),B_2925)
      | k1_xboole_0 = B_2925
      | ~ m1_subset_1(D_2923,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_2924),B_2925)))
      | ~ v1_funct_2(D_2923,k1_tarski(A_2924),B_2925)
      | ~ v1_funct_1(D_2923) ) ),
    inference(resolution,[status(thm)],[c_40,c_1277])).

tff(c_7781,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_7766])).

tff(c_7784,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_7781])).

tff(c_7786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_7784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.48/2.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.36  
% 6.77/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.37  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 6.77/2.37  
% 6.77/2.37  %Foreground sorts:
% 6.77/2.37  
% 6.77/2.37  
% 6.77/2.37  %Background operators:
% 6.77/2.37  
% 6.77/2.37  
% 6.77/2.37  %Foreground operators:
% 6.77/2.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.77/2.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.77/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.77/2.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.77/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.77/2.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.77/2.37  tff('#skF_5', type, '#skF_5': $i).
% 6.77/2.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.77/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.77/2.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.77/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.77/2.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.77/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.77/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.77/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.77/2.37  
% 6.77/2.37  tff(f_60, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 6.77/2.37  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.77/2.37  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.77/2.37  tff(f_48, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 6.77/2.37  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.77/2.37  tff(c_24, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.77/2.37  tff(c_32, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.77/2.37  tff(c_30, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.77/2.37  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.77/2.37  tff(c_34, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.77/2.37  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.77/2.37  tff(c_40, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4])).
% 6.77/2.37  tff(c_1277, plain, (![D_1212, C_1213, B_1214, A_1215]: (r2_hidden(k1_funct_1(D_1212, C_1213), B_1214) | k1_xboole_0=B_1214 | ~r2_hidden(C_1213, A_1215) | ~m1_subset_1(D_1212, k1_zfmisc_1(k2_zfmisc_1(A_1215, B_1214))) | ~v1_funct_2(D_1212, A_1215, B_1214) | ~v1_funct_1(D_1212))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.77/2.37  tff(c_7766, plain, (![D_2923, A_2924, B_2925]: (r2_hidden(k1_funct_1(D_2923, A_2924), B_2925) | k1_xboole_0=B_2925 | ~m1_subset_1(D_2923, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_2924), B_2925))) | ~v1_funct_2(D_2923, k1_tarski(A_2924), B_2925) | ~v1_funct_1(D_2923))), inference(resolution, [status(thm)], [c_40, c_1277])).
% 6.77/2.37  tff(c_7781, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_7766])).
% 6.77/2.37  tff(c_7784, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_7781])).
% 6.77/2.37  tff(c_7786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_7784])).
% 6.77/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.37  
% 6.77/2.37  Inference rules
% 6.77/2.37  ----------------------
% 6.77/2.37  #Ref     : 0
% 6.77/2.37  #Sup     : 1427
% 6.77/2.37  #Fact    : 44
% 6.77/2.37  #Define  : 0
% 6.77/2.37  #Split   : 4
% 6.77/2.37  #Chain   : 0
% 6.77/2.37  #Close   : 0
% 6.77/2.37  
% 6.77/2.37  Ordering : KBO
% 6.77/2.37  
% 6.77/2.37  Simplification rules
% 6.77/2.37  ----------------------
% 6.77/2.37  #Subsume      : 618
% 6.77/2.37  #Demod        : 51
% 6.77/2.37  #Tautology    : 508
% 6.77/2.37  #SimpNegUnit  : 153
% 6.77/2.37  #BackRed      : 0
% 6.77/2.37  
% 6.77/2.37  #Partial instantiations: 2211
% 6.77/2.37  #Strategies tried      : 1
% 6.77/2.37  
% 6.77/2.37  Timing (in seconds)
% 6.77/2.37  ----------------------
% 6.77/2.38  Preprocessing        : 0.31
% 6.77/2.38  Parsing              : 0.15
% 6.77/2.38  CNF conversion       : 0.02
% 6.77/2.38  Main loop            : 1.32
% 6.77/2.38  Inferencing          : 0.57
% 6.77/2.38  Reduction            : 0.31
% 6.77/2.38  Demodulation         : 0.21
% 6.77/2.38  BG Simplification    : 0.06
% 6.77/2.38  Subsumption          : 0.31
% 6.77/2.38  Abstraction          : 0.08
% 6.77/2.38  MUC search           : 0.00
% 6.77/2.38  Cooper               : 0.00
% 6.77/2.38  Total                : 1.64
% 6.77/2.38  Index Insertion      : 0.00
% 6.77/2.38  Index Deletion       : 0.00
% 6.77/2.38  Index Matching       : 0.00
% 6.77/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
