%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:23 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :   44 (  48 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  61 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_84,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | k4_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_88,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_50])).

tff(c_28,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_98,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_110,plain,(
    ! [B_12] : k4_xboole_0(B_12,B_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_98])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_605,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(A_95,B_94)
      | ~ v1_zfmisc_1(B_94)
      | v1_xboole_0(B_94)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2118,plain,(
    ! [A_162,B_163] :
      ( k3_xboole_0(A_162,B_163) = A_162
      | ~ v1_zfmisc_1(A_162)
      | v1_xboole_0(A_162)
      | v1_xboole_0(k3_xboole_0(A_162,B_163)) ) ),
    inference(resolution,[status(thm)],[c_34,c_605])).

tff(c_52,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2121,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2118,c_52])).

tff(c_2145,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2121])).

tff(c_2146,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2145])).

tff(c_40,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2189,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2146,c_40])).

tff(c_2211,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2189])).

tff(c_2213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2211])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:28:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.77/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.67  
% 3.77/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.77/1.67  %$ r2_hidden > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 3.77/1.67  
% 3.77/1.67  %Foreground sorts:
% 3.77/1.67  
% 3.77/1.67  
% 3.77/1.67  %Background operators:
% 3.77/1.67  
% 3.77/1.67  
% 3.77/1.67  %Foreground operators:
% 3.77/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.77/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.77/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.77/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.77/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.77/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.77/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.77/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.77/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.77/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.77/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.77/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.77/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.77/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.77/1.67  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.77/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.77/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.77/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.77/1.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.77/1.67  
% 4.00/1.68  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.00/1.68  tff(f_89, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 4.00/1.68  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.00/1.68  tff(f_52, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.00/1.68  tff(f_77, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.00/1.68  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.00/1.68  tff(c_84, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | k4_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.00/1.68  tff(c_50, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.00/1.68  tff(c_88, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_50])).
% 4.00/1.68  tff(c_28, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.00/1.68  tff(c_98, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.00/1.68  tff(c_110, plain, (![B_12]: (k4_xboole_0(B_12, B_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_98])).
% 4.00/1.68  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.00/1.68  tff(c_54, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.00/1.68  tff(c_34, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.00/1.68  tff(c_605, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(A_95, B_94) | ~v1_zfmisc_1(B_94) | v1_xboole_0(B_94) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.00/1.68  tff(c_2118, plain, (![A_162, B_163]: (k3_xboole_0(A_162, B_163)=A_162 | ~v1_zfmisc_1(A_162) | v1_xboole_0(A_162) | v1_xboole_0(k3_xboole_0(A_162, B_163)))), inference(resolution, [status(thm)], [c_34, c_605])).
% 4.00/1.68  tff(c_52, plain, (~v1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.00/1.68  tff(c_2121, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2118, c_52])).
% 4.00/1.68  tff(c_2145, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4' | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2121])).
% 4.00/1.68  tff(c_2146, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_2145])).
% 4.00/1.68  tff(c_40, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.00/1.68  tff(c_2189, plain, (k4_xboole_0('#skF_4', '#skF_5')=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2146, c_40])).
% 4.00/1.68  tff(c_2211, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2189])).
% 4.00/1.68  tff(c_2213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_2211])).
% 4.00/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.00/1.68  
% 4.00/1.68  Inference rules
% 4.00/1.68  ----------------------
% 4.00/1.68  #Ref     : 0
% 4.00/1.68  #Sup     : 497
% 4.00/1.68  #Fact    : 6
% 4.00/1.68  #Define  : 0
% 4.00/1.68  #Split   : 3
% 4.00/1.68  #Chain   : 0
% 4.00/1.68  #Close   : 0
% 4.00/1.68  
% 4.00/1.68  Ordering : KBO
% 4.00/1.68  
% 4.00/1.68  Simplification rules
% 4.00/1.68  ----------------------
% 4.00/1.68  #Subsume      : 114
% 4.00/1.68  #Demod        : 304
% 4.00/1.68  #Tautology    : 258
% 4.00/1.68  #SimpNegUnit  : 9
% 4.00/1.68  #BackRed      : 2
% 4.00/1.68  
% 4.00/1.68  #Partial instantiations: 0
% 4.00/1.68  #Strategies tried      : 1
% 4.00/1.68  
% 4.00/1.68  Timing (in seconds)
% 4.00/1.68  ----------------------
% 4.00/1.69  Preprocessing        : 0.32
% 4.00/1.69  Parsing              : 0.16
% 4.00/1.69  CNF conversion       : 0.02
% 4.00/1.69  Main loop            : 0.60
% 4.00/1.69  Inferencing          : 0.23
% 4.00/1.69  Reduction            : 0.19
% 4.00/1.69  Demodulation         : 0.14
% 4.00/1.69  BG Simplification    : 0.03
% 4.00/1.69  Subsumption          : 0.11
% 4.00/1.69  Abstraction          : 0.04
% 4.00/1.69  MUC search           : 0.00
% 4.00/1.69  Cooper               : 0.00
% 4.00/1.69  Total                : 0.95
% 4.00/1.69  Index Insertion      : 0.00
% 4.00/1.69  Index Deletion       : 0.00
% 4.00/1.69  Index Matching       : 0.00
% 4.00/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
