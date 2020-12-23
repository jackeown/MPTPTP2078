%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:22 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  64 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [A_23,B_24] :
      ( k4_tarski(k1_mcart_1(A_23),k2_mcart_1(A_23)) = A_23
      | ~ r2_hidden(A_23,B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,(
    ! [A_25,B_26] :
      ( k4_tarski(k1_mcart_1(A_25),k2_mcart_1(A_25)) = A_25
      | ~ v1_relat_1(B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_12,c_75])).

tff(c_81,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_79])).

tff(c_84,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_81])).

tff(c_85,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_53,plain,(
    ! [B_16,A_17] :
      ( ~ v1_xboole_0(B_16)
      | B_16 = A_17
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_2,c_53])).

tff(c_91,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_56])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_6])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.16  
% 1.62/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.16  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.62/1.16  
% 1.62/1.16  %Foreground sorts:
% 1.62/1.16  
% 1.62/1.16  
% 1.62/1.16  %Background operators:
% 1.62/1.16  
% 1.62/1.16  
% 1.62/1.16  %Foreground operators:
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.16  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.62/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.62/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.62/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.62/1.16  
% 1.62/1.17  tff(f_68, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 1.62/1.17  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.62/1.17  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.62/1.17  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.62/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.62/1.17  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.62/1.17  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.62/1.17  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.62/1.17  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.62/1.17  tff(c_18, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.62/1.17  tff(c_14, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.62/1.17  tff(c_20, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.62/1.17  tff(c_12, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.62/1.17  tff(c_75, plain, (![A_23, B_24]: (k4_tarski(k1_mcart_1(A_23), k2_mcart_1(A_23))=A_23 | ~r2_hidden(A_23, B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.62/1.17  tff(c_79, plain, (![A_25, B_26]: (k4_tarski(k1_mcart_1(A_25), k2_mcart_1(A_25))=A_25 | ~v1_relat_1(B_26) | v1_xboole_0(B_26) | ~m1_subset_1(A_25, B_26))), inference(resolution, [status(thm)], [c_12, c_75])).
% 1.62/1.17  tff(c_81, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_79])).
% 1.62/1.17  tff(c_84, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_81])).
% 1.62/1.17  tff(c_85, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_84])).
% 1.62/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.62/1.17  tff(c_53, plain, (![B_16, A_17]: (~v1_xboole_0(B_16) | B_16=A_17 | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.62/1.17  tff(c_56, plain, (![A_17]: (k1_xboole_0=A_17 | ~v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_2, c_53])).
% 1.62/1.17  tff(c_91, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_85, c_56])).
% 1.62/1.17  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.17  tff(c_99, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_91, c_6])).
% 1.62/1.17  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_99])).
% 1.62/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.17  
% 1.62/1.17  Inference rules
% 1.62/1.17  ----------------------
% 1.62/1.17  #Ref     : 0
% 1.62/1.17  #Sup     : 20
% 1.62/1.17  #Fact    : 0
% 1.62/1.17  #Define  : 0
% 1.62/1.17  #Split   : 0
% 1.62/1.17  #Chain   : 0
% 1.62/1.17  #Close   : 0
% 1.62/1.17  
% 1.62/1.17  Ordering : KBO
% 1.62/1.17  
% 1.62/1.17  Simplification rules
% 1.62/1.17  ----------------------
% 1.62/1.17  #Subsume      : 0
% 1.62/1.17  #Demod        : 5
% 1.62/1.17  #Tautology    : 12
% 1.62/1.17  #SimpNegUnit  : 2
% 1.62/1.17  #BackRed      : 2
% 1.62/1.17  
% 1.62/1.17  #Partial instantiations: 0
% 1.62/1.17  #Strategies tried      : 1
% 1.62/1.17  
% 1.62/1.17  Timing (in seconds)
% 1.62/1.17  ----------------------
% 1.62/1.17  Preprocessing        : 0.27
% 1.62/1.17  Parsing              : 0.14
% 1.62/1.17  CNF conversion       : 0.02
% 1.62/1.17  Main loop            : 0.10
% 1.62/1.17  Inferencing          : 0.04
% 1.62/1.17  Reduction            : 0.03
% 1.62/1.17  Demodulation         : 0.02
% 1.62/1.17  BG Simplification    : 0.01
% 1.62/1.17  Subsumption          : 0.01
% 1.62/1.17  Abstraction          : 0.00
% 1.62/1.17  MUC search           : 0.00
% 1.62/1.17  Cooper               : 0.00
% 1.62/1.17  Total                : 0.40
% 1.62/1.17  Index Insertion      : 0.00
% 1.62/1.17  Index Deletion       : 0.00
% 1.62/1.17  Index Matching       : 0.00
% 1.62/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
