%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:09 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   35 (  55 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  70 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_6,plain,(
    ! [A_4] : k1_subset_1(A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18])).

tff(c_29,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_2])).

tff(c_12,plain,
    ( k1_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_29,c_19])).

tff(c_55,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_54,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_69,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = k3_subset_1(A_15,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_69])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k4_xboole_0(B_3,A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_4])).

tff(c_81,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_77])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:38:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.19  
% 1.66/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.19  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.66/1.19  
% 1.66/1.19  %Foreground sorts:
% 1.66/1.19  
% 1.66/1.19  
% 1.66/1.19  %Background operators:
% 1.66/1.19  
% 1.66/1.19  
% 1.66/1.19  %Foreground operators:
% 1.66/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.19  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.66/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.66/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.19  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.66/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.66/1.19  
% 1.66/1.21  tff(f_33, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 1.66/1.21  tff(f_44, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 1.66/1.21  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.66/1.21  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.66/1.21  tff(f_31, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.66/1.21  tff(c_6, plain, (![A_4]: (k1_subset_1(A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.21  tff(c_18, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.66/1.21  tff(c_20, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_18])).
% 1.66/1.21  tff(c_29, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_20])).
% 1.66/1.21  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.21  tff(c_30, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_2])).
% 1.66/1.21  tff(c_12, plain, (k1_subset_1('#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.66/1.21  tff(c_19, plain, (k1_xboole_0!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12])).
% 1.66/1.21  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_29, c_19])).
% 1.66/1.21  tff(c_55, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_20])).
% 1.66/1.21  tff(c_54, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_20])).
% 1.66/1.21  tff(c_10, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.66/1.21  tff(c_69, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=k3_subset_1(A_15, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.66/1.21  tff(c_73, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_10, c_69])).
% 1.66/1.21  tff(c_4, plain, (![A_2, B_3]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k4_xboole_0(B_3, A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.21  tff(c_77, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_4])).
% 1.66/1.21  tff(c_81, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_77])).
% 1.66/1.21  tff(c_83, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_81])).
% 1.66/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.21  
% 1.66/1.21  Inference rules
% 1.66/1.21  ----------------------
% 1.66/1.21  #Ref     : 0
% 1.66/1.21  #Sup     : 12
% 1.66/1.21  #Fact    : 0
% 1.66/1.21  #Define  : 0
% 1.66/1.21  #Split   : 2
% 1.66/1.21  #Chain   : 0
% 1.66/1.21  #Close   : 0
% 1.66/1.21  
% 1.66/1.21  Ordering : KBO
% 1.66/1.21  
% 1.66/1.21  Simplification rules
% 1.66/1.21  ----------------------
% 1.66/1.21  #Subsume      : 1
% 1.66/1.21  #Demod        : 10
% 1.66/1.21  #Tautology    : 12
% 1.66/1.21  #SimpNegUnit  : 1
% 1.66/1.21  #BackRed      : 2
% 1.66/1.21  
% 1.66/1.21  #Partial instantiations: 0
% 1.66/1.21  #Strategies tried      : 1
% 1.66/1.21  
% 1.66/1.21  Timing (in seconds)
% 1.66/1.21  ----------------------
% 1.66/1.21  Preprocessing        : 0.24
% 1.66/1.21  Parsing              : 0.13
% 1.66/1.21  CNF conversion       : 0.01
% 1.66/1.21  Main loop            : 0.12
% 1.66/1.21  Inferencing          : 0.04
% 1.66/1.21  Reduction            : 0.04
% 1.66/1.21  Demodulation         : 0.04
% 1.66/1.21  BG Simplification    : 0.01
% 1.66/1.21  Subsumption          : 0.02
% 1.66/1.21  Abstraction          : 0.01
% 1.66/1.21  MUC search           : 0.00
% 1.66/1.21  Cooper               : 0.00
% 1.66/1.21  Total                : 0.39
% 1.66/1.21  Index Insertion      : 0.00
% 1.66/1.21  Index Deletion       : 0.00
% 1.66/1.21  Index Matching       : 0.00
% 1.66/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
