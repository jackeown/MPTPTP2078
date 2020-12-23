%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:27 EST 2020

% Result     : Theorem 16.49s
% Output     : CNFRefutation 16.49s
% Verified   : 
% Statistics : Number of formulae       :   60 (  65 expanded)
%              Number of leaves         :   52 (  54 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  25 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_21 > #skF_16 > #skF_18 > #skF_13 > #skF_19 > #skF_1 > #skF_25 > #skF_22 > #skF_8 > #skF_6 > #skF_4 > #skF_12 > #skF_3 > #skF_15 > #skF_7 > #skF_10 > #skF_5 > #skF_17 > #skF_11 > #skF_2 > #skF_24 > #skF_23 > #skF_14 > #skF_9 > #skF_20

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_21',type,(
    '#skF_21': $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_19',type,(
    '#skF_19': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_25',type,(
    '#skF_25': $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_22',type,(
    '#skF_22': $i > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_17',type,(
    '#skF_17': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_24',type,(
    '#skF_24': $i )).

tff('#skF_23',type,(
    '#skF_23': $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_20',type,(
    '#skF_20': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_339,axiom,(
    ! [A,B] : v1_relat_1(k1_tarski(k4_tarski(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_relat_1)).

tff(f_359,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( C = k1_tarski(k4_tarski(A,B))
       => ( k1_relat_1(C) = k1_tarski(A)
          & k2_relat_1(C) = k1_tarski(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

tff(f_388,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_577,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_220,plain,(
    ! [A_149,B_150] : v1_relat_1(k1_tarski(k4_tarski(A_149,B_150))) ),
    inference(cnfTransformation,[status(thm)],[f_339])).

tff(c_228,plain,(
    ! [A_153,B_154] :
      ( k1_relat_1(k1_tarski(k4_tarski(A_153,B_154))) = k1_tarski(A_153)
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_359])).

tff(c_320,plain,(
    ! [A_153,B_154] : k1_relat_1(k1_tarski(k4_tarski(A_153,B_154))) = k1_tarski(A_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_228])).

tff(c_1394,plain,(
    ! [A_435,B_436,C_437] : k4_tarski(k4_tarski(A_435,B_436),C_437) = k3_mcart_1(A_435,B_436,C_437) ),
    inference(cnfTransformation,[status(thm)],[f_388])).

tff(c_1406,plain,(
    ! [A_435,B_436,C_437] : k1_relat_1(k1_tarski(k3_mcart_1(A_435,B_436,C_437))) = k1_tarski(k4_tarski(A_435,B_436)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_320])).

tff(c_318,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_23','#skF_24','#skF_25')))) != k1_tarski('#skF_23') ),
    inference(cnfTransformation,[status(thm)],[f_577])).

tff(c_62598,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_23','#skF_24'))) != k1_tarski('#skF_23') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1406,c_318])).

tff(c_62601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_62598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.49/8.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.49/8.40  
% 16.49/8.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.49/8.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_21 > #skF_16 > #skF_18 > #skF_13 > #skF_19 > #skF_1 > #skF_25 > #skF_22 > #skF_8 > #skF_6 > #skF_4 > #skF_12 > #skF_3 > #skF_15 > #skF_7 > #skF_10 > #skF_5 > #skF_17 > #skF_11 > #skF_2 > #skF_24 > #skF_23 > #skF_14 > #skF_9 > #skF_20
% 16.49/8.41  
% 16.49/8.41  %Foreground sorts:
% 16.49/8.41  
% 16.49/8.41  
% 16.49/8.41  %Background operators:
% 16.49/8.41  
% 16.49/8.41  
% 16.49/8.41  %Foreground operators:
% 16.49/8.41  tff('#skF_21', type, '#skF_21': $i > $i).
% 16.49/8.41  tff('#skF_16', type, '#skF_16': $i > $i).
% 16.49/8.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.49/8.41  tff('#skF_18', type, '#skF_18': $i > $i).
% 16.49/8.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.49/8.41  tff('#skF_13', type, '#skF_13': ($i * $i * $i * $i) > $i).
% 16.49/8.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.49/8.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.49/8.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.49/8.41  tff('#skF_19', type, '#skF_19': $i > $i).
% 16.49/8.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.49/8.41  tff('#skF_25', type, '#skF_25': $i).
% 16.49/8.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.49/8.41  tff('#skF_22', type, '#skF_22': $i > $i).
% 16.49/8.41  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 16.49/8.41  tff('#skF_8', type, '#skF_8': $i > $i).
% 16.49/8.41  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i) > $i).
% 16.49/8.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 16.49/8.41  tff('#skF_12', type, '#skF_12': ($i * $i * $i * $i) > $i).
% 16.49/8.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.49/8.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.49/8.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.49/8.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.49/8.41  tff('#skF_15', type, '#skF_15': $i > $i).
% 16.49/8.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.49/8.41  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i * $i) > $i).
% 16.49/8.41  tff('#skF_10', type, '#skF_10': $i > $i).
% 16.49/8.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 16.49/8.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.49/8.41  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 16.49/8.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.49/8.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.49/8.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.49/8.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.49/8.41  tff('#skF_17', type, '#skF_17': $i > $i).
% 16.49/8.41  tff('#skF_11', type, '#skF_11': $i > $i).
% 16.49/8.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.49/8.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.49/8.41  tff('#skF_24', type, '#skF_24': $i).
% 16.49/8.41  tff('#skF_23', type, '#skF_23': $i).
% 16.49/8.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.49/8.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.49/8.41  tff('#skF_14', type, '#skF_14': ($i * $i * $i * $i) > $i).
% 16.49/8.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.49/8.41  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 16.49/8.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.49/8.41  tff('#skF_20', type, '#skF_20': $i > $i).
% 16.49/8.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.49/8.41  
% 16.49/8.41  tff(f_339, axiom, (![A, B]: v1_relat_1(k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_relat_1)).
% 16.49/8.41  tff(f_359, axiom, (![A, B, C]: (v1_relat_1(C) => ((C = k1_tarski(k4_tarski(A, B))) => ((k1_relat_1(C) = k1_tarski(A)) & (k2_relat_1(C) = k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relat_1)).
% 16.49/8.41  tff(f_388, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 16.49/8.41  tff(f_577, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_mcart_1)).
% 16.49/8.41  tff(c_220, plain, (![A_149, B_150]: (v1_relat_1(k1_tarski(k4_tarski(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_339])).
% 16.49/8.41  tff(c_228, plain, (![A_153, B_154]: (k1_relat_1(k1_tarski(k4_tarski(A_153, B_154)))=k1_tarski(A_153) | ~v1_relat_1(k1_tarski(k4_tarski(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_359])).
% 16.49/8.41  tff(c_320, plain, (![A_153, B_154]: (k1_relat_1(k1_tarski(k4_tarski(A_153, B_154)))=k1_tarski(A_153))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_228])).
% 16.49/8.41  tff(c_1394, plain, (![A_435, B_436, C_437]: (k4_tarski(k4_tarski(A_435, B_436), C_437)=k3_mcart_1(A_435, B_436, C_437))), inference(cnfTransformation, [status(thm)], [f_388])).
% 16.49/8.41  tff(c_1406, plain, (![A_435, B_436, C_437]: (k1_relat_1(k1_tarski(k3_mcart_1(A_435, B_436, C_437)))=k1_tarski(k4_tarski(A_435, B_436)))), inference(superposition, [status(thm), theory('equality')], [c_1394, c_320])).
% 16.49/8.41  tff(c_318, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_23', '#skF_24', '#skF_25'))))!=k1_tarski('#skF_23')), inference(cnfTransformation, [status(thm)], [f_577])).
% 16.49/8.41  tff(c_62598, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_23', '#skF_24')))!=k1_tarski('#skF_23')), inference(demodulation, [status(thm), theory('equality')], [c_1406, c_318])).
% 16.49/8.41  tff(c_62601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_320, c_62598])).
% 16.49/8.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.49/8.41  
% 16.49/8.41  Inference rules
% 16.49/8.41  ----------------------
% 16.49/8.41  #Ref     : 8
% 16.49/8.41  #Sup     : 7987
% 16.49/8.41  #Fact    : 52
% 16.49/8.41  #Define  : 0
% 16.49/8.41  #Split   : 1
% 16.49/8.41  #Chain   : 0
% 16.49/8.41  #Close   : 0
% 16.49/8.41  
% 16.49/8.41  Ordering : KBO
% 16.49/8.41  
% 16.49/8.41  Simplification rules
% 16.49/8.41  ----------------------
% 16.49/8.41  #Subsume      : 2198
% 16.49/8.41  #Demod        : 3658
% 16.49/8.41  #Tautology    : 2551
% 16.49/8.41  #SimpNegUnit  : 437
% 16.49/8.41  #BackRed      : 10
% 16.49/8.41  
% 16.49/8.41  #Partial instantiations: 95912
% 16.49/8.41  #Strategies tried      : 1
% 16.49/8.41  
% 16.49/8.41  Timing (in seconds)
% 16.49/8.41  ----------------------
% 16.49/8.42  Preprocessing        : 0.53
% 16.49/8.42  Parsing              : 0.26
% 16.49/8.42  CNF conversion       : 0.05
% 16.49/8.42  Main loop            : 7.18
% 16.49/8.42  Inferencing          : 3.08
% 16.49/8.42  Reduction            : 2.54
% 16.49/8.42  Demodulation         : 2.07
% 16.49/8.42  BG Simplification    : 0.18
% 16.49/8.42  Subsumption          : 1.08
% 16.49/8.42  Abstraction          : 0.21
% 16.49/8.42  MUC search           : 0.00
% 16.49/8.42  Cooper               : 0.00
% 16.49/8.42  Total                : 7.73
% 16.49/8.42  Index Insertion      : 0.00
% 16.49/8.42  Index Deletion       : 0.00
% 16.49/8.42  Index Matching       : 0.00
% 16.49/8.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
