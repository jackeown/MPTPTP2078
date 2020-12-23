%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:23 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  74 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [C_40,B_41,A_42] :
      ( r2_hidden(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_100,plain,(
    ! [A_1,B_41] :
      ( r2_hidden('#skF_1'(A_1),B_41)
      | ~ r1_tarski(A_1,B_41)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_94])).

tff(c_304,plain,(
    ! [A_61,B_62] :
      ( r2_hidden('#skF_1'(A_61),B_62)
      | ~ r1_tarski(A_61,B_62)
      | v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_4,c_94])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_101,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k3_subset_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_101])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_112,plain,(
    ! [D_15] :
      ( ~ r2_hidden(D_15,'#skF_7')
      | ~ r2_hidden(D_15,k3_subset_1('#skF_5','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_14])).

tff(c_901,plain,(
    ! [A_104] :
      ( ~ r2_hidden('#skF_1'(A_104),'#skF_7')
      | ~ r1_tarski(A_104,k3_subset_1('#skF_5','#skF_7'))
      | v1_xboole_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_304,c_112])).

tff(c_1322,plain,(
    ! [A_135] :
      ( ~ r1_tarski(A_135,k3_subset_1('#skF_5','#skF_7'))
      | ~ r1_tarski(A_135,'#skF_7')
      | v1_xboole_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_100,c_901])).

tff(c_1337,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_1322])).

tff(c_1346,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1337])).

tff(c_30,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1351,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1346,c_30])).

tff(c_1356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:06:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.55  
% 3.29/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.55  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 3.29/1.55  
% 3.29/1.55  %Foreground sorts:
% 3.29/1.55  
% 3.29/1.55  
% 3.29/1.55  %Background operators:
% 3.29/1.55  
% 3.29/1.55  
% 3.29/1.55  %Foreground operators:
% 3.29/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.29/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.29/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.29/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.29/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.29/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.29/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.29/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.55  
% 3.29/1.56  tff(f_67, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.29/1.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.29/1.56  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.29/1.56  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.29/1.56  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.29/1.56  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.29/1.56  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.29/1.56  tff(c_40, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.29/1.56  tff(c_38, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.29/1.56  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.56  tff(c_94, plain, (![C_40, B_41, A_42]: (r2_hidden(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.29/1.56  tff(c_100, plain, (![A_1, B_41]: (r2_hidden('#skF_1'(A_1), B_41) | ~r1_tarski(A_1, B_41) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_94])).
% 3.29/1.56  tff(c_304, plain, (![A_61, B_62]: (r2_hidden('#skF_1'(A_61), B_62) | ~r1_tarski(A_61, B_62) | v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_4, c_94])).
% 3.29/1.56  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.29/1.56  tff(c_101, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k3_subset_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.29/1.56  tff(c_105, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_42, c_101])).
% 3.29/1.56  tff(c_14, plain, (![D_15, B_11, A_10]: (~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.29/1.56  tff(c_112, plain, (![D_15]: (~r2_hidden(D_15, '#skF_7') | ~r2_hidden(D_15, k3_subset_1('#skF_5', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_105, c_14])).
% 3.29/1.56  tff(c_901, plain, (![A_104]: (~r2_hidden('#skF_1'(A_104), '#skF_7') | ~r1_tarski(A_104, k3_subset_1('#skF_5', '#skF_7')) | v1_xboole_0(A_104))), inference(resolution, [status(thm)], [c_304, c_112])).
% 3.29/1.56  tff(c_1322, plain, (![A_135]: (~r1_tarski(A_135, k3_subset_1('#skF_5', '#skF_7')) | ~r1_tarski(A_135, '#skF_7') | v1_xboole_0(A_135))), inference(resolution, [status(thm)], [c_100, c_901])).
% 3.29/1.56  tff(c_1337, plain, (~r1_tarski('#skF_6', '#skF_7') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_38, c_1322])).
% 3.29/1.56  tff(c_1346, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1337])).
% 3.29/1.56  tff(c_30, plain, (![A_16]: (k1_xboole_0=A_16 | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.29/1.56  tff(c_1351, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1346, c_30])).
% 3.29/1.56  tff(c_1356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1351])).
% 3.29/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.56  
% 3.29/1.56  Inference rules
% 3.29/1.56  ----------------------
% 3.29/1.56  #Ref     : 0
% 3.29/1.56  #Sup     : 288
% 3.29/1.56  #Fact    : 0
% 3.29/1.56  #Define  : 0
% 3.29/1.56  #Split   : 5
% 3.29/1.56  #Chain   : 0
% 3.29/1.56  #Close   : 0
% 3.29/1.56  
% 3.29/1.56  Ordering : KBO
% 3.29/1.56  
% 3.29/1.56  Simplification rules
% 3.29/1.56  ----------------------
% 3.29/1.56  #Subsume      : 56
% 3.29/1.56  #Demod        : 78
% 3.29/1.56  #Tautology    : 81
% 3.29/1.56  #SimpNegUnit  : 19
% 3.29/1.56  #BackRed      : 10
% 3.29/1.56  
% 3.29/1.56  #Partial instantiations: 0
% 3.29/1.56  #Strategies tried      : 1
% 3.29/1.56  
% 3.29/1.56  Timing (in seconds)
% 3.29/1.56  ----------------------
% 3.29/1.56  Preprocessing        : 0.32
% 3.29/1.56  Parsing              : 0.16
% 3.29/1.56  CNF conversion       : 0.02
% 3.29/1.57  Main loop            : 0.48
% 3.29/1.57  Inferencing          : 0.17
% 3.29/1.57  Reduction            : 0.13
% 3.29/1.57  Demodulation         : 0.09
% 3.29/1.57  BG Simplification    : 0.02
% 3.29/1.57  Subsumption          : 0.11
% 3.29/1.57  Abstraction          : 0.02
% 3.29/1.57  MUC search           : 0.00
% 3.29/1.57  Cooper               : 0.00
% 3.29/1.57  Total                : 0.83
% 3.29/1.57  Index Insertion      : 0.00
% 3.29/1.57  Index Deletion       : 0.00
% 3.29/1.57  Index Matching       : 0.00
% 3.29/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
