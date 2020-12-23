%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:03 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  77 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_40,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_38,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_355,plain,(
    ! [A_93,B_94,C_95] :
      ( r1_tarski(k2_tarski(A_93,B_94),C_95)
      | ~ r2_hidden(B_94,C_95)
      | ~ r2_hidden(A_93,C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_465,plain,(
    ! [A_107,C_108] :
      ( r1_tarski(k1_tarski(A_107),C_108)
      | ~ r2_hidden(A_107,C_108)
      | ~ r2_hidden(A_107,C_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_355])).

tff(c_26,plain,(
    ! [A_21] : r1_tarski(k1_tarski(A_21),k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_90,plain,(
    ! [A_41,C_42,B_43] :
      ( r2_hidden(A_41,C_42)
      | ~ r1_tarski(k2_tarski(A_41,B_43),C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_99,plain,(
    ! [A_44,C_45] :
      ( r2_hidden(A_44,C_45)
      | ~ r1_tarski(k1_tarski(A_44),C_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_90])).

tff(c_109,plain,(
    ! [A_46] : r2_hidden(A_46,k1_zfmisc_1(A_46)) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [A_46] : ~ v1_xboole_0(k1_zfmisc_1(A_46)) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(k1_zfmisc_1(A_19),k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_108,plain,(
    ! [A_21] : r2_hidden(A_21,k1_zfmisc_1(A_21)) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_182,plain,(
    ! [C_67,B_68,A_69] :
      ( r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_309,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(A_87,B_88)
      | ~ r1_tarski(k1_zfmisc_1(A_87),B_88) ) ),
    inference(resolution,[status(thm)],[c_108,c_182])).

tff(c_327,plain,(
    ! [A_89,B_90] :
      ( r2_hidden(A_89,k1_zfmisc_1(B_90))
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_24,c_309])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( m1_subset_1(B_23,A_22)
      | ~ r2_hidden(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_336,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1(A_89,k1_zfmisc_1(B_90))
      | v1_xboole_0(k1_zfmisc_1(B_90))
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_327,c_28])).

tff(c_346,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1(A_91,k1_zfmisc_1(B_92))
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_336])).

tff(c_36,plain,(
    ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_354,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_346,c_36])).

tff(c_473,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_465,c_354])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:55:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.35  
% 2.28/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.35  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.28/1.35  
% 2.28/1.35  %Foreground sorts:
% 2.28/1.35  
% 2.28/1.35  
% 2.28/1.35  %Background operators:
% 2.28/1.35  
% 2.28/1.35  
% 2.28/1.35  %Foreground operators:
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.28/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.35  
% 2.46/1.36  tff(f_74, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.46/1.36  tff(f_40, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.46/1.36  tff(f_50, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.46/1.36  tff(f_56, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 2.46/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.46/1.36  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.46/1.36  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.46/1.36  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.46/1.36  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.46/1.36  tff(c_12, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.46/1.36  tff(c_355, plain, (![A_93, B_94, C_95]: (r1_tarski(k2_tarski(A_93, B_94), C_95) | ~r2_hidden(B_94, C_95) | ~r2_hidden(A_93, C_95))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.46/1.36  tff(c_465, plain, (![A_107, C_108]: (r1_tarski(k1_tarski(A_107), C_108) | ~r2_hidden(A_107, C_108) | ~r2_hidden(A_107, C_108))), inference(superposition, [status(thm), theory('equality')], [c_12, c_355])).
% 2.46/1.36  tff(c_26, plain, (![A_21]: (r1_tarski(k1_tarski(A_21), k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.36  tff(c_90, plain, (![A_41, C_42, B_43]: (r2_hidden(A_41, C_42) | ~r1_tarski(k2_tarski(A_41, B_43), C_42))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.46/1.36  tff(c_99, plain, (![A_44, C_45]: (r2_hidden(A_44, C_45) | ~r1_tarski(k1_tarski(A_44), C_45))), inference(superposition, [status(thm), theory('equality')], [c_12, c_90])).
% 2.46/1.36  tff(c_109, plain, (![A_46]: (r2_hidden(A_46, k1_zfmisc_1(A_46)))), inference(resolution, [status(thm)], [c_26, c_99])).
% 2.46/1.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.36  tff(c_113, plain, (![A_46]: (~v1_xboole_0(k1_zfmisc_1(A_46)))), inference(resolution, [status(thm)], [c_109, c_2])).
% 2.46/1.36  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(k1_zfmisc_1(A_19), k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.46/1.36  tff(c_108, plain, (![A_21]: (r2_hidden(A_21, k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_26, c_99])).
% 2.46/1.36  tff(c_182, plain, (![C_67, B_68, A_69]: (r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.46/1.36  tff(c_309, plain, (![A_87, B_88]: (r2_hidden(A_87, B_88) | ~r1_tarski(k1_zfmisc_1(A_87), B_88))), inference(resolution, [status(thm)], [c_108, c_182])).
% 2.46/1.36  tff(c_327, plain, (![A_89, B_90]: (r2_hidden(A_89, k1_zfmisc_1(B_90)) | ~r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_24, c_309])).
% 2.46/1.36  tff(c_28, plain, (![B_23, A_22]: (m1_subset_1(B_23, A_22) | ~r2_hidden(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.46/1.36  tff(c_336, plain, (![A_89, B_90]: (m1_subset_1(A_89, k1_zfmisc_1(B_90)) | v1_xboole_0(k1_zfmisc_1(B_90)) | ~r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_327, c_28])).
% 2.46/1.36  tff(c_346, plain, (![A_91, B_92]: (m1_subset_1(A_91, k1_zfmisc_1(B_92)) | ~r1_tarski(A_91, B_92))), inference(negUnitSimplification, [status(thm)], [c_113, c_336])).
% 2.46/1.36  tff(c_36, plain, (~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.46/1.36  tff(c_354, plain, (~r1_tarski(k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_346, c_36])).
% 2.46/1.36  tff(c_473, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_465, c_354])).
% 2.46/1.36  tff(c_483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_473])).
% 2.46/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.36  
% 2.46/1.36  Inference rules
% 2.46/1.36  ----------------------
% 2.46/1.36  #Ref     : 0
% 2.46/1.36  #Sup     : 97
% 2.46/1.36  #Fact    : 0
% 2.46/1.36  #Define  : 0
% 2.46/1.36  #Split   : 1
% 2.46/1.36  #Chain   : 0
% 2.46/1.36  #Close   : 0
% 2.46/1.36  
% 2.46/1.36  Ordering : KBO
% 2.46/1.36  
% 2.46/1.36  Simplification rules
% 2.46/1.36  ----------------------
% 2.46/1.36  #Subsume      : 32
% 2.46/1.36  #Demod        : 7
% 2.46/1.36  #Tautology    : 21
% 2.46/1.36  #SimpNegUnit  : 12
% 2.46/1.36  #BackRed      : 0
% 2.46/1.36  
% 2.46/1.36  #Partial instantiations: 0
% 2.46/1.36  #Strategies tried      : 1
% 2.46/1.36  
% 2.46/1.36  Timing (in seconds)
% 2.46/1.36  ----------------------
% 2.46/1.36  Preprocessing        : 0.29
% 2.46/1.36  Parsing              : 0.15
% 2.46/1.36  CNF conversion       : 0.02
% 2.46/1.36  Main loop            : 0.25
% 2.46/1.36  Inferencing          : 0.10
% 2.46/1.36  Reduction            : 0.07
% 2.46/1.37  Demodulation         : 0.04
% 2.46/1.37  BG Simplification    : 0.02
% 2.46/1.37  Subsumption          : 0.05
% 2.46/1.37  Abstraction          : 0.01
% 2.46/1.37  MUC search           : 0.00
% 2.46/1.37  Cooper               : 0.00
% 2.46/1.37  Total                : 0.57
% 2.46/1.37  Index Insertion      : 0.00
% 2.46/1.37  Index Deletion       : 0.00
% 2.46/1.37  Index Matching       : 0.00
% 2.46/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
