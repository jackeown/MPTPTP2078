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
% DateTime   : Thu Dec  3 09:56:27 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  78 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_27,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_35,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_27])).

tff(c_63,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,k3_xboole_0(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [C_28] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_28,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_63])).

tff(c_75,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_20,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_166,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k3_subset_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_170,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_166])).

tff(c_14,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_81,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_xboole_0(A_31,C_32)
      | ~ r1_xboole_0(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_84,plain,(
    ! [A_31,B_16,A_15] :
      ( r1_xboole_0(A_31,B_16)
      | ~ r1_tarski(A_31,k4_xboole_0(A_15,B_16)) ) ),
    inference(resolution,[status(thm)],[c_14,c_81])).

tff(c_209,plain,(
    ! [A_44] :
      ( r1_xboole_0(A_44,'#skF_5')
      | ~ r1_tarski(A_44,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_84])).

tff(c_212,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_209])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_212])).

tff(c_219,plain,(
    ! [C_45] : ~ r2_hidden(C_45,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_223,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_219])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:58:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.29  
% 1.93/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 1.93/1.29  
% 1.93/1.29  %Foreground sorts:
% 1.93/1.29  
% 1.93/1.29  
% 1.93/1.29  %Background operators:
% 1.93/1.29  
% 1.93/1.29  
% 1.93/1.29  %Foreground operators:
% 1.93/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.93/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.29  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.93/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.29  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.29  
% 1.93/1.30  tff(f_74, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 1.93/1.30  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.93/1.30  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.93/1.30  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.93/1.30  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.93/1.30  tff(f_61, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.93/1.30  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.93/1.30  tff(c_18, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.93/1.30  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.30  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.93/1.30  tff(c_27, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.30  tff(c_35, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_22, c_27])).
% 1.93/1.30  tff(c_63, plain, (![A_26, B_27, C_28]: (~r1_xboole_0(A_26, B_27) | ~r2_hidden(C_28, k3_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.30  tff(c_69, plain, (![C_28]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_28, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_35, c_63])).
% 1.93/1.30  tff(c_75, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_69])).
% 1.93/1.30  tff(c_20, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.93/1.30  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.93/1.30  tff(c_166, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k3_subset_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.93/1.30  tff(c_170, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_166])).
% 1.93/1.30  tff(c_14, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.30  tff(c_81, plain, (![A_31, C_32, B_33]: (r1_xboole_0(A_31, C_32) | ~r1_xboole_0(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.30  tff(c_84, plain, (![A_31, B_16, A_15]: (r1_xboole_0(A_31, B_16) | ~r1_tarski(A_31, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_14, c_81])).
% 1.93/1.30  tff(c_209, plain, (![A_44]: (r1_xboole_0(A_44, '#skF_5') | ~r1_tarski(A_44, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_170, c_84])).
% 1.93/1.30  tff(c_212, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_20, c_209])).
% 1.93/1.30  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_212])).
% 1.93/1.30  tff(c_219, plain, (![C_45]: (~r2_hidden(C_45, '#skF_4'))), inference(splitRight, [status(thm)], [c_69])).
% 1.93/1.30  tff(c_223, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6, c_219])).
% 1.93/1.30  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_223])).
% 1.93/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.30  
% 1.93/1.30  Inference rules
% 1.93/1.30  ----------------------
% 1.93/1.30  #Ref     : 0
% 1.93/1.30  #Sup     : 53
% 1.93/1.30  #Fact    : 0
% 1.93/1.30  #Define  : 0
% 1.93/1.30  #Split   : 2
% 1.93/1.30  #Chain   : 0
% 1.93/1.30  #Close   : 0
% 1.93/1.30  
% 1.93/1.30  Ordering : KBO
% 1.93/1.30  
% 1.93/1.30  Simplification rules
% 1.93/1.30  ----------------------
% 1.93/1.30  #Subsume      : 2
% 1.93/1.30  #Demod        : 9
% 1.93/1.30  #Tautology    : 25
% 1.93/1.30  #SimpNegUnit  : 7
% 1.93/1.30  #BackRed      : 0
% 1.93/1.30  
% 1.93/1.30  #Partial instantiations: 0
% 1.93/1.30  #Strategies tried      : 1
% 1.93/1.30  
% 1.93/1.30  Timing (in seconds)
% 1.93/1.30  ----------------------
% 2.13/1.31  Preprocessing        : 0.31
% 2.13/1.31  Parsing              : 0.17
% 2.13/1.31  CNF conversion       : 0.02
% 2.13/1.31  Main loop            : 0.18
% 2.13/1.31  Inferencing          : 0.07
% 2.13/1.31  Reduction            : 0.06
% 2.13/1.31  Demodulation         : 0.04
% 2.13/1.31  BG Simplification    : 0.01
% 2.13/1.31  Subsumption          : 0.03
% 2.13/1.31  Abstraction          : 0.01
% 2.13/1.31  MUC search           : 0.00
% 2.13/1.31  Cooper               : 0.00
% 2.13/1.31  Total                : 0.52
% 2.13/1.31  Index Insertion      : 0.00
% 2.13/1.31  Index Deletion       : 0.00
% 2.13/1.31  Index Matching       : 0.00
% 2.13/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
