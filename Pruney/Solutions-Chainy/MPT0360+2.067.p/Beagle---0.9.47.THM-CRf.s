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
% DateTime   : Thu Dec  3 09:56:27 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  73 expanded)
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

tff(f_72,negated_conjecture,(
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

tff(f_59,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_26])).

tff(c_62,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,k3_xboole_0(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [C_24] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_24,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_62])).

tff(c_74,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_20,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_99,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k3_subset_1(A_34,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_103,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_99])).

tff(c_10,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_xboole_0(A_10,C_12)
      | ~ r1_tarski(A_10,k4_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_114,plain,(
    ! [A_36] :
      ( r1_xboole_0(A_36,'#skF_5')
      | ~ r1_tarski(A_36,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_10])).

tff(c_117,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_114])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_117])).

tff(c_124,plain,(
    ! [C_37] : ~ r2_hidden(C_37,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_128,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:37:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 1.91/1.21  
% 1.91/1.21  %Foreground sorts:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Background operators:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Foreground operators:
% 1.91/1.21  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.91/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.91/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.21  
% 1.91/1.22  tff(f_72, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 1.91/1.22  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.91/1.22  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.91/1.22  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.91/1.22  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.91/1.22  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.91/1.22  tff(c_18, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.91/1.22  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.22  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.91/1.22  tff(c_26, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.91/1.22  tff(c_34, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_22, c_26])).
% 1.91/1.22  tff(c_62, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, k3_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.22  tff(c_68, plain, (![C_24]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_24, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_62])).
% 1.91/1.22  tff(c_74, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_68])).
% 1.91/1.22  tff(c_20, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.91/1.22  tff(c_24, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.91/1.22  tff(c_99, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k3_subset_1(A_34, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.91/1.22  tff(c_103, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_99])).
% 1.91/1.22  tff(c_10, plain, (![A_10, C_12, B_11]: (r1_xboole_0(A_10, C_12) | ~r1_tarski(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.91/1.22  tff(c_114, plain, (![A_36]: (r1_xboole_0(A_36, '#skF_5') | ~r1_tarski(A_36, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_103, c_10])).
% 1.91/1.22  tff(c_117, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_20, c_114])).
% 1.91/1.22  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_117])).
% 1.91/1.22  tff(c_124, plain, (![C_37]: (~r2_hidden(C_37, '#skF_4'))), inference(splitRight, [status(thm)], [c_68])).
% 1.91/1.22  tff(c_128, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6, c_124])).
% 1.91/1.22  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_128])).
% 1.91/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  Inference rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Ref     : 0
% 1.91/1.22  #Sup     : 28
% 1.91/1.22  #Fact    : 0
% 1.91/1.22  #Define  : 0
% 1.91/1.22  #Split   : 2
% 1.91/1.22  #Chain   : 0
% 1.91/1.22  #Close   : 0
% 1.91/1.22  
% 1.91/1.22  Ordering : KBO
% 1.91/1.22  
% 1.91/1.22  Simplification rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Subsume      : 1
% 1.91/1.22  #Demod        : 1
% 1.91/1.22  #Tautology    : 12
% 1.91/1.22  #SimpNegUnit  : 2
% 1.91/1.22  #BackRed      : 0
% 1.91/1.22  
% 1.91/1.22  #Partial instantiations: 0
% 1.91/1.22  #Strategies tried      : 1
% 1.91/1.22  
% 1.91/1.22  Timing (in seconds)
% 1.91/1.22  ----------------------
% 1.91/1.22  Preprocessing        : 0.27
% 1.91/1.22  Parsing              : 0.14
% 1.91/1.22  CNF conversion       : 0.02
% 1.91/1.22  Main loop            : 0.13
% 1.91/1.22  Inferencing          : 0.05
% 1.91/1.22  Reduction            : 0.04
% 1.91/1.22  Demodulation         : 0.03
% 1.91/1.22  BG Simplification    : 0.01
% 1.91/1.22  Subsumption          : 0.02
% 1.91/1.22  Abstraction          : 0.01
% 1.91/1.22  MUC search           : 0.00
% 1.91/1.22  Cooper               : 0.00
% 1.91/1.22  Total                : 0.42
% 1.91/1.23  Index Insertion      : 0.00
% 1.91/1.23  Index Deletion       : 0.00
% 1.91/1.23  Index Matching       : 0.00
% 1.91/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
