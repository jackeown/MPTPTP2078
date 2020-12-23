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
% DateTime   : Thu Dec  3 09:56:27 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  65 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  85 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_40])).

tff(c_61,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_61])).

tff(c_86,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_189,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_201,plain,(
    ! [C_36] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_36,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_189])).

tff(c_260,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_24,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_486,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_490,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_486])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_xboole_0(A_10,C_12)
      | ~ r1_tarski(A_10,k4_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_522,plain,(
    ! [A_69] :
      ( r1_xboole_0(A_69,'#skF_5')
      | ~ r1_tarski(A_69,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_12])).

tff(c_529,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_522])).

tff(c_534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_529])).

tff(c_537,plain,(
    ! [C_70] : ~ r2_hidden(C_70,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_541,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6,c_537])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_541])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.41  
% 2.22/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.22/1.41  
% 2.22/1.41  %Foreground sorts:
% 2.22/1.41  
% 2.22/1.41  
% 2.22/1.41  %Background operators:
% 2.22/1.41  
% 2.22/1.41  
% 2.22/1.41  %Foreground operators:
% 2.22/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.22/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.22/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.22/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.41  
% 2.22/1.42  tff(f_74, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 2.22/1.42  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.22/1.42  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.22/1.42  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.22/1.42  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.22/1.42  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.22/1.42  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.22/1.42  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.22/1.42  tff(c_22, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.22/1.42  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.42  tff(c_16, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.22/1.42  tff(c_26, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.22/1.42  tff(c_40, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.22/1.42  tff(c_52, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_40])).
% 2.22/1.42  tff(c_61, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.42  tff(c_79, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_52, c_61])).
% 2.22/1.42  tff(c_86, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_79])).
% 2.22/1.42  tff(c_189, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.42  tff(c_201, plain, (![C_36]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_36, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_189])).
% 2.22/1.42  tff(c_260, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_201])).
% 2.22/1.42  tff(c_24, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.22/1.42  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.22/1.42  tff(c_486, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.42  tff(c_490, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_486])).
% 2.22/1.42  tff(c_12, plain, (![A_10, C_12, B_11]: (r1_xboole_0(A_10, C_12) | ~r1_tarski(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.42  tff(c_522, plain, (![A_69]: (r1_xboole_0(A_69, '#skF_5') | ~r1_tarski(A_69, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_490, c_12])).
% 2.22/1.42  tff(c_529, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_522])).
% 2.22/1.42  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_529])).
% 2.22/1.42  tff(c_537, plain, (![C_70]: (~r2_hidden(C_70, '#skF_4'))), inference(splitRight, [status(thm)], [c_201])).
% 2.22/1.42  tff(c_541, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_6, c_537])).
% 2.22/1.42  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_541])).
% 2.22/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.42  
% 2.22/1.42  Inference rules
% 2.22/1.42  ----------------------
% 2.22/1.42  #Ref     : 0
% 2.22/1.42  #Sup     : 135
% 2.22/1.42  #Fact    : 0
% 2.22/1.42  #Define  : 0
% 2.22/1.42  #Split   : 3
% 2.22/1.42  #Chain   : 0
% 2.22/1.42  #Close   : 0
% 2.22/1.42  
% 2.22/1.42  Ordering : KBO
% 2.22/1.42  
% 2.22/1.42  Simplification rules
% 2.22/1.42  ----------------------
% 2.22/1.42  #Subsume      : 25
% 2.22/1.42  #Demod        : 19
% 2.22/1.42  #Tautology    : 46
% 2.22/1.42  #SimpNegUnit  : 8
% 2.22/1.42  #BackRed      : 1
% 2.22/1.42  
% 2.22/1.42  #Partial instantiations: 0
% 2.22/1.42  #Strategies tried      : 1
% 2.22/1.42  
% 2.22/1.42  Timing (in seconds)
% 2.22/1.42  ----------------------
% 2.22/1.42  Preprocessing        : 0.28
% 2.22/1.42  Parsing              : 0.15
% 2.22/1.42  CNF conversion       : 0.02
% 2.22/1.42  Main loop            : 0.27
% 2.22/1.42  Inferencing          : 0.11
% 2.22/1.42  Reduction            : 0.08
% 2.22/1.42  Demodulation         : 0.06
% 2.22/1.42  BG Simplification    : 0.01
% 2.22/1.42  Subsumption          : 0.04
% 2.22/1.42  Abstraction          : 0.01
% 2.22/1.42  MUC search           : 0.00
% 2.22/1.42  Cooper               : 0.00
% 2.22/1.42  Total                : 0.57
% 2.22/1.42  Index Insertion      : 0.00
% 2.22/1.42  Index Deletion       : 0.00
% 2.22/1.42  Index Matching       : 0.00
% 2.22/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
