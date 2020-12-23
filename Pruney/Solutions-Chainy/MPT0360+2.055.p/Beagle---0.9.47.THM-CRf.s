%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:26 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  75 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_60,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_68,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_45,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_53,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_40,c_45])).

tff(c_105,plain,(
    ! [D_36,B_37,A_38] :
      ( r2_hidden(D_36,B_37)
      | ~ r2_hidden(D_36,k3_xboole_0(A_38,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_119,plain,(
    ! [D_36] :
      ( r2_hidden(D_36,'#skF_7')
      | ~ r2_hidden(D_36,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_105])).

tff(c_38,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38,c_45])).

tff(c_116,plain,(
    ! [D_36] :
      ( r2_hidden(D_36,k3_subset_1('#skF_5','#skF_7'))
      | ~ r2_hidden(D_36,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_105])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_163,plain,(
    ! [A_47,B_48] :
      ( k4_xboole_0(A_47,B_48) = k3_subset_1(A_47,B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_167,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_163])).

tff(c_32,plain,(
    ! [A_18,B_19] : r1_xboole_0(k4_xboole_0(A_18,B_19),B_19) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_127,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,B_40)
      | ~ r2_hidden(C_41,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_130,plain,(
    ! [C_41,B_19,A_18] :
      ( ~ r2_hidden(C_41,B_19)
      | ~ r2_hidden(C_41,k4_xboole_0(A_18,B_19)) ) ),
    inference(resolution,[status(thm)],[c_32,c_127])).

tff(c_181,plain,(
    ! [C_49] :
      ( ~ r2_hidden(C_49,'#skF_7')
      | ~ r2_hidden(C_49,k3_subset_1('#skF_5','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_130])).

tff(c_216,plain,(
    ! [D_53] :
      ( ~ r2_hidden(D_53,'#skF_7')
      | ~ r2_hidden(D_53,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_116,c_181])).

tff(c_236,plain,(
    ! [D_54] : ~ r2_hidden(D_54,'#skF_6') ),
    inference(resolution,[status(thm)],[c_119,c_216])).

tff(c_248,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_26,c_236])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_248])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:06:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.30  
% 1.90/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 1.90/1.30  
% 1.90/1.30  %Foreground sorts:
% 1.90/1.30  
% 1.90/1.30  
% 1.90/1.30  %Background operators:
% 1.90/1.30  
% 1.90/1.30  
% 1.90/1.30  %Foreground operators:
% 1.90/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.90/1.30  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.90/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.30  tff('#skF_7', type, '#skF_7': $i).
% 1.90/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.90/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.90/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.30  tff('#skF_6', type, '#skF_6': $i).
% 1.90/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.30  
% 2.10/1.31  tff(f_81, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 2.10/1.31  tff(f_60, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.10/1.31  tff(f_66, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.10/1.31  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.10/1.31  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.10/1.31  tff(f_68, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.10/1.31  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.10/1.31  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.10/1.31  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.10/1.31  tff(c_40, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.10/1.31  tff(c_45, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.10/1.31  tff(c_53, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_40, c_45])).
% 2.10/1.31  tff(c_105, plain, (![D_36, B_37, A_38]: (r2_hidden(D_36, B_37) | ~r2_hidden(D_36, k3_xboole_0(A_38, B_37)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.10/1.31  tff(c_119, plain, (![D_36]: (r2_hidden(D_36, '#skF_7') | ~r2_hidden(D_36, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_105])).
% 2.10/1.31  tff(c_38, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.10/1.31  tff(c_52, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_38, c_45])).
% 2.10/1.31  tff(c_116, plain, (![D_36]: (r2_hidden(D_36, k3_subset_1('#skF_5', '#skF_7')) | ~r2_hidden(D_36, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_105])).
% 2.10/1.31  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.10/1.31  tff(c_163, plain, (![A_47, B_48]: (k4_xboole_0(A_47, B_48)=k3_subset_1(A_47, B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.10/1.31  tff(c_167, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_42, c_163])).
% 2.10/1.31  tff(c_32, plain, (![A_18, B_19]: (r1_xboole_0(k4_xboole_0(A_18, B_19), B_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.31  tff(c_127, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, B_40) | ~r2_hidden(C_41, A_39))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.31  tff(c_130, plain, (![C_41, B_19, A_18]: (~r2_hidden(C_41, B_19) | ~r2_hidden(C_41, k4_xboole_0(A_18, B_19)))), inference(resolution, [status(thm)], [c_32, c_127])).
% 2.10/1.31  tff(c_181, plain, (![C_49]: (~r2_hidden(C_49, '#skF_7') | ~r2_hidden(C_49, k3_subset_1('#skF_5', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_167, c_130])).
% 2.10/1.31  tff(c_216, plain, (![D_53]: (~r2_hidden(D_53, '#skF_7') | ~r2_hidden(D_53, '#skF_6'))), inference(resolution, [status(thm)], [c_116, c_181])).
% 2.10/1.31  tff(c_236, plain, (![D_54]: (~r2_hidden(D_54, '#skF_6'))), inference(resolution, [status(thm)], [c_119, c_216])).
% 2.10/1.31  tff(c_248, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_26, c_236])).
% 2.10/1.31  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_248])).
% 2.10/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.31  
% 2.10/1.31  Inference rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Ref     : 0
% 2.10/1.31  #Sup     : 52
% 2.10/1.31  #Fact    : 0
% 2.10/1.31  #Define  : 0
% 2.10/1.31  #Split   : 0
% 2.10/1.31  #Chain   : 0
% 2.10/1.31  #Close   : 0
% 2.10/1.31  
% 2.10/1.31  Ordering : KBO
% 2.10/1.31  
% 2.10/1.31  Simplification rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Subsume      : 3
% 2.10/1.31  #Demod        : 1
% 2.10/1.31  #Tautology    : 18
% 2.10/1.31  #SimpNegUnit  : 1
% 2.10/1.31  #BackRed      : 0
% 2.10/1.31  
% 2.10/1.31  #Partial instantiations: 0
% 2.10/1.31  #Strategies tried      : 1
% 2.10/1.31  
% 2.10/1.31  Timing (in seconds)
% 2.10/1.31  ----------------------
% 2.10/1.31  Preprocessing        : 0.31
% 2.10/1.31  Parsing              : 0.17
% 2.10/1.31  CNF conversion       : 0.02
% 2.10/1.31  Main loop            : 0.17
% 2.10/1.31  Inferencing          : 0.06
% 2.10/1.31  Reduction            : 0.05
% 2.10/1.31  Demodulation         : 0.04
% 2.10/1.31  BG Simplification    : 0.01
% 2.10/1.31  Subsumption          : 0.03
% 2.10/1.31  Abstraction          : 0.01
% 2.10/1.31  MUC search           : 0.00
% 2.10/1.31  Cooper               : 0.00
% 2.10/1.31  Total                : 0.51
% 2.10/1.31  Index Insertion      : 0.00
% 2.10/1.31  Index Deletion       : 0.00
% 2.10/1.31  Index Matching       : 0.00
% 2.10/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
