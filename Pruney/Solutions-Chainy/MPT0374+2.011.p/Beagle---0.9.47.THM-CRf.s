%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:00 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   49 (  83 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 170 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_46,plain,(
    ! [B_18,A_19] :
      ( v1_xboole_0(B_18)
      | ~ m1_subset_1(B_18,A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_57,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_59,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_36,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [B_11,A_10] :
      ( r2_hidden(B_11,A_10)
      | ~ m1_subset_1(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(k2_tarski(A_7,B_8),C_9)
      | ~ r2_hidden(B_8,C_9)
      | ~ r2_hidden(A_7,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( r2_hidden(C_6,k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_83,plain,(
    ! [B_34,A_35] :
      ( m1_subset_1(B_34,A_35)
      | ~ r2_hidden(B_34,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,(
    ! [C_6,A_2] :
      ( m1_subset_1(C_6,k1_zfmisc_1(A_2))
      | v1_xboole_0(k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_103,plain,(
    ! [C_39,A_40] :
      ( m1_subset_1(C_39,k1_zfmisc_1(A_40))
      | ~ r1_tarski(C_39,A_40) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_89])).

tff(c_32,plain,(
    ~ m1_subset_1(k2_tarski('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_115,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_32])).

tff(c_119,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_115])).

tff(c_120,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_123,plain,
    ( ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_120])).

tff(c_126,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_123])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_126])).

tff(c_129,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_133,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_129])).

tff(c_136,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_133])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_136])).

tff(c_140,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_148,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:42:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.50  
% 2.27/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.27/1.50  
% 2.27/1.50  %Foreground sorts:
% 2.27/1.50  
% 2.27/1.50  
% 2.27/1.50  %Background operators:
% 2.27/1.50  
% 2.27/1.50  
% 2.27/1.50  %Foreground operators:
% 2.27/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.50  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.27/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.50  
% 2.37/1.52  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_subset_1)).
% 2.37/1.52  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.37/1.52  tff(f_42, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.37/1.52  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.37/1.52  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.37/1.52  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 2.37/1.52  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.37/1.52  tff(c_38, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.37/1.52  tff(c_46, plain, (![B_18, A_19]: (v1_xboole_0(B_18) | ~m1_subset_1(B_18, A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.52  tff(c_57, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_46])).
% 2.37/1.52  tff(c_59, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_57])).
% 2.37/1.52  tff(c_36, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.37/1.52  tff(c_24, plain, (![B_11, A_10]: (r2_hidden(B_11, A_10) | ~m1_subset_1(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.52  tff(c_16, plain, (![A_7, B_8, C_9]: (r1_tarski(k2_tarski(A_7, B_8), C_9) | ~r2_hidden(B_8, C_9) | ~r2_hidden(A_7, C_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.37/1.52  tff(c_30, plain, (![A_12]: (~v1_xboole_0(k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.37/1.52  tff(c_6, plain, (![C_6, A_2]: (r2_hidden(C_6, k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.37/1.52  tff(c_83, plain, (![B_34, A_35]: (m1_subset_1(B_34, A_35) | ~r2_hidden(B_34, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.52  tff(c_89, plain, (![C_6, A_2]: (m1_subset_1(C_6, k1_zfmisc_1(A_2)) | v1_xboole_0(k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(resolution, [status(thm)], [c_6, c_83])).
% 2.37/1.52  tff(c_103, plain, (![C_39, A_40]: (m1_subset_1(C_39, k1_zfmisc_1(A_40)) | ~r1_tarski(C_39, A_40))), inference(negUnitSimplification, [status(thm)], [c_30, c_89])).
% 2.37/1.52  tff(c_32, plain, (~m1_subset_1(k2_tarski('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.37/1.52  tff(c_115, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_103, c_32])).
% 2.37/1.52  tff(c_119, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_115])).
% 2.37/1.52  tff(c_120, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_119])).
% 2.37/1.52  tff(c_123, plain, (~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_120])).
% 2.37/1.52  tff(c_126, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_123])).
% 2.37/1.52  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_126])).
% 2.37/1.52  tff(c_129, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_119])).
% 2.37/1.52  tff(c_133, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_129])).
% 2.37/1.52  tff(c_136, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_133])).
% 2.37/1.52  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_136])).
% 2.37/1.52  tff(c_140, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_57])).
% 2.37/1.52  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.37/1.52  tff(c_148, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_140, c_2])).
% 2.37/1.52  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_148])).
% 2.37/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.52  
% 2.37/1.52  Inference rules
% 2.37/1.52  ----------------------
% 2.37/1.52  #Ref     : 0
% 2.37/1.52  #Sup     : 19
% 2.37/1.52  #Fact    : 0
% 2.37/1.52  #Define  : 0
% 2.37/1.52  #Split   : 3
% 2.37/1.52  #Chain   : 0
% 2.37/1.52  #Close   : 0
% 2.37/1.52  
% 2.37/1.52  Ordering : KBO
% 2.37/1.52  
% 2.37/1.52  Simplification rules
% 2.37/1.52  ----------------------
% 2.37/1.52  #Subsume      : 4
% 2.37/1.52  #Demod        : 2
% 2.37/1.52  #Tautology    : 6
% 2.37/1.52  #SimpNegUnit  : 5
% 2.37/1.52  #BackRed      : 0
% 2.37/1.52  
% 2.37/1.52  #Partial instantiations: 0
% 2.37/1.52  #Strategies tried      : 1
% 2.37/1.52  
% 2.37/1.52  Timing (in seconds)
% 2.37/1.52  ----------------------
% 2.37/1.53  Preprocessing        : 0.47
% 2.37/1.53  Parsing              : 0.24
% 2.37/1.53  CNF conversion       : 0.03
% 2.37/1.53  Main loop            : 0.23
% 2.37/1.53  Inferencing          : 0.08
% 2.37/1.53  Reduction            : 0.06
% 2.37/1.53  Demodulation         : 0.03
% 2.37/1.53  BG Simplification    : 0.02
% 2.37/1.53  Subsumption          : 0.04
% 2.37/1.53  Abstraction          : 0.01
% 2.37/1.53  MUC search           : 0.00
% 2.37/1.53  Cooper               : 0.00
% 2.37/1.53  Total                : 0.74
% 2.37/1.53  Index Insertion      : 0.00
% 2.37/1.53  Index Deletion       : 0.00
% 2.37/1.53  Index Matching       : 0.00
% 2.37/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
