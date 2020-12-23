%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:00 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   50 (  84 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   64 ( 170 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ! [C] :
            ( m1_subset_1(C,A)
           => ( A != k1_xboole_0
             => m1_subset_1(k2_tarski(B,C),k1_zfmisc_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_38,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    ! [B_20,A_21] :
      ( v1_xboole_0(B_20)
      | ~ m1_subset_1(B_20,A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_59,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_48])).

tff(c_61,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_38,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,A_12)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_118,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_tarski(k2_tarski(A_42,B_43),C_44)
      | ~ r2_hidden(B_43,C_44)
      | ~ r2_hidden(A_42,C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [C_8,A_4] :
      ( r2_hidden(C_8,k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,(
    ! [B_38,A_39] :
      ( m1_subset_1(B_38,A_39)
      | ~ r2_hidden(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_100,plain,(
    ! [C_8,A_4] :
      ( m1_subset_1(C_8,k1_zfmisc_1(A_4))
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_94])).

tff(c_105,plain,(
    ! [C_40,A_41] :
      ( m1_subset_1(C_40,k1_zfmisc_1(A_41))
      | ~ r1_tarski(C_40,A_41) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_100])).

tff(c_34,plain,(
    ~ m1_subset_1(k2_tarski('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_117,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_34])).

tff(c_128,plain,
    ( ~ r2_hidden('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_117])).

tff(c_131,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_134,plain,
    ( ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_137,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_134])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_137])).

tff(c_140,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_154,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_140])).

tff(c_157,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_154])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_157])).

tff(c_161,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_168,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.14  
% 1.74/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.14  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.74/1.14  
% 1.74/1.14  %Foreground sorts:
% 1.74/1.14  
% 1.74/1.14  
% 1.74/1.14  %Background operators:
% 1.74/1.14  
% 1.74/1.14  
% 1.74/1.14  %Foreground operators:
% 1.74/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.74/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.74/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.74/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.74/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.74/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.74/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.74/1.14  
% 1.74/1.15  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (~(A = k1_xboole_0) => m1_subset_1(k2_tarski(B, C), k1_zfmisc_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_subset_1)).
% 1.74/1.15  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.74/1.15  tff(f_44, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.74/1.15  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.74/1.15  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.74/1.15  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.74/1.15  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.74/1.15  tff(c_40, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.74/1.15  tff(c_48, plain, (![B_20, A_21]: (v1_xboole_0(B_20) | ~m1_subset_1(B_20, A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.74/1.15  tff(c_59, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_48])).
% 1.74/1.15  tff(c_61, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_59])).
% 1.74/1.15  tff(c_38, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.74/1.15  tff(c_26, plain, (![B_13, A_12]: (r2_hidden(B_13, A_12) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.74/1.15  tff(c_118, plain, (![A_42, B_43, C_44]: (r1_tarski(k2_tarski(A_42, B_43), C_44) | ~r2_hidden(B_43, C_44) | ~r2_hidden(A_42, C_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.74/1.15  tff(c_32, plain, (![A_14]: (~v1_xboole_0(k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.74/1.15  tff(c_8, plain, (![C_8, A_4]: (r2_hidden(C_8, k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.74/1.15  tff(c_94, plain, (![B_38, A_39]: (m1_subset_1(B_38, A_39) | ~r2_hidden(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.74/1.15  tff(c_100, plain, (![C_8, A_4]: (m1_subset_1(C_8, k1_zfmisc_1(A_4)) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(resolution, [status(thm)], [c_8, c_94])).
% 1.74/1.15  tff(c_105, plain, (![C_40, A_41]: (m1_subset_1(C_40, k1_zfmisc_1(A_41)) | ~r1_tarski(C_40, A_41))), inference(negUnitSimplification, [status(thm)], [c_32, c_100])).
% 1.74/1.15  tff(c_34, plain, (~m1_subset_1(k2_tarski('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.74/1.15  tff(c_117, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_105, c_34])).
% 1.74/1.15  tff(c_128, plain, (~r2_hidden('#skF_5', '#skF_3') | ~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_118, c_117])).
% 1.74/1.15  tff(c_131, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_128])).
% 1.74/1.15  tff(c_134, plain, (~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_131])).
% 1.74/1.15  tff(c_137, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_134])).
% 1.74/1.15  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_137])).
% 1.74/1.15  tff(c_140, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_128])).
% 1.74/1.15  tff(c_154, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_140])).
% 1.74/1.15  tff(c_157, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_154])).
% 1.74/1.15  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_157])).
% 1.74/1.15  tff(c_161, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_59])).
% 1.74/1.15  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.74/1.15  tff(c_168, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_161, c_2])).
% 1.74/1.15  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_168])).
% 1.74/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.15  
% 1.74/1.15  Inference rules
% 1.74/1.15  ----------------------
% 1.74/1.15  #Ref     : 0
% 1.74/1.15  #Sup     : 23
% 1.74/1.16  #Fact    : 0
% 1.74/1.16  #Define  : 0
% 1.74/1.16  #Split   : 3
% 1.74/1.16  #Chain   : 0
% 1.74/1.16  #Close   : 0
% 1.74/1.16  
% 1.74/1.16  Ordering : KBO
% 1.74/1.16  
% 1.74/1.16  Simplification rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Subsume      : 4
% 1.74/1.16  #Demod        : 2
% 1.74/1.16  #Tautology    : 8
% 1.74/1.16  #SimpNegUnit  : 5
% 1.74/1.16  #BackRed      : 0
% 1.74/1.16  
% 1.74/1.16  #Partial instantiations: 0
% 1.74/1.16  #Strategies tried      : 1
% 1.74/1.16  
% 1.74/1.16  Timing (in seconds)
% 1.74/1.16  ----------------------
% 1.74/1.16  Preprocessing        : 0.30
% 1.74/1.16  Parsing              : 0.16
% 1.74/1.16  CNF conversion       : 0.02
% 1.74/1.16  Main loop            : 0.14
% 1.74/1.16  Inferencing          : 0.05
% 1.74/1.16  Reduction            : 0.04
% 1.74/1.16  Demodulation         : 0.02
% 1.74/1.16  BG Simplification    : 0.01
% 1.74/1.16  Subsumption          : 0.02
% 1.74/1.16  Abstraction          : 0.01
% 1.74/1.16  MUC search           : 0.00
% 1.74/1.16  Cooper               : 0.00
% 1.74/1.16  Total                : 0.47
% 1.74/1.16  Index Insertion      : 0.00
% 1.74/1.16  Index Deletion       : 0.00
% 1.74/1.16  Index Matching       : 0.00
% 1.74/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
