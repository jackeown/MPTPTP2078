%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:51 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  51 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,k2_zfmisc_1(k1_relat_1(A_13),k2_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_29,plain,(
    ! [C_26,B_27,A_28] :
      ( r2_hidden(C_26,B_27)
      | ~ r2_hidden(C_26,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_2'(A_36),B_37)
      | ~ r1_tarski(A_36,B_37)
      | k1_xboole_0 = A_36 ) ),
    inference(resolution,[status(thm)],[c_8,c_29])).

tff(c_37,plain,(
    ! [A_30,B_31,C_32] :
      ( k4_tarski('#skF_3'(A_30,B_31,C_32),'#skF_4'(A_30,B_31,C_32)) = A_30
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_31,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [B_16,C_17] : ~ r2_hidden(k4_tarski(B_16,C_17),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r2_hidden(A_30,'#skF_5')
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_31,C_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_16])).

tff(c_88,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r2_hidden('#skF_2'(A_45),'#skF_5')
      | ~ r1_tarski(A_45,k2_zfmisc_1(B_46,C_47))
      | k1_xboole_0 = A_45 ) ),
    inference(resolution,[status(thm)],[c_59,c_42])).

tff(c_94,plain,(
    ! [B_46,C_47] :
      ( ~ r1_tarski('#skF_5',k2_zfmisc_1(B_46,C_47))
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_99,plain,(
    ! [B_48,C_49] : ~ r1_tarski('#skF_5',k2_zfmisc_1(B_48,C_49)) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_14,c_94])).

tff(c_103,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_99])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.14  
% 1.70/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_3 > #skF_1
% 1.70/1.15  
% 1.70/1.15  %Foreground sorts:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Background operators:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Foreground operators:
% 1.70/1.15  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.70/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.70/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.70/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.70/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.70/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.15  
% 1.70/1.15  tff(f_60, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 1.70/1.15  tff(f_51, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 1.70/1.15  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.70/1.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.70/1.15  tff(f_47, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 1.70/1.15  tff(c_18, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.70/1.15  tff(c_12, plain, (![A_13]: (r1_tarski(A_13, k2_zfmisc_1(k1_relat_1(A_13), k2_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.70/1.15  tff(c_14, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.70/1.15  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.70/1.15  tff(c_29, plain, (![C_26, B_27, A_28]: (r2_hidden(C_26, B_27) | ~r2_hidden(C_26, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.70/1.15  tff(c_59, plain, (![A_36, B_37]: (r2_hidden('#skF_2'(A_36), B_37) | ~r1_tarski(A_36, B_37) | k1_xboole_0=A_36)), inference(resolution, [status(thm)], [c_8, c_29])).
% 1.70/1.15  tff(c_37, plain, (![A_30, B_31, C_32]: (k4_tarski('#skF_3'(A_30, B_31, C_32), '#skF_4'(A_30, B_31, C_32))=A_30 | ~r2_hidden(A_30, k2_zfmisc_1(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.70/1.15  tff(c_16, plain, (![B_16, C_17]: (~r2_hidden(k4_tarski(B_16, C_17), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.70/1.15  tff(c_42, plain, (![A_30, B_31, C_32]: (~r2_hidden(A_30, '#skF_5') | ~r2_hidden(A_30, k2_zfmisc_1(B_31, C_32)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_16])).
% 1.70/1.15  tff(c_88, plain, (![A_45, B_46, C_47]: (~r2_hidden('#skF_2'(A_45), '#skF_5') | ~r1_tarski(A_45, k2_zfmisc_1(B_46, C_47)) | k1_xboole_0=A_45)), inference(resolution, [status(thm)], [c_59, c_42])).
% 1.70/1.15  tff(c_94, plain, (![B_46, C_47]: (~r1_tarski('#skF_5', k2_zfmisc_1(B_46, C_47)) | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_8, c_88])).
% 1.70/1.15  tff(c_99, plain, (![B_48, C_49]: (~r1_tarski('#skF_5', k2_zfmisc_1(B_48, C_49)))), inference(negUnitSimplification, [status(thm)], [c_14, c_14, c_94])).
% 1.70/1.15  tff(c_103, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_99])).
% 1.70/1.15  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_103])).
% 1.70/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  Inference rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Ref     : 0
% 1.70/1.15  #Sup     : 17
% 1.70/1.15  #Fact    : 0
% 1.70/1.15  #Define  : 0
% 1.70/1.15  #Split   : 0
% 1.70/1.15  #Chain   : 0
% 1.70/1.15  #Close   : 0
% 1.70/1.15  
% 1.70/1.15  Ordering : KBO
% 1.70/1.15  
% 1.70/1.15  Simplification rules
% 1.70/1.15  ----------------------
% 1.70/1.15  #Subsume      : 0
% 1.70/1.15  #Demod        : 1
% 1.70/1.15  #Tautology    : 3
% 1.70/1.15  #SimpNegUnit  : 1
% 1.70/1.15  #BackRed      : 0
% 1.70/1.15  
% 1.70/1.15  #Partial instantiations: 0
% 1.70/1.15  #Strategies tried      : 1
% 1.70/1.15  
% 1.70/1.16  Timing (in seconds)
% 1.77/1.16  ----------------------
% 1.77/1.16  Preprocessing        : 0.27
% 1.77/1.16  Parsing              : 0.14
% 1.77/1.16  CNF conversion       : 0.02
% 1.77/1.16  Main loop            : 0.12
% 1.77/1.16  Inferencing          : 0.05
% 1.77/1.16  Reduction            : 0.03
% 1.77/1.16  Demodulation         : 0.02
% 1.77/1.16  BG Simplification    : 0.01
% 1.77/1.16  Subsumption          : 0.02
% 1.77/1.16  Abstraction          : 0.01
% 1.77/1.16  MUC search           : 0.00
% 1.77/1.16  Cooper               : 0.00
% 1.77/1.16  Total                : 0.42
% 1.77/1.16  Index Insertion      : 0.00
% 1.77/1.16  Index Deletion       : 0.00
% 1.77/1.16  Index Matching       : 0.00
% 1.77/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
