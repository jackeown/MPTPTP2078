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
% DateTime   : Thu Dec  3 10:04:37 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   44 (  65 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 ( 104 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_63,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_45,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(k1_tarski(A_19),B_20)
      | r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    ! [B_20,A_19] :
      ( r1_xboole_0(B_20,k1_tarski(A_19))
      | r2_hidden(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_69,plain,(
    ! [B_27,A_28] :
      ( k10_relat_1(B_27,A_28) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_27),A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    ! [B_31,A_32] :
      ( k10_relat_1(B_31,k1_tarski(A_32)) = k1_xboole_0
      | ~ v1_relat_1(B_31)
      | r2_hidden(A_32,k2_relat_1(B_31)) ) ),
    inference(resolution,[status(thm)],[c_52,c_69])).

tff(c_18,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_96,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_64])).

tff(c_99,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_96])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_99])).

tff(c_102,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_63])).

tff(c_110,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_112,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_112])).

tff(c_115,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_129,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(k2_relat_1(B_35),A_36)
      | k10_relat_1(B_35,A_36) != k1_xboole_0
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_137,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(A_37,k2_relat_1(B_38))
      | k10_relat_1(B_38,A_37) != k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden(A_6,B_7)
      | ~ r1_xboole_0(k1_tarski(A_6),B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_152,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden(A_41,k2_relat_1(B_42))
      | k10_relat_1(B_42,k1_tarski(A_41)) != k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_137,c_8])).

tff(c_158,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_152])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_115,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.18  
% 1.82/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.19  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.82/1.19  
% 1.82/1.19  %Foreground sorts:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Background operators:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Foreground operators:
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.82/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.82/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.19  
% 1.82/1.20  tff(f_57, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 1.82/1.20  tff(f_43, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.82/1.20  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.82/1.20  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.82/1.20  tff(f_38, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.82/1.20  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.20  tff(c_24, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.20  tff(c_63, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24])).
% 1.82/1.20  tff(c_45, plain, (![A_19, B_20]: (r1_xboole_0(k1_tarski(A_19), B_20) | r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.20  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.20  tff(c_52, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k1_tarski(A_19)) | r2_hidden(A_19, B_20))), inference(resolution, [status(thm)], [c_45, c_2])).
% 1.82/1.20  tff(c_69, plain, (![B_27, A_28]: (k10_relat_1(B_27, A_28)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_27), A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.82/1.20  tff(c_93, plain, (![B_31, A_32]: (k10_relat_1(B_31, k1_tarski(A_32))=k1_xboole_0 | ~v1_relat_1(B_31) | r2_hidden(A_32, k2_relat_1(B_31)))), inference(resolution, [status(thm)], [c_52, c_69])).
% 1.82/1.20  tff(c_18, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.20  tff(c_64, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_18])).
% 1.82/1.20  tff(c_96, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_93, c_64])).
% 1.82/1.20  tff(c_99, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_96])).
% 1.82/1.20  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_99])).
% 1.82/1.20  tff(c_102, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_18])).
% 1.82/1.20  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_63])).
% 1.82/1.20  tff(c_110, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_24])).
% 1.82/1.20  tff(c_112, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_18])).
% 1.82/1.20  tff(c_114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_112])).
% 1.82/1.20  tff(c_115, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_18])).
% 1.82/1.20  tff(c_129, plain, (![B_35, A_36]: (r1_xboole_0(k2_relat_1(B_35), A_36) | k10_relat_1(B_35, A_36)!=k1_xboole_0 | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.82/1.20  tff(c_137, plain, (![A_37, B_38]: (r1_xboole_0(A_37, k2_relat_1(B_38)) | k10_relat_1(B_38, A_37)!=k1_xboole_0 | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_129, c_2])).
% 1.82/1.20  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden(A_6, B_7) | ~r1_xboole_0(k1_tarski(A_6), B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.82/1.20  tff(c_152, plain, (![A_41, B_42]: (~r2_hidden(A_41, k2_relat_1(B_42)) | k10_relat_1(B_42, k1_tarski(A_41))!=k1_xboole_0 | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_137, c_8])).
% 1.82/1.20  tff(c_158, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_110, c_152])).
% 1.82/1.20  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_115, c_158])).
% 1.82/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.20  
% 1.82/1.20  Inference rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Ref     : 0
% 1.82/1.20  #Sup     : 27
% 1.82/1.20  #Fact    : 0
% 1.82/1.20  #Define  : 0
% 1.82/1.20  #Split   : 3
% 1.82/1.20  #Chain   : 0
% 1.82/1.20  #Close   : 0
% 1.82/1.20  
% 1.82/1.20  Ordering : KBO
% 1.82/1.20  
% 1.82/1.20  Simplification rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Subsume      : 3
% 1.82/1.20  #Demod        : 7
% 1.82/1.20  #Tautology    : 16
% 1.82/1.20  #SimpNegUnit  : 1
% 1.82/1.20  #BackRed      : 0
% 1.82/1.20  
% 1.82/1.20  #Partial instantiations: 0
% 1.82/1.20  #Strategies tried      : 1
% 1.82/1.20  
% 1.82/1.20  Timing (in seconds)
% 1.82/1.20  ----------------------
% 1.82/1.20  Preprocessing        : 0.26
% 1.82/1.20  Parsing              : 0.14
% 1.82/1.20  CNF conversion       : 0.02
% 1.82/1.20  Main loop            : 0.14
% 1.82/1.20  Inferencing          : 0.06
% 1.82/1.20  Reduction            : 0.03
% 1.82/1.20  Demodulation         : 0.03
% 1.82/1.20  BG Simplification    : 0.01
% 1.82/1.20  Subsumption          : 0.03
% 1.82/1.20  Abstraction          : 0.01
% 1.82/1.20  MUC search           : 0.00
% 1.82/1.20  Cooper               : 0.00
% 1.82/1.20  Total                : 0.43
% 1.82/1.20  Index Insertion      : 0.00
% 1.82/1.20  Index Deletion       : 0.00
% 1.82/1.20  Index Matching       : 0.00
% 1.82/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
