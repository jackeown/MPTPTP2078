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
% DateTime   : Thu Dec  3 10:04:37 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   38 (  52 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  84 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_20,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_20])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( r1_xboole_0(k1_tarski(A_11),B_12)
      | r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    ! [B_12,A_11] :
      ( r1_xboole_0(B_12,k1_tarski(A_11))
      | r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_22,c_2])).

tff(c_43,plain,(
    ! [B_19,A_20] :
      ( k10_relat_1(B_19,A_20) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_19),A_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [B_25,A_26] :
      ( k10_relat_1(B_25,k1_tarski(A_26)) = k1_xboole_0
      | ~ v1_relat_1(B_25)
      | r2_hidden(A_26,k2_relat_1(B_25)) ) ),
    inference(resolution,[status(thm)],[c_25,c_43])).

tff(c_74,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_40])).

tff(c_77,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_74])).

tff(c_79,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_77])).

tff(c_80,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_81,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_89,plain,(
    ! [B_29,A_30] :
      ( r1_xboole_0(k2_relat_1(B_29),A_30)
      | k10_relat_1(B_29,A_30) != k1_xboole_0
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_103,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,k2_relat_1(B_34))
      | k10_relat_1(B_34,A_33) != k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_89,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden(A_5,B_6)
      | ~ r1_xboole_0(k1_tarski(A_5),B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden(A_37,k2_relat_1(B_38))
      | k10_relat_1(B_38,k1_tarski(A_37)) != k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_103,c_6])).

tff(c_124,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_118])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_80,c_124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.21  
% 1.75/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.21  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.75/1.21  
% 1.75/1.21  %Foreground sorts:
% 1.75/1.21  
% 1.75/1.21  
% 1.75/1.21  %Background operators:
% 1.75/1.21  
% 1.75/1.21  
% 1.75/1.21  %Foreground operators:
% 1.75/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.75/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.75/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.75/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.75/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.75/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.75/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.21  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.75/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.75/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.21  
% 1.75/1.22  tff(f_53, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 1.75/1.22  tff(f_34, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.75/1.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.75/1.22  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.75/1.22  tff(f_39, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 1.75/1.22  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.75/1.22  tff(c_14, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.75/1.22  tff(c_40, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_14])).
% 1.75/1.22  tff(c_20, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.75/1.22  tff(c_42, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_20])).
% 1.75/1.22  tff(c_22, plain, (![A_11, B_12]: (r1_xboole_0(k1_tarski(A_11), B_12) | r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.75/1.22  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.75/1.22  tff(c_25, plain, (![B_12, A_11]: (r1_xboole_0(B_12, k1_tarski(A_11)) | r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_22, c_2])).
% 1.75/1.22  tff(c_43, plain, (![B_19, A_20]: (k10_relat_1(B_19, A_20)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_19), A_20) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.75/1.22  tff(c_71, plain, (![B_25, A_26]: (k10_relat_1(B_25, k1_tarski(A_26))=k1_xboole_0 | ~v1_relat_1(B_25) | r2_hidden(A_26, k2_relat_1(B_25)))), inference(resolution, [status(thm)], [c_25, c_43])).
% 1.75/1.22  tff(c_74, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_71, c_40])).
% 1.75/1.22  tff(c_77, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_74])).
% 1.75/1.22  tff(c_79, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_77])).
% 1.75/1.22  tff(c_80, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_14])).
% 1.75/1.22  tff(c_81, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_14])).
% 1.75/1.22  tff(c_89, plain, (![B_29, A_30]: (r1_xboole_0(k2_relat_1(B_29), A_30) | k10_relat_1(B_29, A_30)!=k1_xboole_0 | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.75/1.22  tff(c_103, plain, (![A_33, B_34]: (r1_xboole_0(A_33, k2_relat_1(B_34)) | k10_relat_1(B_34, A_33)!=k1_xboole_0 | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_89, c_2])).
% 1.75/1.22  tff(c_6, plain, (![A_5, B_6]: (~r2_hidden(A_5, B_6) | ~r1_xboole_0(k1_tarski(A_5), B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.75/1.22  tff(c_118, plain, (![A_37, B_38]: (~r2_hidden(A_37, k2_relat_1(B_38)) | k10_relat_1(B_38, k1_tarski(A_37))!=k1_xboole_0 | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_103, c_6])).
% 1.75/1.22  tff(c_124, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_81, c_118])).
% 1.75/1.22  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_80, c_124])).
% 1.75/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.22  
% 1.75/1.22  Inference rules
% 1.75/1.22  ----------------------
% 1.75/1.22  #Ref     : 0
% 1.75/1.22  #Sup     : 21
% 1.75/1.22  #Fact    : 0
% 1.75/1.22  #Define  : 0
% 1.75/1.22  #Split   : 1
% 1.75/1.22  #Chain   : 0
% 1.75/1.22  #Close   : 0
% 1.75/1.22  
% 1.75/1.22  Ordering : KBO
% 1.75/1.22  
% 1.75/1.22  Simplification rules
% 1.75/1.22  ----------------------
% 1.75/1.22  #Subsume      : 3
% 1.75/1.22  #Demod        : 5
% 1.75/1.22  #Tautology    : 9
% 1.75/1.22  #SimpNegUnit  : 2
% 1.75/1.22  #BackRed      : 0
% 1.75/1.22  
% 1.75/1.22  #Partial instantiations: 0
% 1.75/1.22  #Strategies tried      : 1
% 1.75/1.22  
% 1.75/1.22  Timing (in seconds)
% 1.75/1.22  ----------------------
% 1.86/1.22  Preprocessing        : 0.27
% 1.86/1.22  Parsing              : 0.16
% 1.86/1.22  CNF conversion       : 0.02
% 1.86/1.22  Main loop            : 0.14
% 1.86/1.22  Inferencing          : 0.06
% 1.86/1.22  Reduction            : 0.03
% 1.86/1.22  Demodulation         : 0.02
% 1.86/1.22  BG Simplification    : 0.01
% 1.86/1.22  Subsumption          : 0.02
% 1.86/1.22  Abstraction          : 0.01
% 1.86/1.22  MUC search           : 0.00
% 1.86/1.22  Cooper               : 0.00
% 1.86/1.22  Total                : 0.44
% 1.86/1.22  Index Insertion      : 0.00
% 1.86/1.22  Index Deletion       : 0.00
% 1.86/1.23  Index Matching       : 0.00
% 1.86/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
