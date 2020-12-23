%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:37 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   43 (  57 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  88 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_38,axiom,(
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

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_72,plain,(
    ~ r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_24,plain,
    ( r2_hidden('#skF_1',k2_relat_1('#skF_2'))
    | k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_73,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_24])).

tff(c_44,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),B_19)
      | r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [B_19,A_18] :
      ( r1_xboole_0(B_19,k1_tarski(A_18))
      | r2_hidden(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_79,plain,(
    ! [B_34,A_35] :
      ( k10_relat_1(B_34,A_35) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [B_38,A_39] :
      ( k10_relat_1(B_38,k1_tarski(A_39)) = k1_xboole_0
      | ~ v1_relat_1(B_38)
      | r2_hidden(A_39,k2_relat_1(B_38)) ) ),
    inference(resolution,[status(thm)],[c_47,c_79])).

tff(c_111,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_72])).

tff(c_114,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_111])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_114])).

tff(c_117,plain,(
    k10_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_118,plain,(
    r2_hidden('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_132,plain,(
    ! [B_45,A_46] :
      ( r1_xboole_0(k2_relat_1(B_45),A_46)
      | k10_relat_1(B_45,A_46) != k1_xboole_0
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_140,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(A_47,k2_relat_1(B_48))
      | k10_relat_1(B_48,A_47) != k1_xboole_0
      | ~ v1_relat_1(B_48) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_20,C_21,B_22] :
      ( ~ r2_hidden(A_20,C_21)
      | ~ r1_xboole_0(k2_tarski(A_20,B_22),C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_51,plain,(
    ! [A_3,C_21] :
      ( ~ r2_hidden(A_3,C_21)
      | ~ r1_xboole_0(k1_tarski(A_3),C_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_160,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden(A_51,k2_relat_1(B_52))
      | k10_relat_1(B_52,k1_tarski(A_51)) != k1_xboole_0
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_140,c_51])).

tff(c_166,plain,
    ( k10_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_160])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_117,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.24  
% 1.91/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.24  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.91/1.24  
% 1.91/1.24  %Foreground sorts:
% 1.91/1.24  
% 1.91/1.24  
% 1.91/1.24  %Background operators:
% 1.91/1.24  
% 1.91/1.24  
% 1.91/1.24  %Foreground operators:
% 1.91/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.91/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.91/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.24  
% 1.91/1.25  tff(f_57, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 1.91/1.25  tff(f_38, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.91/1.25  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.91/1.25  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.91/1.25  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.91/1.25  tff(f_43, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.91/1.25  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.25  tff(c_18, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.25  tff(c_72, plain, (~r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_18])).
% 1.91/1.25  tff(c_24, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2')) | k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.25  tff(c_73, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_72, c_24])).
% 1.91/1.25  tff(c_44, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), B_19) | r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.91/1.25  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.25  tff(c_47, plain, (![B_19, A_18]: (r1_xboole_0(B_19, k1_tarski(A_18)) | r2_hidden(A_18, B_19))), inference(resolution, [status(thm)], [c_44, c_2])).
% 1.91/1.25  tff(c_79, plain, (![B_34, A_35]: (k10_relat_1(B_34, A_35)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.91/1.25  tff(c_108, plain, (![B_38, A_39]: (k10_relat_1(B_38, k1_tarski(A_39))=k1_xboole_0 | ~v1_relat_1(B_38) | r2_hidden(A_39, k2_relat_1(B_38)))), inference(resolution, [status(thm)], [c_47, c_79])).
% 1.91/1.25  tff(c_111, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_108, c_72])).
% 1.91/1.25  tff(c_114, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_111])).
% 1.91/1.25  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_114])).
% 1.91/1.25  tff(c_117, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_18])).
% 1.91/1.25  tff(c_118, plain, (r2_hidden('#skF_1', k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_18])).
% 1.91/1.25  tff(c_132, plain, (![B_45, A_46]: (r1_xboole_0(k2_relat_1(B_45), A_46) | k10_relat_1(B_45, A_46)!=k1_xboole_0 | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.91/1.25  tff(c_140, plain, (![A_47, B_48]: (r1_xboole_0(A_47, k2_relat_1(B_48)) | k10_relat_1(B_48, A_47)!=k1_xboole_0 | ~v1_relat_1(B_48))), inference(resolution, [status(thm)], [c_132, c_2])).
% 1.91/1.25  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.25  tff(c_48, plain, (![A_20, C_21, B_22]: (~r2_hidden(A_20, C_21) | ~r1_xboole_0(k2_tarski(A_20, B_22), C_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.25  tff(c_51, plain, (![A_3, C_21]: (~r2_hidden(A_3, C_21) | ~r1_xboole_0(k1_tarski(A_3), C_21))), inference(superposition, [status(thm), theory('equality')], [c_4, c_48])).
% 1.91/1.25  tff(c_160, plain, (![A_51, B_52]: (~r2_hidden(A_51, k2_relat_1(B_52)) | k10_relat_1(B_52, k1_tarski(A_51))!=k1_xboole_0 | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_140, c_51])).
% 1.91/1.25  tff(c_166, plain, (k10_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_118, c_160])).
% 1.91/1.25  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_117, c_166])).
% 1.91/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.25  
% 1.91/1.25  Inference rules
% 1.91/1.25  ----------------------
% 1.91/1.25  #Ref     : 0
% 1.91/1.25  #Sup     : 29
% 1.91/1.25  #Fact    : 0
% 1.91/1.25  #Define  : 0
% 1.91/1.25  #Split   : 1
% 1.91/1.25  #Chain   : 0
% 1.91/1.25  #Close   : 0
% 1.91/1.25  
% 1.91/1.25  Ordering : KBO
% 1.91/1.25  
% 1.91/1.25  Simplification rules
% 1.91/1.25  ----------------------
% 1.91/1.25  #Subsume      : 3
% 1.91/1.25  #Demod        : 5
% 1.91/1.25  #Tautology    : 13
% 1.91/1.25  #SimpNegUnit  : 2
% 1.91/1.25  #BackRed      : 0
% 1.91/1.25  
% 1.91/1.25  #Partial instantiations: 0
% 1.91/1.25  #Strategies tried      : 1
% 1.91/1.25  
% 1.91/1.25  Timing (in seconds)
% 1.91/1.25  ----------------------
% 1.91/1.25  Preprocessing        : 0.30
% 1.91/1.25  Parsing              : 0.16
% 1.91/1.25  CNF conversion       : 0.02
% 1.91/1.25  Main loop            : 0.14
% 1.91/1.25  Inferencing          : 0.06
% 1.91/1.25  Reduction            : 0.03
% 1.91/1.25  Demodulation         : 0.02
% 1.91/1.25  BG Simplification    : 0.01
% 1.91/1.25  Subsumption          : 0.03
% 1.91/1.25  Abstraction          : 0.01
% 1.91/1.25  MUC search           : 0.00
% 1.91/1.25  Cooper               : 0.00
% 1.91/1.25  Total                : 0.47
% 1.91/1.25  Index Insertion      : 0.00
% 1.91/1.25  Index Deletion       : 0.00
% 1.91/1.25  Index Matching       : 0.00
% 1.91/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
