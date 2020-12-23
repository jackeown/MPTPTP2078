%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:34 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  85 expanded)
%              Number of equality atoms :   23 (  35 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k2_relat_1(B))
        <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_34,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,
    ( r2_hidden('#skF_4',k2_relat_1('#skF_5'))
    | k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_81,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_40])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,k1_tarski(B_14)) = A_13
      | r2_hidden(B_14,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [B_39,A_40] :
      ( k10_relat_1(B_39,A_40) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_39),A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_250,plain,(
    ! [B_62,B_63] :
      ( k10_relat_1(B_62,B_63) = k1_xboole_0
      | ~ v1_relat_1(B_62)
      | k4_xboole_0(k2_relat_1(B_62),B_63) != k2_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_10,c_102])).

tff(c_261,plain,(
    ! [B_64,B_65] :
      ( k10_relat_1(B_64,k1_tarski(B_65)) = k1_xboole_0
      | ~ v1_relat_1(B_64)
      | r2_hidden(B_65,k2_relat_1(B_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_250])).

tff(c_270,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_261,c_80])).

tff(c_275,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_270])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_275])).

tff(c_278,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_279,plain,(
    r2_hidden('#skF_4',k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_316,plain,(
    ! [B_75,A_76] :
      ( r1_xboole_0(k2_relat_1(B_75),A_76)
      | k10_relat_1(B_75,A_76) != k1_xboole_0
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_469,plain,(
    ! [B_96,A_97] :
      ( k4_xboole_0(k2_relat_1(B_96),A_97) = k2_relat_1(B_96)
      | k10_relat_1(B_96,A_97) != k1_xboole_0
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_316,c_8])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( ~ r2_hidden(B_14,A_13)
      | k4_xboole_0(A_13,k1_tarski(B_14)) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_508,plain,(
    ! [B_98,B_99] :
      ( ~ r2_hidden(B_98,k2_relat_1(B_99))
      | k10_relat_1(B_99,k1_tarski(B_98)) != k1_xboole_0
      | ~ v1_relat_1(B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_24])).

tff(c_515,plain,
    ( k10_relat_1('#skF_5',k1_tarski('#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_279,c_508])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_278,c_515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.33  
% 2.14/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.33  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.14/1.33  
% 2.14/1.33  %Foreground sorts:
% 2.14/1.33  
% 2.14/1.33  
% 2.14/1.33  %Background operators:
% 2.14/1.33  
% 2.14/1.33  
% 2.14/1.33  %Foreground operators:
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.14/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.14/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.33  
% 2.53/1.34  tff(f_73, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.53/1.34  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.53/1.34  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.53/1.34  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.53/1.34  tff(c_32, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.53/1.34  tff(c_34, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.53/1.34  tff(c_80, plain, (~r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_34])).
% 2.53/1.34  tff(c_40, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5')) | k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.53/1.34  tff(c_81, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_40])).
% 2.53/1.34  tff(c_26, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k1_tarski(B_14))=A_13 | r2_hidden(B_14, A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.34  tff(c_10, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k4_xboole_0(A_6, B_7)!=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.34  tff(c_102, plain, (![B_39, A_40]: (k10_relat_1(B_39, A_40)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_39), A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.34  tff(c_250, plain, (![B_62, B_63]: (k10_relat_1(B_62, B_63)=k1_xboole_0 | ~v1_relat_1(B_62) | k4_xboole_0(k2_relat_1(B_62), B_63)!=k2_relat_1(B_62))), inference(resolution, [status(thm)], [c_10, c_102])).
% 2.53/1.34  tff(c_261, plain, (![B_64, B_65]: (k10_relat_1(B_64, k1_tarski(B_65))=k1_xboole_0 | ~v1_relat_1(B_64) | r2_hidden(B_65, k2_relat_1(B_64)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_250])).
% 2.53/1.34  tff(c_270, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_261, c_80])).
% 2.53/1.34  tff(c_275, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_270])).
% 2.53/1.34  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_275])).
% 2.53/1.34  tff(c_278, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 2.53/1.34  tff(c_279, plain, (r2_hidden('#skF_4', k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_34])).
% 2.53/1.34  tff(c_316, plain, (![B_75, A_76]: (r1_xboole_0(k2_relat_1(B_75), A_76) | k10_relat_1(B_75, A_76)!=k1_xboole_0 | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.53/1.34  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.53/1.34  tff(c_469, plain, (![B_96, A_97]: (k4_xboole_0(k2_relat_1(B_96), A_97)=k2_relat_1(B_96) | k10_relat_1(B_96, A_97)!=k1_xboole_0 | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_316, c_8])).
% 2.53/1.34  tff(c_24, plain, (![B_14, A_13]: (~r2_hidden(B_14, A_13) | k4_xboole_0(A_13, k1_tarski(B_14))!=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.53/1.34  tff(c_508, plain, (![B_98, B_99]: (~r2_hidden(B_98, k2_relat_1(B_99)) | k10_relat_1(B_99, k1_tarski(B_98))!=k1_xboole_0 | ~v1_relat_1(B_99))), inference(superposition, [status(thm), theory('equality')], [c_469, c_24])).
% 2.53/1.34  tff(c_515, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_279, c_508])).
% 2.53/1.34  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_278, c_515])).
% 2.53/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.34  
% 2.53/1.34  Inference rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Ref     : 0
% 2.53/1.34  #Sup     : 108
% 2.53/1.34  #Fact    : 0
% 2.53/1.34  #Define  : 0
% 2.53/1.34  #Split   : 1
% 2.53/1.34  #Chain   : 0
% 2.53/1.34  #Close   : 0
% 2.53/1.34  
% 2.53/1.34  Ordering : KBO
% 2.53/1.34  
% 2.53/1.34  Simplification rules
% 2.53/1.34  ----------------------
% 2.53/1.34  #Subsume      : 6
% 2.53/1.34  #Demod        : 9
% 2.53/1.34  #Tautology    : 55
% 2.53/1.34  #SimpNegUnit  : 2
% 2.53/1.34  #BackRed      : 0
% 2.53/1.34  
% 2.53/1.34  #Partial instantiations: 0
% 2.53/1.34  #Strategies tried      : 1
% 2.53/1.34  
% 2.53/1.34  Timing (in seconds)
% 2.53/1.34  ----------------------
% 2.53/1.35  Preprocessing        : 0.30
% 2.53/1.35  Parsing              : 0.16
% 2.53/1.35  CNF conversion       : 0.02
% 2.53/1.35  Main loop            : 0.28
% 2.53/1.35  Inferencing          : 0.12
% 2.53/1.35  Reduction            : 0.06
% 2.53/1.35  Demodulation         : 0.04
% 2.53/1.35  BG Simplification    : 0.02
% 2.53/1.35  Subsumption          : 0.06
% 2.53/1.35  Abstraction          : 0.02
% 2.53/1.35  MUC search           : 0.00
% 2.53/1.35  Cooper               : 0.00
% 2.53/1.35  Total                : 0.60
% 2.53/1.35  Index Insertion      : 0.00
% 2.53/1.35  Index Deletion       : 0.00
% 2.53/1.35  Index Matching       : 0.00
% 2.53/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
