%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:39 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  60 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_35,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(k1_tarski(A_20),B_21)
      | r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(B_7,A_6)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( r1_xboole_0(B_21,k1_tarski(A_20))
      | r2_hidden(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_35,c_8])).

tff(c_65,plain,(
    ! [B_35,A_36] :
      ( k10_relat_1(B_35,A_36) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,(
    ! [B_44,A_45] :
      ( k10_relat_1(B_44,k1_tarski(A_45)) = k1_xboole_0
      | ~ v1_relat_1(B_44)
      | r2_hidden(A_45,k2_relat_1(B_44)) ) ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,k2_relat_1(B_56))
      | k10_relat_1(B_56,k1_tarski('#skF_1'(A_55,k2_relat_1(B_56)))) = k1_xboole_0
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_22,plain,(
    ! [C_16] :
      ( k10_relat_1('#skF_3',k1_tarski(C_16)) != k1_xboole_0
      | ~ r2_hidden(C_16,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_123,plain,(
    ! [A_55] :
      ( ~ r2_hidden('#skF_1'(A_55,k2_relat_1('#skF_3')),'#skF_2')
      | r1_tarski(A_55,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_22])).

tff(c_132,plain,(
    ! [A_57] :
      ( ~ r2_hidden('#skF_1'(A_57,k2_relat_1('#skF_3')),'#skF_2')
      | r1_tarski(A_57,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_123])).

tff(c_140,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k1_enumset1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.88/1.18  
% 1.88/1.18  %Foreground sorts:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Background operators:
% 1.88/1.18  
% 1.88/1.18  
% 1.88/1.18  %Foreground operators:
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.88/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.18  
% 1.88/1.19  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_1)).
% 1.88/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.88/1.19  tff(f_45, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.88/1.19  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.88/1.19  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 1.88/1.19  tff(c_20, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.88/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.19  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.88/1.19  tff(c_35, plain, (![A_20, B_21]: (r1_xboole_0(k1_tarski(A_20), B_21) | r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.19  tff(c_8, plain, (![B_7, A_6]: (r1_xboole_0(B_7, A_6) | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.88/1.19  tff(c_38, plain, (![B_21, A_20]: (r1_xboole_0(B_21, k1_tarski(A_20)) | r2_hidden(A_20, B_21))), inference(resolution, [status(thm)], [c_35, c_8])).
% 1.88/1.19  tff(c_65, plain, (![B_35, A_36]: (k10_relat_1(B_35, A_36)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.19  tff(c_97, plain, (![B_44, A_45]: (k10_relat_1(B_44, k1_tarski(A_45))=k1_xboole_0 | ~v1_relat_1(B_44) | r2_hidden(A_45, k2_relat_1(B_44)))), inference(resolution, [status(thm)], [c_38, c_65])).
% 1.88/1.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.19  tff(c_116, plain, (![A_55, B_56]: (r1_tarski(A_55, k2_relat_1(B_56)) | k10_relat_1(B_56, k1_tarski('#skF_1'(A_55, k2_relat_1(B_56))))=k1_xboole_0 | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_97, c_4])).
% 1.88/1.19  tff(c_22, plain, (![C_16]: (k10_relat_1('#skF_3', k1_tarski(C_16))!=k1_xboole_0 | ~r2_hidden(C_16, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.88/1.19  tff(c_123, plain, (![A_55]: (~r2_hidden('#skF_1'(A_55, k2_relat_1('#skF_3')), '#skF_2') | r1_tarski(A_55, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_22])).
% 1.88/1.19  tff(c_132, plain, (![A_57]: (~r2_hidden('#skF_1'(A_57, k2_relat_1('#skF_3')), '#skF_2') | r1_tarski(A_57, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_123])).
% 1.88/1.19  tff(c_140, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_132])).
% 1.88/1.19  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_140])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 0
% 1.88/1.19  #Sup     : 24
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 0
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 4
% 1.88/1.19  #Demod        : 1
% 1.88/1.19  #Tautology    : 8
% 1.88/1.19  #SimpNegUnit  : 1
% 1.88/1.19  #BackRed      : 0
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.20  Preprocessing        : 0.29
% 1.88/1.20  Parsing              : 0.15
% 1.88/1.20  CNF conversion       : 0.02
% 1.88/1.20  Main loop            : 0.15
% 1.88/1.20  Inferencing          : 0.07
% 1.88/1.20  Reduction            : 0.04
% 1.88/1.20  Demodulation         : 0.03
% 1.88/1.20  BG Simplification    : 0.01
% 1.88/1.20  Subsumption          : 0.03
% 1.88/1.20  Abstraction          : 0.01
% 1.88/1.20  MUC search           : 0.00
% 1.88/1.20  Cooper               : 0.00
% 1.88/1.20  Total                : 0.46
% 1.88/1.20  Index Insertion      : 0.00
% 1.88/1.20  Index Deletion       : 0.00
% 1.95/1.20  Index Matching       : 0.00
% 1.95/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
