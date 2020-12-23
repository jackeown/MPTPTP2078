%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:30 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 (  85 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_relat_2 > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> r1_relat_2(A,k3_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_relat_2)).

tff(f_68,negated_conjecture,(
    ~ ! [A] : v1_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord2)).

tff(c_36,plain,(
    ! [A_25] : v1_relat_1(k1_wellord2(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_6,B_12] :
      ( r2_hidden('#skF_2'(A_6,B_12),B_12)
      | r1_relat_2(A_6,B_12)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_34] : r1_tarski(A_34,A_34) ),
    inference(resolution,[status(thm)],[c_78,c_4])).

tff(c_32,plain,(
    ! [C_23,D_24,A_17] :
      ( r2_hidden(k4_tarski(C_23,D_24),k1_wellord2(A_17))
      | ~ r1_tarski(C_23,D_24)
      | ~ r2_hidden(D_24,A_17)
      | ~ r2_hidden(C_23,A_17)
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_169,plain,(
    ! [C_60,D_61,A_62] :
      ( r2_hidden(k4_tarski(C_60,D_61),k1_wellord2(A_62))
      | ~ r1_tarski(C_60,D_61)
      | ~ r2_hidden(D_61,A_62)
      | ~ r2_hidden(C_60,A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32])).

tff(c_10,plain,(
    ! [A_6,B_12] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_6,B_12),'#skF_2'(A_6,B_12)),A_6)
      | r1_relat_2(A_6,B_12)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_177,plain,(
    ! [A_62,B_12] :
      ( r1_relat_2(k1_wellord2(A_62),B_12)
      | ~ v1_relat_1(k1_wellord2(A_62))
      | ~ r1_tarski('#skF_2'(k1_wellord2(A_62),B_12),'#skF_2'(k1_wellord2(A_62),B_12))
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_62),B_12),A_62) ) ),
    inference(resolution,[status(thm)],[c_169,c_10])).

tff(c_190,plain,(
    ! [A_63,B_64] :
      ( r1_relat_2(k1_wellord2(A_63),B_64)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_63),B_64),A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_36,c_177])).

tff(c_198,plain,(
    ! [B_12] :
      ( r1_relat_2(k1_wellord2(B_12),B_12)
      | ~ v1_relat_1(k1_wellord2(B_12)) ) ),
    inference(resolution,[status(thm)],[c_12,c_190])).

tff(c_204,plain,(
    ! [B_12] : r1_relat_2(k1_wellord2(B_12),B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_198])).

tff(c_30,plain,(
    ! [A_17] :
      ( k3_relat_1(k1_wellord2(A_17)) = A_17
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    ! [A_17] : k3_relat_1(k1_wellord2(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30])).

tff(c_62,plain,(
    ! [A_31] :
      ( v1_relat_2(A_31)
      | ~ r1_relat_2(A_31,k3_relat_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [A_17] :
      ( v1_relat_2(k1_wellord2(A_17))
      | ~ r1_relat_2(k1_wellord2(A_17),A_17)
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_62])).

tff(c_71,plain,(
    ! [A_17] :
      ( v1_relat_2(k1_wellord2(A_17))
      | ~ r1_relat_2(k1_wellord2(A_17),A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_68])).

tff(c_206,plain,(
    ! [A_17] : v1_relat_2(k1_wellord2(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_71])).

tff(c_38,plain,(
    ~ v1_relat_2(k1_wellord2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:26:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.30  
% 1.96/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.30  %$ r2_hidden > r1_tarski > r1_relat_2 > v1_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 1.96/1.30  
% 1.96/1.30  %Foreground sorts:
% 1.96/1.30  
% 1.96/1.30  
% 1.96/1.30  %Background operators:
% 1.96/1.30  
% 1.96/1.30  
% 1.96/1.30  %Foreground operators:
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.30  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 1.96/1.30  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.96/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.96/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.30  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 1.96/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.30  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.96/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.96/1.30  
% 1.96/1.31  tff(f_65, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.96/1.31  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_2)).
% 1.96/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.96/1.31  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 1.96/1.31  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> r1_relat_2(A, k3_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_relat_2)).
% 1.96/1.31  tff(f_68, negated_conjecture, ~(![A]: v1_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_wellord2)).
% 1.96/1.31  tff(c_36, plain, (![A_25]: (v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.96/1.31  tff(c_12, plain, (![A_6, B_12]: (r2_hidden('#skF_2'(A_6, B_12), B_12) | r1_relat_2(A_6, B_12) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.31  tff(c_78, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(A_34, B_35), A_34) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.31  tff(c_83, plain, (![A_34]: (r1_tarski(A_34, A_34))), inference(resolution, [status(thm)], [c_78, c_4])).
% 1.96/1.31  tff(c_32, plain, (![C_23, D_24, A_17]: (r2_hidden(k4_tarski(C_23, D_24), k1_wellord2(A_17)) | ~r1_tarski(C_23, D_24) | ~r2_hidden(D_24, A_17) | ~r2_hidden(C_23, A_17) | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.96/1.31  tff(c_169, plain, (![C_60, D_61, A_62]: (r2_hidden(k4_tarski(C_60, D_61), k1_wellord2(A_62)) | ~r1_tarski(C_60, D_61) | ~r2_hidden(D_61, A_62) | ~r2_hidden(C_60, A_62))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32])).
% 1.96/1.31  tff(c_10, plain, (![A_6, B_12]: (~r2_hidden(k4_tarski('#skF_2'(A_6, B_12), '#skF_2'(A_6, B_12)), A_6) | r1_relat_2(A_6, B_12) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.96/1.31  tff(c_177, plain, (![A_62, B_12]: (r1_relat_2(k1_wellord2(A_62), B_12) | ~v1_relat_1(k1_wellord2(A_62)) | ~r1_tarski('#skF_2'(k1_wellord2(A_62), B_12), '#skF_2'(k1_wellord2(A_62), B_12)) | ~r2_hidden('#skF_2'(k1_wellord2(A_62), B_12), A_62))), inference(resolution, [status(thm)], [c_169, c_10])).
% 1.96/1.31  tff(c_190, plain, (![A_63, B_64]: (r1_relat_2(k1_wellord2(A_63), B_64) | ~r2_hidden('#skF_2'(k1_wellord2(A_63), B_64), A_63))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_36, c_177])).
% 1.96/1.31  tff(c_198, plain, (![B_12]: (r1_relat_2(k1_wellord2(B_12), B_12) | ~v1_relat_1(k1_wellord2(B_12)))), inference(resolution, [status(thm)], [c_12, c_190])).
% 1.96/1.31  tff(c_204, plain, (![B_12]: (r1_relat_2(k1_wellord2(B_12), B_12))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_198])).
% 1.96/1.31  tff(c_30, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17 | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.96/1.31  tff(c_44, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30])).
% 1.96/1.31  tff(c_62, plain, (![A_31]: (v1_relat_2(A_31) | ~r1_relat_2(A_31, k3_relat_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.96/1.31  tff(c_68, plain, (![A_17]: (v1_relat_2(k1_wellord2(A_17)) | ~r1_relat_2(k1_wellord2(A_17), A_17) | ~v1_relat_1(k1_wellord2(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_62])).
% 1.96/1.31  tff(c_71, plain, (![A_17]: (v1_relat_2(k1_wellord2(A_17)) | ~r1_relat_2(k1_wellord2(A_17), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_68])).
% 1.96/1.31  tff(c_206, plain, (![A_17]: (v1_relat_2(k1_wellord2(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_71])).
% 1.96/1.31  tff(c_38, plain, (~v1_relat_2(k1_wellord2('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.96/1.31  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_38])).
% 1.96/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.31  
% 1.96/1.31  Inference rules
% 1.96/1.31  ----------------------
% 1.96/1.31  #Ref     : 0
% 1.96/1.31  #Sup     : 33
% 1.96/1.31  #Fact    : 0
% 1.96/1.31  #Define  : 0
% 1.96/1.31  #Split   : 0
% 1.96/1.31  #Chain   : 0
% 1.96/1.31  #Close   : 0
% 1.96/1.31  
% 1.96/1.31  Ordering : KBO
% 1.96/1.31  
% 1.96/1.31  Simplification rules
% 1.96/1.31  ----------------------
% 1.96/1.31  #Subsume      : 1
% 1.96/1.31  #Demod        : 40
% 1.96/1.31  #Tautology    : 15
% 1.96/1.31  #SimpNegUnit  : 0
% 1.96/1.31  #BackRed      : 2
% 1.96/1.31  
% 1.96/1.31  #Partial instantiations: 0
% 1.96/1.31  #Strategies tried      : 1
% 1.96/1.31  
% 1.96/1.31  Timing (in seconds)
% 1.96/1.31  ----------------------
% 1.96/1.31  Preprocessing        : 0.32
% 1.96/1.31  Parsing              : 0.16
% 1.96/1.31  CNF conversion       : 0.03
% 1.96/1.31  Main loop            : 0.18
% 1.96/1.31  Inferencing          : 0.07
% 1.96/1.31  Reduction            : 0.05
% 1.96/1.31  Demodulation         : 0.04
% 1.96/1.31  BG Simplification    : 0.02
% 1.96/1.31  Subsumption          : 0.04
% 1.96/1.31  Abstraction          : 0.01
% 1.96/1.31  MUC search           : 0.00
% 1.96/1.31  Cooper               : 0.00
% 1.96/1.31  Total                : 0.53
% 1.96/1.31  Index Insertion      : 0.00
% 1.96/1.31  Index Deletion       : 0.00
% 1.96/1.31  Index Matching       : 0.00
% 1.96/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
