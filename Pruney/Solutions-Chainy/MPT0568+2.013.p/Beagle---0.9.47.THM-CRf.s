%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:22 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_41,axiom,(
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
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [A_16] :
      ( v1_relat_1(A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_44])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k10_relat_1(B_27,A_28),k1_relat_1(B_27))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_95,plain,(
    ! [A_28] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_28),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_92])).

tff(c_97,plain,(
    ! [A_28] : r1_tarski(k10_relat_1(k1_xboole_0,A_28),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_95])).

tff(c_10,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_111,plain,(
    ! [C_33,B_34,A_35] :
      ( r2_hidden(C_33,B_34)
      | ~ r2_hidden(C_33,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_2'(A_36),B_37)
      | ~ r1_tarski(A_36,B_37)
      | k1_xboole_0 = A_36 ) ),
    inference(resolution,[status(thm)],[c_10,c_111])).

tff(c_14,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ! [A_18,B_19] : ~ r2_hidden(A_18,k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_70,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_64])).

tff(c_132,plain,(
    ! [A_38] :
      ( ~ r1_tarski(A_38,k1_xboole_0)
      | k1_xboole_0 = A_38 ) ),
    inference(resolution,[status(thm)],[c_118,c_70])).

tff(c_144,plain,(
    ! [A_28] : k10_relat_1(k1_xboole_0,A_28) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_132])).

tff(c_28,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:57:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.19  
% 1.76/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.19  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.76/1.19  
% 1.76/1.19  %Foreground sorts:
% 1.76/1.19  
% 1.76/1.19  
% 1.76/1.19  %Background operators:
% 1.76/1.19  
% 1.76/1.19  
% 1.76/1.19  %Foreground operators:
% 1.76/1.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.76/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.76/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.76/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.76/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.76/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.76/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.76/1.19  
% 1.92/1.20  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.92/1.20  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.92/1.20  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.92/1.20  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.92/1.20  tff(f_41, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.92/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.92/1.20  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.92/1.20  tff(f_50, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.92/1.20  tff(f_64, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.92/1.20  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.20  tff(c_44, plain, (![A_16]: (v1_relat_1(A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.20  tff(c_48, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_44])).
% 1.92/1.20  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.20  tff(c_92, plain, (![B_27, A_28]: (r1_tarski(k10_relat_1(B_27, A_28), k1_relat_1(B_27)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.92/1.20  tff(c_95, plain, (![A_28]: (r1_tarski(k10_relat_1(k1_xboole_0, A_28), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_92])).
% 1.92/1.20  tff(c_97, plain, (![A_28]: (r1_tarski(k10_relat_1(k1_xboole_0, A_28), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_95])).
% 1.92/1.20  tff(c_10, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.20  tff(c_111, plain, (![C_33, B_34, A_35]: (r2_hidden(C_33, B_34) | ~r2_hidden(C_33, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.20  tff(c_118, plain, (![A_36, B_37]: (r2_hidden('#skF_2'(A_36), B_37) | ~r1_tarski(A_36, B_37) | k1_xboole_0=A_36)), inference(resolution, [status(thm)], [c_10, c_111])).
% 1.92/1.20  tff(c_14, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.20  tff(c_64, plain, (![A_18, B_19]: (~r2_hidden(A_18, k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.20  tff(c_70, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_64])).
% 1.92/1.20  tff(c_132, plain, (![A_38]: (~r1_tarski(A_38, k1_xboole_0) | k1_xboole_0=A_38)), inference(resolution, [status(thm)], [c_118, c_70])).
% 1.92/1.20  tff(c_144, plain, (![A_28]: (k10_relat_1(k1_xboole_0, A_28)=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_132])).
% 1.92/1.20  tff(c_28, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.20  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_28])).
% 1.92/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  Inference rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Ref     : 0
% 1.92/1.20  #Sup     : 27
% 1.92/1.20  #Fact    : 0
% 1.92/1.20  #Define  : 0
% 1.92/1.20  #Split   : 0
% 1.92/1.20  #Chain   : 0
% 1.92/1.20  #Close   : 0
% 1.92/1.20  
% 1.92/1.20  Ordering : KBO
% 1.92/1.20  
% 1.92/1.20  Simplification rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Subsume      : 1
% 1.92/1.20  #Demod        : 4
% 1.92/1.20  #Tautology    : 16
% 1.92/1.20  #SimpNegUnit  : 0
% 1.92/1.20  #BackRed      : 2
% 1.92/1.20  
% 1.92/1.20  #Partial instantiations: 0
% 1.92/1.20  #Strategies tried      : 1
% 1.92/1.20  
% 1.92/1.20  Timing (in seconds)
% 1.92/1.20  ----------------------
% 1.92/1.20  Preprocessing        : 0.26
% 1.92/1.20  Parsing              : 0.15
% 1.92/1.20  CNF conversion       : 0.02
% 1.92/1.20  Main loop            : 0.13
% 1.92/1.20  Inferencing          : 0.06
% 1.92/1.20  Reduction            : 0.04
% 1.92/1.20  Demodulation         : 0.03
% 1.92/1.20  BG Simplification    : 0.01
% 1.92/1.20  Subsumption          : 0.02
% 1.92/1.21  Abstraction          : 0.00
% 1.92/1.21  MUC search           : 0.00
% 1.92/1.21  Cooper               : 0.00
% 1.92/1.21  Total                : 0.42
% 1.92/1.21  Index Insertion      : 0.00
% 1.92/1.21  Index Deletion       : 0.00
% 1.92/1.21  Index Matching       : 0.00
% 1.92/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
