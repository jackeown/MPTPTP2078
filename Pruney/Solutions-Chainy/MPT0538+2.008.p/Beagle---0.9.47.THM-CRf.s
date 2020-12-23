%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:23 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  48 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_40,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_6,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_28,plain,(
    ! [A_14] :
      ( v1_relat_1(A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_23,c_28])).

tff(c_18,plain,(
    ! [A_11] :
      ( v1_xboole_0(k2_relat_1(A_11))
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_45,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_2'(A_20,B_21),A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_20,B_21] :
      ( ~ v1_xboole_0(A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_73,plain,(
    ! [A_32,B_33] :
      ( k8_relat_1(A_32,B_33) = B_33
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_102,plain,(
    ! [B_37,B_38] :
      ( k8_relat_1(B_37,B_38) = B_38
      | ~ v1_relat_1(B_38)
      | ~ v1_xboole_0(k2_relat_1(B_38)) ) ),
    inference(resolution,[status(thm)],[c_49,c_73])).

tff(c_106,plain,(
    ! [B_39,A_40] :
      ( k8_relat_1(B_39,A_40) = A_40
      | ~ v1_relat_1(A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_18,c_102])).

tff(c_110,plain,(
    ! [B_39] :
      ( k8_relat_1(B_39,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_23,c_106])).

tff(c_114,plain,(
    ! [B_39] : k8_relat_1(B_39,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110])).

tff(c_22,plain,(
    k8_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.14  
% 1.73/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.14  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.73/1.14  
% 1.73/1.14  %Foreground sorts:
% 1.73/1.14  
% 1.73/1.14  
% 1.73/1.14  %Background operators:
% 1.73/1.14  
% 1.73/1.14  
% 1.73/1.14  %Foreground operators:
% 1.73/1.14  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.73/1.14  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.73/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.73/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.14  
% 1.73/1.15  tff(f_32, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 1.73/1.15  tff(f_40, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 1.73/1.15  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.73/1.15  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 1.73/1.15  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.73/1.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.73/1.15  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.73/1.15  tff(f_57, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.73/1.15  tff(c_6, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.73/1.15  tff(c_14, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.73/1.15  tff(c_23, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 1.73/1.15  tff(c_28, plain, (![A_14]: (v1_relat_1(A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.73/1.15  tff(c_32, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_23, c_28])).
% 1.73/1.15  tff(c_18, plain, (![A_11]: (v1_xboole_0(k2_relat_1(A_11)) | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.15  tff(c_45, plain, (![A_20, B_21]: (r2_hidden('#skF_2'(A_20, B_21), A_20) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.73/1.15  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.15  tff(c_49, plain, (![A_20, B_21]: (~v1_xboole_0(A_20) | r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_45, c_2])).
% 1.73/1.15  tff(c_73, plain, (![A_32, B_33]: (k8_relat_1(A_32, B_33)=B_33 | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.73/1.15  tff(c_102, plain, (![B_37, B_38]: (k8_relat_1(B_37, B_38)=B_38 | ~v1_relat_1(B_38) | ~v1_xboole_0(k2_relat_1(B_38)))), inference(resolution, [status(thm)], [c_49, c_73])).
% 1.73/1.15  tff(c_106, plain, (![B_39, A_40]: (k8_relat_1(B_39, A_40)=A_40 | ~v1_relat_1(A_40) | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_18, c_102])).
% 1.73/1.15  tff(c_110, plain, (![B_39]: (k8_relat_1(B_39, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_23, c_106])).
% 1.73/1.15  tff(c_114, plain, (![B_39]: (k8_relat_1(B_39, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_110])).
% 1.73/1.15  tff(c_22, plain, (k8_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.73/1.15  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_22])).
% 1.73/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.15  
% 1.73/1.15  Inference rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Ref     : 0
% 1.73/1.15  #Sup     : 20
% 1.73/1.15  #Fact    : 0
% 1.73/1.15  #Define  : 0
% 1.73/1.15  #Split   : 0
% 1.73/1.15  #Chain   : 0
% 1.73/1.15  #Close   : 0
% 1.73/1.15  
% 1.73/1.15  Ordering : KBO
% 1.73/1.15  
% 1.73/1.15  Simplification rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Subsume      : 0
% 1.73/1.15  #Demod        : 3
% 1.73/1.15  #Tautology    : 7
% 1.73/1.15  #SimpNegUnit  : 0
% 1.73/1.15  #BackRed      : 1
% 1.73/1.15  
% 1.73/1.15  #Partial instantiations: 0
% 1.73/1.15  #Strategies tried      : 1
% 1.73/1.15  
% 1.73/1.15  Timing (in seconds)
% 1.73/1.15  ----------------------
% 1.73/1.15  Preprocessing        : 0.27
% 1.73/1.15  Parsing              : 0.14
% 1.73/1.15  CNF conversion       : 0.02
% 1.73/1.15  Main loop            : 0.13
% 1.73/1.15  Inferencing          : 0.05
% 1.73/1.15  Reduction            : 0.03
% 1.73/1.15  Demodulation         : 0.02
% 1.73/1.15  BG Simplification    : 0.01
% 1.73/1.15  Subsumption          : 0.02
% 1.73/1.15  Abstraction          : 0.01
% 1.73/1.15  MUC search           : 0.00
% 1.73/1.15  Cooper               : 0.00
% 1.73/1.15  Total                : 0.42
% 1.73/1.15  Index Insertion      : 0.00
% 1.73/1.15  Index Deletion       : 0.00
% 1.73/1.15  Index Matching       : 0.00
% 1.73/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
