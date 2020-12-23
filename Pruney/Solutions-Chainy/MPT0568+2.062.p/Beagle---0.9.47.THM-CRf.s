%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:28 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   43 (  72 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   52 ( 109 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_3'(A_36),A_36)
      | v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(A_37)
      | v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_42,c_2])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_20,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden(k4_tarski(A_25,'#skF_6'(A_25,B_26,C_27)),C_27)
      | ~ r2_hidden(A_25,k10_relat_1(C_27,B_26))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_73,plain,(
    ! [A_48,B_49,C_50] :
      ( r2_hidden('#skF_6'(A_48,B_49,C_50),B_49)
      | ~ r2_hidden(A_48,k10_relat_1(C_50,B_49))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ! [B_51,A_52,C_53] :
      ( ~ v1_xboole_0(B_51)
      | ~ r2_hidden(A_52,k10_relat_1(C_53,B_51))
      | ~ v1_relat_1(C_53) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_114,plain,(
    ! [B_61,C_62] :
      ( ~ v1_xboole_0(B_61)
      | ~ v1_relat_1(C_62)
      | k10_relat_1(C_62,B_61) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_131,plain,(
    ! [C_66] :
      ( ~ v1_relat_1(C_66)
      | k10_relat_1(C_66,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_139,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_131])).

tff(c_77,plain,(
    ! [B_49,A_48,C_50] :
      ( ~ v1_xboole_0(B_49)
      | ~ r2_hidden(A_48,k10_relat_1(C_50,B_49))
      | ~ v1_relat_1(C_50) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_149,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_48,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_77])).

tff(c_159,plain,(
    ! [A_67] : ~ r2_hidden(A_67,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_6,c_149])).

tff(c_163,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden(A_25,k10_relat_1(k1_xboole_0,B_26))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_159])).

tff(c_190,plain,(
    ! [A_68,B_69] : ~ r2_hidden(A_68,k10_relat_1(k1_xboole_0,B_69)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_163])).

tff(c_217,plain,(
    ! [B_69] : k10_relat_1(k1_xboole_0,B_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_190])).

tff(c_24,plain,(
    k10_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  
% 1.92/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.22  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4
% 1.92/1.22  
% 1.92/1.22  %Foreground sorts:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Background operators:
% 1.92/1.22  
% 1.92/1.22  
% 1.92/1.22  %Foreground operators:
% 1.92/1.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.22  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.92/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.92/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.92/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.92/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.92/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.22  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.92/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.92/1.22  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.92/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.92/1.22  
% 1.92/1.23  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.92/1.23  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.92/1.23  tff(f_50, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.92/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.92/1.23  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.92/1.23  tff(f_64, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.92/1.23  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.92/1.23  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.23  tff(c_42, plain, (![A_36]: (r2_hidden('#skF_3'(A_36), A_36) | v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.23  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.23  tff(c_47, plain, (![A_37]: (~v1_xboole_0(A_37) | v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_42, c_2])).
% 1.92/1.23  tff(c_51, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_47])).
% 1.92/1.23  tff(c_20, plain, (![A_25, B_26, C_27]: (r2_hidden(k4_tarski(A_25, '#skF_6'(A_25, B_26, C_27)), C_27) | ~r2_hidden(A_25, k10_relat_1(C_27, B_26)) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.23  tff(c_73, plain, (![A_48, B_49, C_50]: (r2_hidden('#skF_6'(A_48, B_49, C_50), B_49) | ~r2_hidden(A_48, k10_relat_1(C_50, B_49)) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.23  tff(c_78, plain, (![B_51, A_52, C_53]: (~v1_xboole_0(B_51) | ~r2_hidden(A_52, k10_relat_1(C_53, B_51)) | ~v1_relat_1(C_53))), inference(resolution, [status(thm)], [c_73, c_2])).
% 1.92/1.23  tff(c_114, plain, (![B_61, C_62]: (~v1_xboole_0(B_61) | ~v1_relat_1(C_62) | k10_relat_1(C_62, B_61)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_78])).
% 1.92/1.23  tff(c_131, plain, (![C_66]: (~v1_relat_1(C_66) | k10_relat_1(C_66, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_114])).
% 1.92/1.23  tff(c_139, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_131])).
% 1.92/1.23  tff(c_77, plain, (![B_49, A_48, C_50]: (~v1_xboole_0(B_49) | ~r2_hidden(A_48, k10_relat_1(C_50, B_49)) | ~v1_relat_1(C_50))), inference(resolution, [status(thm)], [c_73, c_2])).
% 1.92/1.23  tff(c_149, plain, (![A_48]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_48, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_139, c_77])).
% 1.92/1.23  tff(c_159, plain, (![A_67]: (~r2_hidden(A_67, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_6, c_149])).
% 1.92/1.23  tff(c_163, plain, (![A_25, B_26]: (~r2_hidden(A_25, k10_relat_1(k1_xboole_0, B_26)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_159])).
% 1.92/1.23  tff(c_190, plain, (![A_68, B_69]: (~r2_hidden(A_68, k10_relat_1(k1_xboole_0, B_69)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_163])).
% 1.92/1.23  tff(c_217, plain, (![B_69]: (k10_relat_1(k1_xboole_0, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_190])).
% 1.92/1.23  tff(c_24, plain, (k10_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.23  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_24])).
% 1.92/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.23  
% 1.92/1.23  Inference rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Ref     : 1
% 1.92/1.23  #Sup     : 51
% 1.92/1.23  #Fact    : 0
% 1.92/1.23  #Define  : 0
% 1.92/1.23  #Split   : 0
% 1.92/1.23  #Chain   : 0
% 1.92/1.23  #Close   : 0
% 1.92/1.23  
% 1.92/1.23  Ordering : KBO
% 1.92/1.23  
% 1.92/1.23  Simplification rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Subsume      : 3
% 1.92/1.23  #Demod        : 21
% 1.92/1.23  #Tautology    : 18
% 1.92/1.23  #SimpNegUnit  : 0
% 1.92/1.23  #BackRed      : 4
% 1.92/1.23  
% 1.92/1.23  #Partial instantiations: 0
% 1.92/1.23  #Strategies tried      : 1
% 1.92/1.23  
% 1.92/1.23  Timing (in seconds)
% 1.92/1.23  ----------------------
% 1.92/1.23  Preprocessing        : 0.26
% 1.92/1.23  Parsing              : 0.14
% 1.92/1.24  CNF conversion       : 0.02
% 1.92/1.24  Main loop            : 0.19
% 1.92/1.24  Inferencing          : 0.08
% 2.02/1.24  Reduction            : 0.05
% 2.02/1.24  Demodulation         : 0.03
% 2.02/1.24  BG Simplification    : 0.01
% 2.02/1.24  Subsumption          : 0.04
% 2.02/1.24  Abstraction          : 0.01
% 2.02/1.24  MUC search           : 0.00
% 2.02/1.24  Cooper               : 0.00
% 2.02/1.24  Total                : 0.48
% 2.02/1.24  Index Insertion      : 0.00
% 2.02/1.24  Index Deletion       : 0.00
% 2.02/1.24  Index Matching       : 0.00
% 2.02/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
