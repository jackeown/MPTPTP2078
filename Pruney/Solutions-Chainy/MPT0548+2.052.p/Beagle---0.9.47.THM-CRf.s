%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:42 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  66 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_16,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_2'(A_9),A_9)
      | v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [A_6,C_40] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_40,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_46])).

tff(c_66,plain,(
    ! [C_43] : ~ r2_hidden(C_43,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_71,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_66])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_88,plain,(
    ! [B_48,A_49] :
      ( k7_relat_1(B_48,A_49) = B_48
      | ~ r1_tarski(k1_relat_1(B_48),A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_91,plain,(
    ! [A_49] :
      ( k7_relat_1(k1_xboole_0,A_49) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_49)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_88])).

tff(c_104,plain,(
    ! [A_52] : k7_relat_1(k1_xboole_0,A_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_8,c_91])).

tff(c_18,plain,(
    ! [B_28,A_27] :
      ( k2_relat_1(k7_relat_1(B_28,A_27)) = k9_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_109,plain,(
    ! [A_52] :
      ( k9_relat_1(k1_xboole_0,A_52) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_18])).

tff(c_114,plain,(
    ! [A_52] : k9_relat_1(k1_xboole_0,A_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_20,c_109])).

tff(c_26,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.72/1.14  
% 1.72/1.14  %Foreground sorts:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Background operators:
% 1.72/1.14  
% 1.72/1.14  
% 1.72/1.14  %Foreground operators:
% 1.72/1.14  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.72/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.72/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.72/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.72/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.72/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.72/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.72/1.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.72/1.14  
% 1.72/1.15  tff(f_55, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.72/1.15  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.72/1.15  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.72/1.15  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.72/1.15  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.72/1.15  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.72/1.15  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 1.72/1.15  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.72/1.15  tff(f_71, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.72/1.15  tff(c_16, plain, (![A_9]: (r2_hidden('#skF_2'(A_9), A_9) | v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.72/1.15  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.72/1.15  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.72/1.15  tff(c_46, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.15  tff(c_53, plain, (![A_6, C_40]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_46])).
% 1.72/1.15  tff(c_66, plain, (![C_43]: (~r2_hidden(C_43, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_53])).
% 1.72/1.15  tff(c_71, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_66])).
% 1.72/1.15  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.72/1.15  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.72/1.15  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.72/1.15  tff(c_88, plain, (![B_48, A_49]: (k7_relat_1(B_48, A_49)=B_48 | ~r1_tarski(k1_relat_1(B_48), A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.72/1.15  tff(c_91, plain, (![A_49]: (k7_relat_1(k1_xboole_0, A_49)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_49) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_88])).
% 1.72/1.15  tff(c_104, plain, (![A_52]: (k7_relat_1(k1_xboole_0, A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_8, c_91])).
% 1.72/1.15  tff(c_18, plain, (![B_28, A_27]: (k2_relat_1(k7_relat_1(B_28, A_27))=k9_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.72/1.15  tff(c_109, plain, (![A_52]: (k9_relat_1(k1_xboole_0, A_52)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_104, c_18])).
% 1.72/1.15  tff(c_114, plain, (![A_52]: (k9_relat_1(k1_xboole_0, A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_20, c_109])).
% 1.72/1.15  tff(c_26, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.72/1.15  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_26])).
% 1.72/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.15  
% 1.72/1.15  Inference rules
% 1.72/1.15  ----------------------
% 1.72/1.15  #Ref     : 0
% 1.72/1.15  #Sup     : 21
% 1.72/1.15  #Fact    : 0
% 1.72/1.15  #Define  : 0
% 1.72/1.15  #Split   : 0
% 1.72/1.15  #Chain   : 0
% 1.72/1.15  #Close   : 0
% 1.72/1.15  
% 1.72/1.15  Ordering : KBO
% 1.72/1.15  
% 1.72/1.15  Simplification rules
% 1.72/1.15  ----------------------
% 1.72/1.15  #Subsume      : 0
% 1.72/1.15  #Demod        : 9
% 1.72/1.15  #Tautology    : 15
% 1.72/1.15  #SimpNegUnit  : 1
% 1.72/1.15  #BackRed      : 1
% 1.72/1.15  
% 1.72/1.15  #Partial instantiations: 0
% 1.72/1.15  #Strategies tried      : 1
% 1.72/1.15  
% 1.72/1.15  Timing (in seconds)
% 1.72/1.15  ----------------------
% 1.72/1.15  Preprocessing        : 0.28
% 1.72/1.15  Parsing              : 0.16
% 1.72/1.15  CNF conversion       : 0.02
% 1.72/1.15  Main loop            : 0.12
% 1.72/1.15  Inferencing          : 0.06
% 1.72/1.15  Reduction            : 0.03
% 1.72/1.15  Demodulation         : 0.02
% 1.72/1.15  BG Simplification    : 0.01
% 1.72/1.15  Subsumption          : 0.01
% 1.72/1.15  Abstraction          : 0.00
% 1.72/1.15  MUC search           : 0.00
% 1.72/1.15  Cooper               : 0.00
% 1.72/1.15  Total                : 0.42
% 1.72/1.15  Index Insertion      : 0.00
% 1.72/1.16  Index Deletion       : 0.00
% 1.72/1.16  Index Matching       : 0.00
% 1.72/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
