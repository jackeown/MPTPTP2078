%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:21 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   46 (  48 expanded)
%              Number of leaves         :   26 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 (  53 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_71,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    ! [A_31,B_32] :
      ( ~ r1_xboole_0(A_31,B_32)
      | v1_xboole_0(k3_xboole_0(A_31,B_32)) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [B_23,A_24] :
      ( ~ v1_xboole_0(B_23)
      | B_23 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_76,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_64,c_50])).

tff(c_80,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_76])).

tff(c_36,plain,(
    ! [A_19] :
      ( v1_relat_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_81,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(k10_relat_1(B_35,A_36),k1_relat_1(B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,(
    ! [A_36] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_36),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_81])).

tff(c_115,plain,(
    ! [A_39] : r1_tarski(k10_relat_1(k1_xboole_0,A_39),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_87])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_118,plain,(
    ! [A_39] : k3_xboole_0(k10_relat_1(k1_xboole_0,A_39),k1_xboole_0) = k10_relat_1(k1_xboole_0,A_39) ),
    inference(resolution,[status(thm)],[c_115,c_12])).

tff(c_120,plain,(
    ! [A_39] : k10_relat_1(k1_xboole_0,A_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_118])).

tff(c_26,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.13  
% 1.73/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.73/1.13  
% 1.73/1.13  %Foreground sorts:
% 1.73/1.13  
% 1.73/1.13  
% 1.73/1.13  %Background operators:
% 1.73/1.13  
% 1.73/1.13  
% 1.73/1.13  %Foreground operators:
% 1.73/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.73/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.73/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.73/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.73/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.13  
% 1.73/1.15  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.73/1.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.73/1.15  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.73/1.15  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.73/1.15  tff(f_60, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.73/1.15  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.73/1.15  tff(f_71, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.73/1.15  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.73/1.15  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.73/1.15  tff(f_74, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.73/1.15  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.73/1.15  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.15  tff(c_58, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.73/1.15  tff(c_64, plain, (![A_31, B_32]: (~r1_xboole_0(A_31, B_32) | v1_xboole_0(k3_xboole_0(A_31, B_32)))), inference(resolution, [status(thm)], [c_4, c_58])).
% 1.73/1.15  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.73/1.15  tff(c_47, plain, (![B_23, A_24]: (~v1_xboole_0(B_23) | B_23=A_24 | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.73/1.15  tff(c_50, plain, (![A_24]: (k1_xboole_0=A_24 | ~v1_xboole_0(A_24))), inference(resolution, [status(thm)], [c_6, c_47])).
% 1.73/1.15  tff(c_76, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_xboole_0(A_33, B_34))), inference(resolution, [status(thm)], [c_64, c_50])).
% 1.73/1.15  tff(c_80, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_76])).
% 1.73/1.15  tff(c_36, plain, (![A_19]: (v1_relat_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.73/1.15  tff(c_40, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_36])).
% 1.73/1.15  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.73/1.15  tff(c_81, plain, (![B_35, A_36]: (r1_tarski(k10_relat_1(B_35, A_36), k1_relat_1(B_35)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.73/1.15  tff(c_87, plain, (![A_36]: (r1_tarski(k10_relat_1(k1_xboole_0, A_36), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_81])).
% 1.73/1.15  tff(c_115, plain, (![A_39]: (r1_tarski(k10_relat_1(k1_xboole_0, A_39), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_87])).
% 1.73/1.15  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.15  tff(c_118, plain, (![A_39]: (k3_xboole_0(k10_relat_1(k1_xboole_0, A_39), k1_xboole_0)=k10_relat_1(k1_xboole_0, A_39))), inference(resolution, [status(thm)], [c_115, c_12])).
% 1.73/1.15  tff(c_120, plain, (![A_39]: (k10_relat_1(k1_xboole_0, A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_118])).
% 1.73/1.15  tff(c_26, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.73/1.15  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_26])).
% 1.73/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.15  
% 1.73/1.15  Inference rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Ref     : 0
% 1.73/1.15  #Sup     : 24
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
% 1.73/1.15  #Demod        : 9
% 1.73/1.15  #Tautology    : 12
% 1.73/1.15  #SimpNegUnit  : 1
% 1.73/1.15  #BackRed      : 2
% 1.73/1.15  
% 1.73/1.15  #Partial instantiations: 0
% 1.73/1.15  #Strategies tried      : 1
% 1.73/1.15  
% 1.73/1.15  Timing (in seconds)
% 1.73/1.15  ----------------------
% 1.83/1.15  Preprocessing        : 0.27
% 1.83/1.15  Parsing              : 0.16
% 1.83/1.15  CNF conversion       : 0.02
% 1.83/1.15  Main loop            : 0.13
% 1.83/1.15  Inferencing          : 0.06
% 1.83/1.15  Reduction            : 0.03
% 1.83/1.15  Demodulation         : 0.03
% 1.83/1.15  BG Simplification    : 0.01
% 1.83/1.15  Subsumption          : 0.01
% 1.83/1.15  Abstraction          : 0.01
% 1.83/1.15  MUC search           : 0.00
% 1.83/1.15  Cooper               : 0.00
% 1.83/1.15  Total                : 0.42
% 1.83/1.15  Index Insertion      : 0.00
% 1.83/1.15  Index Deletion       : 0.00
% 1.83/1.15  Index Matching       : 0.00
% 1.83/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
