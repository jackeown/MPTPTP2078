%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:28 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   29 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  63 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_57,plain,(
    ! [A_47,B_48,C_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | ~ r2_hidden(C_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_68,plain,(
    ! [A_11,C_49] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_49,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_57])).

tff(c_72,plain,(
    ! [C_49] : ~ r2_hidden(C_49,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_68])).

tff(c_22,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_3'(A_14),A_14)
      | v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_73,plain,(
    ! [C_50] : ~ r2_hidden(C_50,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_68])).

tff(c_83,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_433,plain,(
    ! [A_94,B_95,C_96] :
      ( r2_hidden('#skF_6'(A_94,B_95,C_96),k2_relat_1(C_96))
      | ~ r2_hidden(A_94,k10_relat_1(C_96,B_95))
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_438,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_6'(A_94,B_95,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_94,k10_relat_1(k1_xboole_0,B_95))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_433])).

tff(c_441,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_6'(A_94,B_95,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_94,k10_relat_1(k1_xboole_0,B_95)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_438])).

tff(c_443,plain,(
    ! [A_97,B_98] : ~ r2_hidden(A_97,k10_relat_1(k1_xboole_0,B_98)) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_441])).

tff(c_479,plain,(
    ! [B_100,B_101] : r1_tarski(k10_relat_1(k1_xboole_0,B_100),B_101) ),
    inference(resolution,[status(thm)],[c_6,c_443])).

tff(c_14,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_509,plain,(
    ! [B_100] : k10_relat_1(k1_xboole_0,B_100) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_479,c_14])).

tff(c_36,plain,(
    k10_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.39  
% 2.30/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.60/1.40  
% 2.60/1.40  %Foreground sorts:
% 2.60/1.40  
% 2.60/1.40  
% 2.60/1.40  %Background operators:
% 2.60/1.40  
% 2.60/1.40  
% 2.60/1.40  %Foreground operators:
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.40  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.60/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.60/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.60/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.60/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.60/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.40  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.60/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.60/1.40  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.60/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.60/1.40  
% 2.60/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.60/1.42  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.60/1.42  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.60/1.42  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.60/1.42  tff(f_64, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.60/1.42  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.60/1.42  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.60/1.42  tff(f_52, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.60/1.42  tff(f_81, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.60/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.42  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.60/1.42  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.60/1.42  tff(c_57, plain, (![A_47, B_48, C_49]: (~r1_xboole_0(A_47, B_48) | ~r2_hidden(C_49, k3_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.60/1.42  tff(c_68, plain, (![A_11, C_49]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_49, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_57])).
% 2.60/1.42  tff(c_72, plain, (![C_49]: (~r2_hidden(C_49, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_68])).
% 2.60/1.42  tff(c_22, plain, (![A_14]: (r2_hidden('#skF_3'(A_14), A_14) | v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.60/1.42  tff(c_73, plain, (![C_50]: (~r2_hidden(C_50, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_68])).
% 2.60/1.42  tff(c_83, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_73])).
% 2.60/1.42  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.60/1.42  tff(c_433, plain, (![A_94, B_95, C_96]: (r2_hidden('#skF_6'(A_94, B_95, C_96), k2_relat_1(C_96)) | ~r2_hidden(A_94, k10_relat_1(C_96, B_95)) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.60/1.42  tff(c_438, plain, (![A_94, B_95]: (r2_hidden('#skF_6'(A_94, B_95, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_94, k10_relat_1(k1_xboole_0, B_95)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_433])).
% 2.60/1.42  tff(c_441, plain, (![A_94, B_95]: (r2_hidden('#skF_6'(A_94, B_95, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_94, k10_relat_1(k1_xboole_0, B_95)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_438])).
% 2.60/1.42  tff(c_443, plain, (![A_97, B_98]: (~r2_hidden(A_97, k10_relat_1(k1_xboole_0, B_98)))), inference(negUnitSimplification, [status(thm)], [c_72, c_441])).
% 2.60/1.42  tff(c_479, plain, (![B_100, B_101]: (r1_tarski(k10_relat_1(k1_xboole_0, B_100), B_101))), inference(resolution, [status(thm)], [c_6, c_443])).
% 2.60/1.42  tff(c_14, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.60/1.42  tff(c_509, plain, (![B_100]: (k10_relat_1(k1_xboole_0, B_100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_479, c_14])).
% 2.60/1.42  tff(c_36, plain, (k10_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.60/1.42  tff(c_547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_509, c_36])).
% 2.60/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.42  
% 2.60/1.42  Inference rules
% 2.60/1.42  ----------------------
% 2.60/1.42  #Ref     : 0
% 2.60/1.42  #Sup     : 106
% 2.60/1.42  #Fact    : 0
% 2.60/1.42  #Define  : 0
% 2.60/1.42  #Split   : 0
% 2.60/1.42  #Chain   : 0
% 2.60/1.42  #Close   : 0
% 2.60/1.42  
% 2.60/1.42  Ordering : KBO
% 2.60/1.42  
% 2.60/1.42  Simplification rules
% 2.60/1.42  ----------------------
% 2.60/1.42  #Subsume      : 20
% 2.60/1.42  #Demod        : 47
% 2.60/1.42  #Tautology    : 48
% 2.60/1.42  #SimpNegUnit  : 2
% 2.60/1.42  #BackRed      : 4
% 2.60/1.42  
% 2.60/1.42  #Partial instantiations: 0
% 2.60/1.42  #Strategies tried      : 1
% 2.60/1.42  
% 2.60/1.42  Timing (in seconds)
% 2.60/1.42  ----------------------
% 2.60/1.43  Preprocessing        : 0.32
% 2.60/1.43  Parsing              : 0.17
% 2.60/1.43  CNF conversion       : 0.03
% 2.60/1.43  Main loop            : 0.27
% 2.60/1.43  Inferencing          : 0.12
% 2.60/1.43  Reduction            : 0.07
% 2.60/1.43  Demodulation         : 0.05
% 2.60/1.43  BG Simplification    : 0.02
% 2.60/1.43  Subsumption          : 0.05
% 2.60/1.43  Abstraction          : 0.01
% 2.60/1.43  MUC search           : 0.00
% 2.60/1.43  Cooper               : 0.00
% 2.60/1.43  Total                : 0.63
% 2.60/1.43  Index Insertion      : 0.00
% 2.60/1.43  Index Deletion       : 0.00
% 2.60/1.43  Index Matching       : 0.00
% 2.60/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
