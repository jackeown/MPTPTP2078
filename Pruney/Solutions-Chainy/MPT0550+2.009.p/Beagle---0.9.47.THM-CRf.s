%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:53 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   39 (  53 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  76 expanded)
%              Number of equality atoms :   15 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_105,plain,(
    ! [B_31,A_32] :
      ( r1_xboole_0(k1_relat_1(B_31),A_32)
      | k9_relat_1(B_31,A_32) != k1_xboole_0
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_61,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_65,plain,(
    k3_xboole_0('#skF_3',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_61])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_xboole_0(A_19,B_20)
      | ~ r2_hidden(C_21,k3_xboole_0(A_19,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_xboole_0(A_24,B_25)
      | ~ r2_hidden(C_26,k3_xboole_0(B_25,A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_70])).

tff(c_90,plain,(
    ! [C_26] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_26,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_87])).

tff(c_102,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_114,plain,
    ( k9_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_102])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_114])).

tff(c_126,plain,(
    ! [C_33] : ~ r2_hidden(C_33,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_130,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_126])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.43  
% 1.86/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.86/1.43  
% 1.86/1.43  %Foreground sorts:
% 1.86/1.43  
% 1.86/1.43  
% 1.86/1.43  %Background operators:
% 1.86/1.43  
% 1.86/1.43  
% 1.86/1.43  %Foreground operators:
% 1.86/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.86/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.86/1.43  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.43  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.86/1.43  
% 1.99/1.44  tff(f_70, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 1.99/1.44  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.99/1.44  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.99/1.44  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.99/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.99/1.44  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.99/1.44  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.99/1.44  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.44  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.99/1.44  tff(c_16, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.99/1.44  tff(c_105, plain, (![B_31, A_32]: (r1_xboole_0(k1_relat_1(B_31), A_32) | k9_relat_1(B_31, A_32)!=k1_xboole_0 | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.44  tff(c_18, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.99/1.44  tff(c_61, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.44  tff(c_65, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_18, c_61])).
% 1.99/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.44  tff(c_70, plain, (![A_19, B_20, C_21]: (~r1_xboole_0(A_19, B_20) | ~r2_hidden(C_21, k3_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.44  tff(c_87, plain, (![A_24, B_25, C_26]: (~r1_xboole_0(A_24, B_25) | ~r2_hidden(C_26, k3_xboole_0(B_25, A_24)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_70])).
% 1.99/1.44  tff(c_90, plain, (![C_26]: (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | ~r2_hidden(C_26, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_65, c_87])).
% 1.99/1.44  tff(c_102, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_90])).
% 1.99/1.44  tff(c_114, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_105, c_102])).
% 1.99/1.44  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_114])).
% 1.99/1.44  tff(c_126, plain, (![C_33]: (~r2_hidden(C_33, '#skF_3'))), inference(splitRight, [status(thm)], [c_90])).
% 1.99/1.44  tff(c_130, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_126])).
% 1.99/1.44  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_130])).
% 1.99/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.44  
% 1.99/1.44  Inference rules
% 1.99/1.44  ----------------------
% 1.99/1.44  #Ref     : 0
% 1.99/1.44  #Sup     : 26
% 1.99/1.44  #Fact    : 0
% 1.99/1.44  #Define  : 0
% 1.99/1.44  #Split   : 2
% 1.99/1.44  #Chain   : 0
% 1.99/1.44  #Close   : 0
% 1.99/1.44  
% 1.99/1.44  Ordering : KBO
% 1.99/1.44  
% 1.99/1.44  Simplification rules
% 1.99/1.44  ----------------------
% 1.99/1.44  #Subsume      : 3
% 1.99/1.44  #Demod        : 2
% 1.99/1.44  #Tautology    : 13
% 1.99/1.44  #SimpNegUnit  : 1
% 1.99/1.44  #BackRed      : 0
% 1.99/1.44  
% 1.99/1.44  #Partial instantiations: 0
% 1.99/1.44  #Strategies tried      : 1
% 1.99/1.44  
% 1.99/1.44  Timing (in seconds)
% 1.99/1.44  ----------------------
% 1.99/1.44  Preprocessing        : 0.46
% 1.99/1.44  Parsing              : 0.31
% 1.99/1.44  CNF conversion       : 0.02
% 1.99/1.44  Main loop            : 0.12
% 1.99/1.44  Inferencing          : 0.05
% 1.99/1.44  Reduction            : 0.03
% 1.99/1.44  Demodulation         : 0.03
% 1.99/1.44  BG Simplification    : 0.01
% 1.99/1.44  Subsumption          : 0.02
% 1.99/1.44  Abstraction          : 0.01
% 1.99/1.44  MUC search           : 0.00
% 1.99/1.45  Cooper               : 0.00
% 1.99/1.45  Total                : 0.61
% 1.99/1.45  Index Insertion      : 0.00
% 1.99/1.45  Index Deletion       : 0.00
% 1.99/1.45  Index Matching       : 0.00
% 1.99/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
