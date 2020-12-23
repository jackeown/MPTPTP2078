%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:46 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  89 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_56,plain,(
    ! [B_27,A_28] :
      ( r1_xboole_0(k2_relat_1(B_27),A_28)
      | k10_relat_1(B_27,A_28) != k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(k2_relat_1(B_27),A_28) = k1_xboole_0
      | k10_relat_1(B_27,A_28) != k1_xboole_0
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,B_23)
      | ~ r2_hidden(C_24,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_68,plain,(
    ! [C_29,B_30,A_31] :
      ( ~ r2_hidden(C_29,B_30)
      | ~ r2_hidden(C_29,A_31)
      | k3_xboole_0(A_31,B_30) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_46])).

tff(c_89,plain,(
    ! [A_36,B_37,A_38] :
      ( ~ r2_hidden('#skF_1'(A_36,B_37),A_38)
      | k3_xboole_0(A_38,A_36) != k1_xboole_0
      | r1_xboole_0(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_10,c_68])).

tff(c_98,plain,(
    ! [B_39,A_40] :
      ( k3_xboole_0(B_39,A_40) != k1_xboole_0
      | r1_xboole_0(A_40,B_39) ) ),
    inference(resolution,[status(thm)],[c_8,c_89])).

tff(c_116,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = k1_xboole_0
      | k3_xboole_0(B_44,A_43) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_141,plain,(
    ! [A_52,B_53] :
      ( k3_xboole_0(A_52,k2_relat_1(B_53)) = k1_xboole_0
      | k10_relat_1(B_53,A_52) != k1_xboole_0
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_116])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_35,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_39,plain,(
    k3_xboole_0('#skF_2',k2_relat_1('#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_163,plain,
    ( k1_xboole_0 = '#skF_2'
    | k10_relat_1('#skF_3','#skF_2') != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_39])).

tff(c_181,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_163])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:27:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.25  
% 1.99/1.25  %Foreground sorts:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Background operators:
% 1.99/1.25  
% 1.99/1.25  
% 1.99/1.25  %Foreground operators:
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.99/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.25  
% 1.99/1.26  tff(f_68, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 1.99/1.26  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.99/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.99/1.26  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.99/1.26  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.99/1.26  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.26  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.26  tff(c_18, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.26  tff(c_56, plain, (![B_27, A_28]: (r1_xboole_0(k2_relat_1(B_27), A_28) | k10_relat_1(B_27, A_28)!=k1_xboole_0 | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.26  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.26  tff(c_67, plain, (![B_27, A_28]: (k3_xboole_0(k2_relat_1(B_27), A_28)=k1_xboole_0 | k10_relat_1(B_27, A_28)!=k1_xboole_0 | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_56, c_2])).
% 1.99/1.26  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.26  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.26  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.26  tff(c_46, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, B_23) | ~r2_hidden(C_24, A_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.26  tff(c_68, plain, (![C_29, B_30, A_31]: (~r2_hidden(C_29, B_30) | ~r2_hidden(C_29, A_31) | k3_xboole_0(A_31, B_30)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_46])).
% 1.99/1.26  tff(c_89, plain, (![A_36, B_37, A_38]: (~r2_hidden('#skF_1'(A_36, B_37), A_38) | k3_xboole_0(A_38, A_36)!=k1_xboole_0 | r1_xboole_0(A_36, B_37))), inference(resolution, [status(thm)], [c_10, c_68])).
% 1.99/1.26  tff(c_98, plain, (![B_39, A_40]: (k3_xboole_0(B_39, A_40)!=k1_xboole_0 | r1_xboole_0(A_40, B_39))), inference(resolution, [status(thm)], [c_8, c_89])).
% 1.99/1.26  tff(c_116, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=k1_xboole_0 | k3_xboole_0(B_44, A_43)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_98, c_2])).
% 1.99/1.26  tff(c_141, plain, (![A_52, B_53]: (k3_xboole_0(A_52, k2_relat_1(B_53))=k1_xboole_0 | k10_relat_1(B_53, A_52)!=k1_xboole_0 | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_67, c_116])).
% 1.99/1.26  tff(c_20, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.99/1.26  tff(c_35, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.26  tff(c_39, plain, (k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_20, c_35])).
% 1.99/1.26  tff(c_163, plain, (k1_xboole_0='#skF_2' | k10_relat_1('#skF_3', '#skF_2')!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_39])).
% 1.99/1.26  tff(c_181, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_163])).
% 1.99/1.26  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_181])).
% 1.99/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.26  
% 1.99/1.26  Inference rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Ref     : 0
% 1.99/1.26  #Sup     : 38
% 1.99/1.26  #Fact    : 0
% 1.99/1.26  #Define  : 0
% 1.99/1.26  #Split   : 0
% 1.99/1.26  #Chain   : 0
% 1.99/1.26  #Close   : 0
% 1.99/1.26  
% 1.99/1.26  Ordering : KBO
% 1.99/1.26  
% 1.99/1.26  Simplification rules
% 1.99/1.26  ----------------------
% 1.99/1.26  #Subsume      : 4
% 1.99/1.26  #Demod        : 4
% 1.99/1.26  #Tautology    : 12
% 1.99/1.26  #SimpNegUnit  : 1
% 1.99/1.26  #BackRed      : 0
% 1.99/1.26  
% 1.99/1.26  #Partial instantiations: 0
% 1.99/1.26  #Strategies tried      : 1
% 1.99/1.27  
% 1.99/1.27  Timing (in seconds)
% 1.99/1.27  ----------------------
% 1.99/1.27  Preprocessing        : 0.29
% 1.99/1.27  Parsing              : 0.16
% 1.99/1.27  CNF conversion       : 0.02
% 1.99/1.27  Main loop            : 0.16
% 1.99/1.27  Inferencing          : 0.07
% 1.99/1.27  Reduction            : 0.04
% 1.99/1.27  Demodulation         : 0.03
% 1.99/1.27  BG Simplification    : 0.01
% 1.99/1.27  Subsumption          : 0.03
% 1.99/1.27  Abstraction          : 0.01
% 1.99/1.27  MUC search           : 0.00
% 1.99/1.27  Cooper               : 0.00
% 1.99/1.27  Total                : 0.47
% 1.99/1.27  Index Insertion      : 0.00
% 1.99/1.27  Index Deletion       : 0.00
% 1.99/1.27  Index Matching       : 0.00
% 1.99/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
