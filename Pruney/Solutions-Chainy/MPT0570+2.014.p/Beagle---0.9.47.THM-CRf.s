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
% DateTime   : Thu Dec  3 10:01:43 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  87 expanded)
%              Number of equality atoms :   16 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_338,plain,(
    ! [B_53,A_54] :
      ( r1_xboole_0(k2_relat_1(B_53),A_54)
      | k10_relat_1(B_53,A_54) != k1_xboole_0
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_74,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_78,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_74])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [A_25,B_26,C_27] :
      ( ~ r1_xboole_0(A_25,B_26)
      | ~ r2_hidden(C_27,k3_xboole_0(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    ! [B_30,A_31,C_32] :
      ( ~ r1_xboole_0(B_30,A_31)
      | ~ r2_hidden(C_32,k3_xboole_0(A_31,B_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_117,plain,(
    ! [C_32] :
      ( ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_32,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_106])).

tff(c_162,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_349,plain,
    ( k10_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_338,c_162])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_349])).

tff(c_365,plain,(
    ! [C_55] : ~ r2_hidden(C_55,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_376,plain,(
    ! [A_56] : r1_xboole_0(A_56,'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_365])).

tff(c_18,plain,(
    ! [A_15] :
      ( ~ r1_xboole_0(A_15,A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_382,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_376,c_18])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.06/1.23  
% 2.06/1.23  %Foreground sorts:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Background operators:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Foreground operators:
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.06/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.23  
% 2.12/1.24  tff(f_92, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.12/1.24  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.12/1.24  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.12/1.24  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.12/1.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.12/1.24  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.12/1.24  tff(f_75, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.12/1.24  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.12/1.24  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.12/1.24  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.12/1.24  tff(c_24, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.12/1.24  tff(c_338, plain, (![B_53, A_54]: (r1_xboole_0(k2_relat_1(B_53), A_54) | k10_relat_1(B_53, A_54)!=k1_xboole_0 | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.12/1.24  tff(c_26, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.12/1.24  tff(c_74, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.12/1.24  tff(c_78, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_26, c_74])).
% 2.12/1.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.24  tff(c_84, plain, (![A_25, B_26, C_27]: (~r1_xboole_0(A_25, B_26) | ~r2_hidden(C_27, k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.12/1.24  tff(c_106, plain, (![B_30, A_31, C_32]: (~r1_xboole_0(B_30, A_31) | ~r2_hidden(C_32, k3_xboole_0(A_31, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 2.12/1.24  tff(c_117, plain, (![C_32]: (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3') | ~r2_hidden(C_32, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_106])).
% 2.12/1.24  tff(c_162, plain, (~r1_xboole_0(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_117])).
% 2.12/1.24  tff(c_349, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_338, c_162])).
% 2.12/1.24  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_349])).
% 2.12/1.24  tff(c_365, plain, (![C_55]: (~r2_hidden(C_55, '#skF_3'))), inference(splitRight, [status(thm)], [c_117])).
% 2.12/1.24  tff(c_376, plain, (![A_56]: (r1_xboole_0(A_56, '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_365])).
% 2.12/1.24  tff(c_18, plain, (![A_15]: (~r1_xboole_0(A_15, A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.12/1.24  tff(c_382, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_376, c_18])).
% 2.12/1.24  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_382])).
% 2.12/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.24  
% 2.12/1.24  Inference rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Ref     : 0
% 2.12/1.24  #Sup     : 83
% 2.12/1.24  #Fact    : 0
% 2.12/1.24  #Define  : 0
% 2.12/1.24  #Split   : 2
% 2.12/1.24  #Chain   : 0
% 2.12/1.24  #Close   : 0
% 2.12/1.24  
% 2.12/1.24  Ordering : KBO
% 2.12/1.24  
% 2.12/1.24  Simplification rules
% 2.12/1.24  ----------------------
% 2.12/1.24  #Subsume      : 11
% 2.12/1.24  #Demod        : 23
% 2.12/1.24  #Tautology    : 40
% 2.12/1.24  #SimpNegUnit  : 4
% 2.12/1.24  #BackRed      : 0
% 2.12/1.24  
% 2.12/1.24  #Partial instantiations: 0
% 2.12/1.24  #Strategies tried      : 1
% 2.12/1.24  
% 2.12/1.24  Timing (in seconds)
% 2.12/1.24  ----------------------
% 2.12/1.24  Preprocessing        : 0.27
% 2.12/1.24  Parsing              : 0.14
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.19
% 2.12/1.24  Inferencing          : 0.07
% 2.12/1.24  Reduction            : 0.06
% 2.12/1.24  Demodulation         : 0.05
% 2.12/1.24  BG Simplification    : 0.02
% 2.12/1.24  Subsumption          : 0.03
% 2.12/1.24  Abstraction          : 0.01
% 2.12/1.25  MUC search           : 0.00
% 2.12/1.25  Cooper               : 0.00
% 2.12/1.25  Total                : 0.49
% 2.12/1.25  Index Insertion      : 0.00
% 2.12/1.25  Index Deletion       : 0.00
% 2.12/1.25  Index Matching       : 0.00
% 2.12/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
