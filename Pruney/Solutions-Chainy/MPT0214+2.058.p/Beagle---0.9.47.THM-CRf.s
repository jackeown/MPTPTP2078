%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:37 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   52 (  77 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   51 ( 101 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_40,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [C_17] : ~ v1_xboole_0(k1_tarski(C_17)) ),
    inference(resolution,[status(thm)],[c_16,c_56])).

tff(c_77,plain,(
    ! [A_41] :
      ( v1_xboole_0(A_41)
      | r2_hidden('#skF_1'(A_41),A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_81,plain,(
    ! [A_13] :
      ( '#skF_1'(k1_tarski(A_13)) = A_13
      | v1_xboole_0(k1_tarski(A_13)) ) ),
    inference(resolution,[status(thm)],[c_77,c_14])).

tff(c_87,plain,(
    ! [A_13] : '#skF_1'(k1_tarski(A_13)) = A_13 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_81])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    ! [A_51,C_52] :
      ( ~ r1_xboole_0(A_51,A_51)
      | ~ r2_hidden(C_52,A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_112])).

tff(c_135,plain,(
    ! [C_53] : ~ r2_hidden(C_53,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_130])).

tff(c_140,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_135])).

tff(c_42,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_141,plain,(
    ! [B_54,A_55] :
      ( k1_tarski(B_54) = A_55
      | k1_xboole_0 = A_55
      | ~ r1_tarski(A_55,k1_tarski(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_151,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_141])).

tff(c_167,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_181,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_60])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_181])).

tff(c_199,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_222,plain,(
    '#skF_1'(k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_87])).

tff(c_242,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_222])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:36:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  
% 1.86/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.86/1.22  
% 1.86/1.22  %Foreground sorts:
% 1.86/1.22  
% 1.86/1.22  
% 1.86/1.22  %Background operators:
% 1.86/1.22  
% 1.86/1.22  
% 1.86/1.22  %Foreground operators:
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.86/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.86/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.86/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.86/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.86/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.86/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.86/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.86/1.22  
% 1.86/1.23  tff(f_75, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.86/1.23  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.86/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.86/1.23  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.86/1.23  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.86/1.23  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.86/1.23  tff(f_70, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.86/1.23  tff(c_40, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.86/1.23  tff(c_16, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.23  tff(c_56, plain, (![B_35, A_36]: (~r2_hidden(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.23  tff(c_60, plain, (![C_17]: (~v1_xboole_0(k1_tarski(C_17)))), inference(resolution, [status(thm)], [c_16, c_56])).
% 1.86/1.23  tff(c_77, plain, (![A_41]: (v1_xboole_0(A_41) | r2_hidden('#skF_1'(A_41), A_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.23  tff(c_14, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.23  tff(c_81, plain, (![A_13]: ('#skF_1'(k1_tarski(A_13))=A_13 | v1_xboole_0(k1_tarski(A_13)))), inference(resolution, [status(thm)], [c_77, c_14])).
% 1.86/1.23  tff(c_87, plain, (![A_13]: ('#skF_1'(k1_tarski(A_13))=A_13)), inference(negUnitSimplification, [status(thm)], [c_60, c_81])).
% 1.86/1.23  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.23  tff(c_12, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.86/1.23  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.23  tff(c_112, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.86/1.23  tff(c_130, plain, (![A_51, C_52]: (~r1_xboole_0(A_51, A_51) | ~r2_hidden(C_52, A_51))), inference(superposition, [status(thm), theory('equality')], [c_6, c_112])).
% 1.86/1.23  tff(c_135, plain, (![C_53]: (~r2_hidden(C_53, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_130])).
% 1.86/1.23  tff(c_140, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_135])).
% 1.86/1.23  tff(c_42, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.86/1.23  tff(c_141, plain, (![B_54, A_55]: (k1_tarski(B_54)=A_55 | k1_xboole_0=A_55 | ~r1_tarski(A_55, k1_tarski(B_54)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.86/1.23  tff(c_151, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_141])).
% 1.86/1.23  tff(c_167, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_151])).
% 1.86/1.23  tff(c_181, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_167, c_60])).
% 1.86/1.23  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_181])).
% 1.86/1.23  tff(c_199, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_151])).
% 1.86/1.23  tff(c_222, plain, ('#skF_1'(k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_199, c_87])).
% 1.86/1.23  tff(c_242, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_222])).
% 1.86/1.23  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_242])).
% 1.86/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.23  
% 1.86/1.23  Inference rules
% 1.86/1.23  ----------------------
% 1.86/1.23  #Ref     : 0
% 1.86/1.23  #Sup     : 47
% 1.86/1.23  #Fact    : 0
% 1.86/1.23  #Define  : 0
% 1.86/1.23  #Split   : 1
% 1.86/1.23  #Chain   : 0
% 1.86/1.23  #Close   : 0
% 1.86/1.23  
% 1.86/1.23  Ordering : KBO
% 1.86/1.23  
% 1.86/1.23  Simplification rules
% 1.86/1.23  ----------------------
% 1.86/1.23  #Subsume      : 2
% 1.86/1.23  #Demod        : 11
% 1.86/1.23  #Tautology    : 21
% 1.86/1.23  #SimpNegUnit  : 3
% 1.86/1.23  #BackRed      : 3
% 1.86/1.23  
% 1.86/1.23  #Partial instantiations: 0
% 1.86/1.23  #Strategies tried      : 1
% 1.86/1.23  
% 1.86/1.23  Timing (in seconds)
% 1.86/1.23  ----------------------
% 2.05/1.23  Preprocessing        : 0.31
% 2.05/1.23  Parsing              : 0.16
% 2.05/1.23  CNF conversion       : 0.02
% 2.05/1.23  Main loop            : 0.14
% 2.05/1.23  Inferencing          : 0.05
% 2.05/1.23  Reduction            : 0.04
% 2.05/1.23  Demodulation         : 0.03
% 2.05/1.23  BG Simplification    : 0.01
% 2.05/1.23  Subsumption          : 0.02
% 2.05/1.23  Abstraction          : 0.01
% 2.05/1.23  MUC search           : 0.00
% 2.05/1.23  Cooper               : 0.00
% 2.05/1.23  Total                : 0.48
% 2.05/1.23  Index Insertion      : 0.00
% 2.05/1.23  Index Deletion       : 0.00
% 2.05/1.23  Index Matching       : 0.00
% 2.05/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
