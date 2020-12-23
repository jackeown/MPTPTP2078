%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:54 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   41 (  43 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).

tff(c_20,plain,(
    ! [D_18,B_14] : r2_hidden(D_18,k2_tarski(D_18,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    ! [B_45,A_46] :
      ( ~ r2_hidden(B_45,A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [D_18,B_14] : ~ v1_xboole_0(k2_tarski(D_18,B_14)) ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_47,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_80,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_46])).

tff(c_85,plain,(
    ! [A_52,B_53] :
      ( ~ v1_xboole_0(k2_xboole_0(A_52,B_53))
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0(k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_85])).

tff(c_90,plain,(
    v1_xboole_0(k2_tarski('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.15  
% 1.73/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.15  %$ r2_hidden > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.73/1.15  
% 1.73/1.15  %Foreground sorts:
% 1.73/1.15  
% 1.73/1.15  
% 1.73/1.15  %Background operators:
% 1.73/1.15  
% 1.73/1.15  
% 1.73/1.15  %Foreground operators:
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.73/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.73/1.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.73/1.15  tff('#skF_7', type, '#skF_7': $i).
% 1.73/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.73/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.73/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.73/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.73/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.73/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.73/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.73/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.73/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.15  
% 1.73/1.16  tff(f_56, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.73/1.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.73/1.16  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.73/1.16  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.73/1.16  tff(f_72, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.73/1.16  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_xboole_0)).
% 1.73/1.16  tff(c_20, plain, (![D_18, B_14]: (r2_hidden(D_18, k2_tarski(D_18, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.73/1.16  tff(c_64, plain, (![B_45, A_46]: (~r2_hidden(B_45, A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.16  tff(c_68, plain, (![D_18, B_14]: (~v1_xboole_0(k2_tarski(D_18, B_14)))), inference(resolution, [status(thm)], [c_20, c_64])).
% 1.73/1.16  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.73/1.16  tff(c_47, plain, (![A_41]: (k1_xboole_0=A_41 | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.16  tff(c_51, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_47])).
% 1.73/1.16  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.73/1.16  tff(c_80, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_46])).
% 1.73/1.16  tff(c_85, plain, (![A_52, B_53]: (~v1_xboole_0(k2_xboole_0(A_52, B_53)) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.73/1.16  tff(c_88, plain, (~v1_xboole_0('#skF_2') | v1_xboole_0(k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_85])).
% 1.73/1.16  tff(c_90, plain, (v1_xboole_0(k2_tarski('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_88])).
% 1.73/1.16  tff(c_92, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_90])).
% 1.73/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  Inference rules
% 1.73/1.16  ----------------------
% 1.73/1.16  #Ref     : 0
% 1.73/1.16  #Sup     : 10
% 1.73/1.16  #Fact    : 0
% 1.73/1.16  #Define  : 0
% 1.73/1.16  #Split   : 0
% 1.73/1.16  #Chain   : 0
% 1.73/1.16  #Close   : 0
% 1.73/1.16  
% 1.73/1.16  Ordering : KBO
% 1.73/1.16  
% 1.73/1.16  Simplification rules
% 1.73/1.16  ----------------------
% 1.73/1.16  #Subsume      : 1
% 1.73/1.16  #Demod        : 3
% 1.73/1.16  #Tautology    : 6
% 1.73/1.16  #SimpNegUnit  : 1
% 1.73/1.16  #BackRed      : 1
% 1.73/1.16  
% 1.73/1.16  #Partial instantiations: 0
% 1.73/1.16  #Strategies tried      : 1
% 1.73/1.16  
% 1.73/1.16  Timing (in seconds)
% 1.73/1.16  ----------------------
% 1.73/1.16  Preprocessing        : 0.31
% 1.73/1.16  Parsing              : 0.16
% 1.73/1.16  CNF conversion       : 0.02
% 1.73/1.16  Main loop            : 0.10
% 1.73/1.16  Inferencing          : 0.03
% 1.73/1.16  Reduction            : 0.04
% 1.73/1.16  Demodulation         : 0.03
% 1.73/1.16  BG Simplification    : 0.01
% 1.73/1.16  Subsumption          : 0.02
% 1.73/1.16  Abstraction          : 0.01
% 1.73/1.16  MUC search           : 0.00
% 1.73/1.16  Cooper               : 0.00
% 1.73/1.16  Total                : 0.43
% 1.73/1.16  Index Insertion      : 0.00
% 1.73/1.16  Index Deletion       : 0.00
% 1.73/1.16  Index Matching       : 0.00
% 1.73/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
