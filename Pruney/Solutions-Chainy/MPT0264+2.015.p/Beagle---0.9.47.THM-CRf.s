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
% DateTime   : Thu Dec  3 09:52:22 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  76 expanded)
%              Number of equality atoms :   27 (  42 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_63,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_68,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_70,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_118,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_124,plain,(
    ! [B_44,A_43] : r2_hidden(B_44,k2_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_38])).

tff(c_72,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_168,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_180,plain,(
    k5_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_5')) = k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_168])).

tff(c_283,plain,(
    ! [A_74,C_75,B_76] :
      ( r2_hidden(A_74,C_75)
      | ~ r2_hidden(A_74,B_76)
      | r2_hidden(A_74,k5_xboole_0(B_76,C_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_407,plain,(
    ! [A_96] :
      ( r2_hidden(A_96,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_96,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(A_96,k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_283])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_425,plain,(
    ! [A_97] :
      ( ~ r2_hidden(A_97,'#skF_7')
      | r2_hidden(A_97,k1_tarski('#skF_5'))
      | ~ r2_hidden(A_97,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_407,c_6])).

tff(c_433,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_124,c_425])).

tff(c_439,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_433])).

tff(c_60,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    ! [A_22,B_23] : k1_enumset1(A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_338,plain,(
    ! [E_83,C_84,B_85,A_86] :
      ( E_83 = C_84
      | E_83 = B_85
      | E_83 = A_86
      | ~ r2_hidden(E_83,k1_enumset1(A_86,B_85,C_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_357,plain,(
    ! [E_87,B_88,A_89] :
      ( E_87 = B_88
      | E_87 = A_89
      | E_87 = A_89
      | ~ r2_hidden(E_87,k2_tarski(A_89,B_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_338])).

tff(c_366,plain,(
    ! [E_87,A_21] :
      ( E_87 = A_21
      | E_87 = A_21
      | E_87 = A_21
      | ~ r2_hidden(E_87,k1_tarski(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_357])).

tff(c_442,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_439,c_366])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_68,c_442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:13:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.44  
% 2.31/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.44  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.31/1.44  
% 2.31/1.44  %Foreground sorts:
% 2.31/1.44  
% 2.31/1.44  
% 2.31/1.44  %Background operators:
% 2.31/1.44  
% 2.31/1.44  
% 2.31/1.44  %Foreground operators:
% 2.31/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.31/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.31/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.31/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.31/1.44  
% 2.31/1.45  tff(f_78, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.31/1.45  tff(f_65, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.31/1.45  tff(f_61, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.31/1.45  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.31/1.45  tff(f_44, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.31/1.45  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.31/1.45  tff(f_63, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.31/1.45  tff(c_68, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.31/1.45  tff(c_70, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.31/1.45  tff(c_118, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.45  tff(c_38, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.31/1.45  tff(c_124, plain, (![B_44, A_43]: (r2_hidden(B_44, k2_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_38])).
% 2.31/1.45  tff(c_72, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.31/1.45  tff(c_168, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.31/1.45  tff(c_180, plain, (k5_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_5'))=k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_72, c_168])).
% 2.31/1.45  tff(c_283, plain, (![A_74, C_75, B_76]: (r2_hidden(A_74, C_75) | ~r2_hidden(A_74, B_76) | r2_hidden(A_74, k5_xboole_0(B_76, C_75)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.31/1.45  tff(c_407, plain, (![A_96]: (r2_hidden(A_96, k1_tarski('#skF_5')) | ~r2_hidden(A_96, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(A_96, k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_180, c_283])).
% 2.31/1.45  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.45  tff(c_425, plain, (![A_97]: (~r2_hidden(A_97, '#skF_7') | r2_hidden(A_97, k1_tarski('#skF_5')) | ~r2_hidden(A_97, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_407, c_6])).
% 2.31/1.45  tff(c_433, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_124, c_425])).
% 2.31/1.45  tff(c_439, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_433])).
% 2.31/1.45  tff(c_60, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.31/1.45  tff(c_62, plain, (![A_22, B_23]: (k1_enumset1(A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.31/1.45  tff(c_338, plain, (![E_83, C_84, B_85, A_86]: (E_83=C_84 | E_83=B_85 | E_83=A_86 | ~r2_hidden(E_83, k1_enumset1(A_86, B_85, C_84)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.31/1.45  tff(c_357, plain, (![E_87, B_88, A_89]: (E_87=B_88 | E_87=A_89 | E_87=A_89 | ~r2_hidden(E_87, k2_tarski(A_89, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_338])).
% 2.31/1.45  tff(c_366, plain, (![E_87, A_21]: (E_87=A_21 | E_87=A_21 | E_87=A_21 | ~r2_hidden(E_87, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_357])).
% 2.31/1.45  tff(c_442, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_439, c_366])).
% 2.31/1.45  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_68, c_442])).
% 2.31/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.45  
% 2.31/1.45  Inference rules
% 2.31/1.45  ----------------------
% 2.31/1.45  #Ref     : 0
% 2.31/1.45  #Sup     : 90
% 2.31/1.45  #Fact    : 0
% 2.31/1.45  #Define  : 0
% 2.31/1.46  #Split   : 0
% 2.31/1.46  #Chain   : 0
% 2.31/1.46  #Close   : 0
% 2.31/1.46  
% 2.31/1.46  Ordering : KBO
% 2.31/1.46  
% 2.31/1.46  Simplification rules
% 2.31/1.46  ----------------------
% 2.31/1.46  #Subsume      : 4
% 2.31/1.46  #Demod        : 15
% 2.31/1.46  #Tautology    : 58
% 2.31/1.46  #SimpNegUnit  : 1
% 2.31/1.46  #BackRed      : 0
% 2.31/1.46  
% 2.31/1.46  #Partial instantiations: 0
% 2.31/1.46  #Strategies tried      : 1
% 2.31/1.46  
% 2.31/1.46  Timing (in seconds)
% 2.31/1.46  ----------------------
% 2.31/1.46  Preprocessing        : 0.38
% 2.31/1.46  Parsing              : 0.18
% 2.31/1.46  CNF conversion       : 0.03
% 2.31/1.46  Main loop            : 0.25
% 2.31/1.46  Inferencing          : 0.09
% 2.31/1.46  Reduction            : 0.09
% 2.31/1.46  Demodulation         : 0.07
% 2.31/1.46  BG Simplification    : 0.02
% 2.31/1.46  Subsumption          : 0.05
% 2.31/1.46  Abstraction          : 0.01
% 2.31/1.46  MUC search           : 0.00
% 2.31/1.46  Cooper               : 0.00
% 2.31/1.46  Total                : 0.66
% 2.31/1.46  Index Insertion      : 0.00
% 2.31/1.46  Index Deletion       : 0.00
% 2.31/1.46  Index Matching       : 0.00
% 2.31/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
