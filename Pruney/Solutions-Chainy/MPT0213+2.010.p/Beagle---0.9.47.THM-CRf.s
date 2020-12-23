%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:28 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   40 (  77 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   44 ( 137 expanded)
%              Number of equality atoms :   14 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_44,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),A_12)
      | r2_hidden('#skF_5'(A_12,B_13),B_13)
      | k3_tarski(A_12) = B_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_12,C_27] :
      ( r2_hidden('#skF_6'(A_12,k3_tarski(A_12),C_27),A_12)
      | ~ r2_hidden(C_27,k3_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_200,plain,(
    ! [A_54,C_55] :
      ( r2_hidden('#skF_6'(A_54,k3_tarski(A_54),C_55),A_54)
      | ~ r2_hidden(C_55,k3_tarski(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    ! [D_42,B_43,A_44] :
      ( ~ r2_hidden(D_42,B_43)
      | ~ r2_hidden(D_42,k4_xboole_0(A_44,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_105,plain,(
    ! [D_42,A_9] :
      ( ~ r2_hidden(D_42,A_9)
      | ~ r2_hidden(D_42,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_99])).

tff(c_320,plain,(
    ! [A_68,C_69] :
      ( ~ r2_hidden('#skF_6'(A_68,k3_tarski(A_68),C_69),k1_xboole_0)
      | ~ r2_hidden(C_69,k3_tarski(A_68)) ) ),
    inference(resolution,[status(thm)],[c_200,c_105])).

tff(c_326,plain,(
    ! [C_70] : ~ r2_hidden(C_70,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_28,c_320])).

tff(c_433,plain,(
    ! [B_78] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),B_78),B_78)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_78 ) ),
    inference(resolution,[status(thm)],[c_40,c_326])).

tff(c_325,plain,(
    ! [C_27] : ~ r2_hidden(C_27,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_28,c_320])).

tff(c_483,plain,(
    k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_433,c_325])).

tff(c_339,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),B_13),B_13)
      | k3_tarski(k3_tarski(k1_xboole_0)) = B_13 ) ),
    inference(resolution,[status(thm)],[c_40,c_326])).

tff(c_524,plain,(
    ! [B_81] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),B_81),B_81)
      | k3_tarski(k1_xboole_0) = B_81 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_339])).

tff(c_20,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [D_37,A_38,B_39] :
      ( r2_hidden(D_37,A_38)
      | ~ r2_hidden(D_37,k4_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_94,plain,(
    ! [D_37,A_7] :
      ( r2_hidden(D_37,A_7)
      | ~ r2_hidden(D_37,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_91])).

tff(c_543,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),k1_xboole_0),A_7)
      | k3_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_524,c_94])).

tff(c_558,plain,(
    ! [A_82] : r2_hidden('#skF_5'(k3_tarski(k1_xboole_0),k1_xboole_0),A_82) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_543])).

tff(c_582,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_558,c_325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:13:46 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_6 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 2.16/1.28  
% 2.16/1.28  %Foreground sorts:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Background operators:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Foreground operators:
% 2.16/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.28  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.16/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.16/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.16/1.28  
% 2.16/1.29  tff(f_53, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.16/1.29  tff(f_51, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 2.16/1.29  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.16/1.29  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.16/1.29  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.16/1.29  tff(c_44, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.29  tff(c_40, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), A_12) | r2_hidden('#skF_5'(A_12, B_13), B_13) | k3_tarski(A_12)=B_13)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.29  tff(c_28, plain, (![A_12, C_27]: (r2_hidden('#skF_6'(A_12, k3_tarski(A_12), C_27), A_12) | ~r2_hidden(C_27, k3_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.29  tff(c_200, plain, (![A_54, C_55]: (r2_hidden('#skF_6'(A_54, k3_tarski(A_54), C_55), A_54) | ~r2_hidden(C_55, k3_tarski(A_54)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.29  tff(c_22, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.16/1.29  tff(c_99, plain, (![D_42, B_43, A_44]: (~r2_hidden(D_42, B_43) | ~r2_hidden(D_42, k4_xboole_0(A_44, B_43)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.29  tff(c_105, plain, (![D_42, A_9]: (~r2_hidden(D_42, A_9) | ~r2_hidden(D_42, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_99])).
% 2.16/1.29  tff(c_320, plain, (![A_68, C_69]: (~r2_hidden('#skF_6'(A_68, k3_tarski(A_68), C_69), k1_xboole_0) | ~r2_hidden(C_69, k3_tarski(A_68)))), inference(resolution, [status(thm)], [c_200, c_105])).
% 2.16/1.29  tff(c_326, plain, (![C_70]: (~r2_hidden(C_70, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_28, c_320])).
% 2.16/1.29  tff(c_433, plain, (![B_78]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), B_78), B_78) | k3_tarski(k3_tarski(k1_xboole_0))=B_78)), inference(resolution, [status(thm)], [c_40, c_326])).
% 2.16/1.29  tff(c_325, plain, (![C_27]: (~r2_hidden(C_27, k3_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_28, c_320])).
% 2.16/1.29  tff(c_483, plain, (k3_tarski(k3_tarski(k1_xboole_0))=k3_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_433, c_325])).
% 2.16/1.29  tff(c_339, plain, (![B_13]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), B_13), B_13) | k3_tarski(k3_tarski(k1_xboole_0))=B_13)), inference(resolution, [status(thm)], [c_40, c_326])).
% 2.16/1.29  tff(c_524, plain, (![B_81]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), B_81), B_81) | k3_tarski(k1_xboole_0)=B_81)), inference(demodulation, [status(thm), theory('equality')], [c_483, c_339])).
% 2.16/1.29  tff(c_20, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.29  tff(c_91, plain, (![D_37, A_38, B_39]: (r2_hidden(D_37, A_38) | ~r2_hidden(D_37, k4_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.29  tff(c_94, plain, (![D_37, A_7]: (r2_hidden(D_37, A_7) | ~r2_hidden(D_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_91])).
% 2.16/1.29  tff(c_543, plain, (![A_7]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), k1_xboole_0), A_7) | k3_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_524, c_94])).
% 2.16/1.29  tff(c_558, plain, (![A_82]: (r2_hidden('#skF_5'(k3_tarski(k1_xboole_0), k1_xboole_0), A_82))), inference(negUnitSimplification, [status(thm)], [c_44, c_543])).
% 2.16/1.29  tff(c_582, plain, $false, inference(resolution, [status(thm)], [c_558, c_325])).
% 2.16/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  Inference rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Ref     : 0
% 2.16/1.29  #Sup     : 125
% 2.16/1.29  #Fact    : 0
% 2.16/1.29  #Define  : 0
% 2.16/1.29  #Split   : 0
% 2.16/1.29  #Chain   : 0
% 2.16/1.29  #Close   : 0
% 2.16/1.29  
% 2.16/1.29  Ordering : KBO
% 2.16/1.29  
% 2.16/1.29  Simplification rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Subsume      : 17
% 2.16/1.29  #Demod        : 47
% 2.16/1.29  #Tautology    : 32
% 2.16/1.29  #SimpNegUnit  : 2
% 2.16/1.29  #BackRed      : 6
% 2.16/1.29  
% 2.16/1.29  #Partial instantiations: 0
% 2.16/1.29  #Strategies tried      : 1
% 2.16/1.29  
% 2.16/1.29  Timing (in seconds)
% 2.16/1.29  ----------------------
% 2.16/1.29  Preprocessing        : 0.28
% 2.16/1.29  Parsing              : 0.15
% 2.16/1.29  CNF conversion       : 0.02
% 2.16/1.29  Main loop            : 0.27
% 2.16/1.29  Inferencing          : 0.10
% 2.16/1.29  Reduction            : 0.08
% 2.16/1.29  Demodulation         : 0.06
% 2.16/1.29  BG Simplification    : 0.02
% 2.16/1.29  Subsumption          : 0.05
% 2.16/1.29  Abstraction          : 0.02
% 2.16/1.29  MUC search           : 0.00
% 2.16/1.29  Cooper               : 0.00
% 2.16/1.29  Total                : 0.58
% 2.16/1.29  Index Insertion      : 0.00
% 2.16/1.29  Index Deletion       : 0.00
% 2.16/1.29  Index Matching       : 0.00
% 2.16/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
