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
% DateTime   : Thu Dec  3 09:58:50 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  78 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_246,plain,(
    ! [A_68,B_69] :
      ( r2_hidden(k4_tarski('#skF_5'(A_68,B_69),'#skF_6'(A_68,B_69)),A_68)
      | r1_tarski(A_68,B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ! [B_33,C_34] : ~ r2_hidden(k4_tarski(B_33,C_34),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_265,plain,(
    ! [B_69] :
      ( r1_tarski('#skF_7',B_69)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_246,c_36])).

tff(c_273,plain,(
    ! [B_69] : r1_tarski('#skF_7',B_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_265])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_71,plain,(
    ! [C_49,B_50,A_51] :
      ( r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_12,B_50] :
      ( r2_hidden('#skF_4'(A_12),B_50)
      | ~ r1_tarski(A_12,B_50)
      | k1_xboole_0 = A_12 ) ),
    inference(resolution,[status(thm)],[c_26,c_71])).

tff(c_60,plain,(
    ! [D_46,A_47,B_48] :
      ( r2_hidden(D_46,A_47)
      | ~ r2_hidden(D_46,k4_xboole_0(A_47,B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_70,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_47,B_48)),A_47)
      | k4_xboole_0(A_47,B_48) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_60])).

tff(c_49,plain,(
    ! [D_43,B_44,A_45] :
      ( ~ r2_hidden(D_43,B_44)
      | ~ r2_hidden(D_43,k4_xboole_0(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_106,plain,(
    ! [A_56,B_57] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_56,B_57)),B_57)
      | k4_xboole_0(A_56,B_57) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_117,plain,(
    ! [A_58] : k4_xboole_0(A_58,A_58) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_106])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_181,plain,(
    ! [D_64,A_65] :
      ( ~ r2_hidden(D_64,A_65)
      | ~ r2_hidden(D_64,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_10])).

tff(c_197,plain,(
    ! [A_66] :
      ( ~ r2_hidden('#skF_4'(A_66),k1_xboole_0)
      | k1_xboole_0 = A_66 ) ),
    inference(resolution,[status(thm)],[c_26,c_181])).

tff(c_275,plain,(
    ! [A_71] :
      ( ~ r1_tarski(A_71,k1_xboole_0)
      | k1_xboole_0 = A_71 ) ),
    inference(resolution,[status(thm)],[c_77,c_197])).

tff(c_279,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_273,c_275])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.21  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_3 > #skF_1 > #skF_5
% 1.91/1.21  
% 1.91/1.21  %Foreground sorts:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Background operators:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Foreground operators:
% 1.91/1.21  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.91/1.21  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.91/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.91/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.21  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.91/1.21  
% 1.91/1.22  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 1.91/1.22  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 1.91/1.22  tff(f_50, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.91/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.91/1.22  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.91/1.22  tff(c_34, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.91/1.22  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.91/1.22  tff(c_246, plain, (![A_68, B_69]: (r2_hidden(k4_tarski('#skF_5'(A_68, B_69), '#skF_6'(A_68, B_69)), A_68) | r1_tarski(A_68, B_69) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.22  tff(c_36, plain, (![B_33, C_34]: (~r2_hidden(k4_tarski(B_33, C_34), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.91/1.22  tff(c_265, plain, (![B_69]: (r1_tarski('#skF_7', B_69) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_246, c_36])).
% 1.91/1.22  tff(c_273, plain, (![B_69]: (r1_tarski('#skF_7', B_69))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_265])).
% 1.91/1.22  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.22  tff(c_71, plain, (![C_49, B_50, A_51]: (r2_hidden(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.22  tff(c_77, plain, (![A_12, B_50]: (r2_hidden('#skF_4'(A_12), B_50) | ~r1_tarski(A_12, B_50) | k1_xboole_0=A_12)), inference(resolution, [status(thm)], [c_26, c_71])).
% 1.91/1.22  tff(c_60, plain, (![D_46, A_47, B_48]: (r2_hidden(D_46, A_47) | ~r2_hidden(D_46, k4_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.91/1.22  tff(c_70, plain, (![A_47, B_48]: (r2_hidden('#skF_4'(k4_xboole_0(A_47, B_48)), A_47) | k4_xboole_0(A_47, B_48)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_60])).
% 1.91/1.22  tff(c_49, plain, (![D_43, B_44, A_45]: (~r2_hidden(D_43, B_44) | ~r2_hidden(D_43, k4_xboole_0(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.91/1.22  tff(c_106, plain, (![A_56, B_57]: (~r2_hidden('#skF_4'(k4_xboole_0(A_56, B_57)), B_57) | k4_xboole_0(A_56, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_49])).
% 1.91/1.22  tff(c_117, plain, (![A_58]: (k4_xboole_0(A_58, A_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_106])).
% 1.91/1.22  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.91/1.22  tff(c_181, plain, (![D_64, A_65]: (~r2_hidden(D_64, A_65) | ~r2_hidden(D_64, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_117, c_10])).
% 1.91/1.22  tff(c_197, plain, (![A_66]: (~r2_hidden('#skF_4'(A_66), k1_xboole_0) | k1_xboole_0=A_66)), inference(resolution, [status(thm)], [c_26, c_181])).
% 1.91/1.22  tff(c_275, plain, (![A_71]: (~r1_tarski(A_71, k1_xboole_0) | k1_xboole_0=A_71)), inference(resolution, [status(thm)], [c_77, c_197])).
% 1.91/1.22  tff(c_279, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_273, c_275])).
% 1.91/1.22  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_279])).
% 1.91/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  Inference rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Ref     : 0
% 1.91/1.22  #Sup     : 56
% 1.91/1.22  #Fact    : 0
% 1.91/1.22  #Define  : 0
% 1.91/1.22  #Split   : 0
% 1.91/1.22  #Chain   : 0
% 1.91/1.22  #Close   : 0
% 1.91/1.22  
% 1.91/1.22  Ordering : KBO
% 1.91/1.22  
% 1.91/1.22  Simplification rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Subsume      : 5
% 1.91/1.22  #Demod        : 5
% 1.91/1.22  #Tautology    : 15
% 1.91/1.22  #SimpNegUnit  : 1
% 1.91/1.22  #BackRed      : 0
% 1.91/1.22  
% 1.91/1.22  #Partial instantiations: 0
% 1.91/1.22  #Strategies tried      : 1
% 1.91/1.22  
% 1.91/1.22  Timing (in seconds)
% 1.91/1.22  ----------------------
% 1.91/1.22  Preprocessing        : 0.28
% 1.91/1.22  Parsing              : 0.14
% 1.91/1.22  CNF conversion       : 0.02
% 1.91/1.22  Main loop            : 0.18
% 1.91/1.22  Inferencing          : 0.07
% 1.91/1.22  Reduction            : 0.05
% 1.91/1.22  Demodulation         : 0.03
% 1.91/1.22  BG Simplification    : 0.02
% 1.91/1.22  Subsumption          : 0.04
% 1.91/1.22  Abstraction          : 0.01
% 1.91/1.22  MUC search           : 0.00
% 1.91/1.22  Cooper               : 0.00
% 1.91/1.22  Total                : 0.48
% 1.91/1.22  Index Insertion      : 0.00
% 1.91/1.22  Index Deletion       : 0.00
% 1.91/1.22  Index Matching       : 0.00
% 1.91/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
