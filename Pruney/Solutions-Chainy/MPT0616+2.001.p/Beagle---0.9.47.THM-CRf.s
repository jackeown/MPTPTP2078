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
% DateTime   : Thu Dec  3 10:02:50 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   45 (  72 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   60 ( 155 expanded)
%              Number of equality atoms :   12 (  34 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> ( r2_hidden(A,k1_relat_1(C))
            & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_36,plain,
    ( r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7')
    | r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,
    ( r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7')
    | k1_funct_1('#skF_7','#skF_5') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,(
    k1_funct_1('#skF_7','#skF_5') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_26,plain,
    ( k1_funct_1('#skF_7','#skF_5') != '#skF_6'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_37,c_26])).

tff(c_24,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    ! [B_34,A_35] :
      ( r2_hidden(k4_tarski(B_34,k1_funct_1(A_35,B_34)),A_35)
      | ~ r2_hidden(B_34,k1_relat_1(A_35))
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,
    ( r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_58])).

tff(c_67,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_42,c_64])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_67])).

tff(c_71,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_70,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_72,plain,(
    ! [C_36,A_37,D_38] :
      ( r2_hidden(C_36,k1_relat_1(A_37))
      | ~ r2_hidden(k4_tarski(C_36,D_38),A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_70,c_72])).

tff(c_79,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_75])).

tff(c_81,plain,(
    k1_funct_1('#skF_7','#skF_5') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_80,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_82,plain,(
    ! [C_39,A_40,D_41] :
      ( r2_hidden(C_39,k1_relat_1(A_40))
      | ~ r2_hidden(k4_tarski(C_39,D_41),A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_80,c_82])).

tff(c_133,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_funct_1(A_56,B_57) = C_58
      | ~ r2_hidden(k4_tarski(B_57,C_58),A_56)
      | ~ r2_hidden(B_57,k1_relat_1(A_56))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_150,plain,
    ( k1_funct_1('#skF_7','#skF_5') = '#skF_6'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_133])).

tff(c_158,plain,(
    k1_funct_1('#skF_7','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_86,c_150])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.22  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 1.81/1.22  
% 1.81/1.22  %Foreground sorts:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Background operators:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Foreground operators:
% 1.81/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.81/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.81/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.81/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.81/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.81/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.81/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.22  
% 1.81/1.23  tff(f_62, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 1.81/1.23  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 1.81/1.23  tff(f_33, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.81/1.23  tff(c_36, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), '#skF_7') | r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.81/1.23  tff(c_42, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_36])).
% 1.81/1.23  tff(c_32, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), '#skF_7') | k1_funct_1('#skF_7', '#skF_5')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.81/1.23  tff(c_37, plain, (k1_funct_1('#skF_7', '#skF_5')='#skF_6'), inference(splitLeft, [status(thm)], [c_32])).
% 1.81/1.23  tff(c_26, plain, (k1_funct_1('#skF_7', '#skF_5')!='#skF_6' | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~r2_hidden(k4_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.81/1.23  tff(c_52, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_37, c_26])).
% 1.81/1.23  tff(c_24, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.81/1.23  tff(c_22, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.81/1.23  tff(c_58, plain, (![B_34, A_35]: (r2_hidden(k4_tarski(B_34, k1_funct_1(A_35, B_34)), A_35) | ~r2_hidden(B_34, k1_relat_1(A_35)) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.81/1.23  tff(c_64, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), '#skF_7') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_37, c_58])).
% 1.81/1.23  tff(c_67, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_42, c_64])).
% 1.81/1.23  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_67])).
% 1.81/1.23  tff(c_71, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_36])).
% 1.81/1.23  tff(c_70, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_36])).
% 1.81/1.23  tff(c_72, plain, (![C_36, A_37, D_38]: (r2_hidden(C_36, k1_relat_1(A_37)) | ~r2_hidden(k4_tarski(C_36, D_38), A_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.23  tff(c_75, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_70, c_72])).
% 1.81/1.23  tff(c_79, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_75])).
% 1.81/1.23  tff(c_81, plain, (k1_funct_1('#skF_7', '#skF_5')!='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 1.81/1.23  tff(c_80, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_32])).
% 1.81/1.23  tff(c_82, plain, (![C_39, A_40, D_41]: (r2_hidden(C_39, k1_relat_1(A_40)) | ~r2_hidden(k4_tarski(C_39, D_41), A_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.81/1.23  tff(c_86, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_80, c_82])).
% 1.81/1.23  tff(c_133, plain, (![A_56, B_57, C_58]: (k1_funct_1(A_56, B_57)=C_58 | ~r2_hidden(k4_tarski(B_57, C_58), A_56) | ~r2_hidden(B_57, k1_relat_1(A_56)) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.81/1.23  tff(c_150, plain, (k1_funct_1('#skF_7', '#skF_5')='#skF_6' | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_133])).
% 1.81/1.23  tff(c_158, plain, (k1_funct_1('#skF_7', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_86, c_150])).
% 1.81/1.23  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_158])).
% 1.81/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.23  
% 1.81/1.23  Inference rules
% 1.81/1.23  ----------------------
% 1.81/1.23  #Ref     : 0
% 1.81/1.23  #Sup     : 22
% 1.81/1.23  #Fact    : 0
% 1.81/1.23  #Define  : 0
% 1.81/1.23  #Split   : 2
% 1.81/1.23  #Chain   : 0
% 1.81/1.23  #Close   : 0
% 1.81/1.23  
% 1.81/1.23  Ordering : KBO
% 1.81/1.23  
% 1.81/1.23  Simplification rules
% 1.81/1.23  ----------------------
% 1.81/1.23  #Subsume      : 3
% 1.81/1.23  #Demod        : 12
% 1.81/1.23  #Tautology    : 13
% 1.81/1.23  #SimpNegUnit  : 3
% 1.81/1.23  #BackRed      : 0
% 1.81/1.23  
% 1.81/1.23  #Partial instantiations: 0
% 1.81/1.23  #Strategies tried      : 1
% 1.81/1.23  
% 1.81/1.23  Timing (in seconds)
% 1.81/1.23  ----------------------
% 2.01/1.23  Preprocessing        : 0.27
% 2.01/1.23  Parsing              : 0.14
% 2.01/1.23  CNF conversion       : 0.02
% 2.01/1.23  Main loop            : 0.16
% 2.01/1.23  Inferencing          : 0.07
% 2.01/1.23  Reduction            : 0.04
% 2.01/1.23  Demodulation         : 0.03
% 2.01/1.23  BG Simplification    : 0.02
% 2.01/1.23  Subsumption          : 0.03
% 2.01/1.23  Abstraction          : 0.01
% 2.01/1.23  MUC search           : 0.00
% 2.01/1.23  Cooper               : 0.00
% 2.01/1.23  Total                : 0.46
% 2.01/1.23  Index Insertion      : 0.00
% 2.01/1.23  Index Deletion       : 0.00
% 2.01/1.23  Index Matching       : 0.00
% 2.01/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
