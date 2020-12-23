%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:11 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   35 (  47 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  86 expanded)
%              Number of equality atoms :   13 (  28 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(c_38,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | k1_relat_1('#skF_7') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,(
    k1_relat_1('#skF_7') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_47,plain,(
    ! [A_24,B_25,D_26] :
      ( '#skF_4'(A_24,B_25,k1_funct_2(A_24,B_25),D_26) = D_26
      | ~ r2_hidden(D_26,k1_funct_2(A_24,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_funct_2('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_47])).

tff(c_70,plain,(
    ! [A_32,B_33,D_34] :
      ( k1_relat_1('#skF_4'(A_32,B_33,k1_funct_2(A_32,B_33),D_34)) = A_32
      | ~ r2_hidden(D_34,k1_funct_2(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_70])).

tff(c_86,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_86])).

tff(c_89,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_96,plain,(
    ! [A_38,B_39,D_40] :
      ( '#skF_4'(A_38,B_39,k1_funct_2(A_38,B_39),D_40) = D_40
      | ~ r2_hidden(D_40,k1_funct_2(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_funct_2('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_40,c_96])).

tff(c_146,plain,(
    ! [A_51,B_52,D_53] :
      ( r1_tarski(k2_relat_1('#skF_4'(A_51,B_52,k1_funct_2(A_51,B_52),D_53)),B_52)
      | ~ r2_hidden(D_53,k1_funct_2(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_149,plain,
    ( r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_146])).

tff(c_151,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_149])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.24  
% 1.78/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.24  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.78/1.24  
% 1.78/1.24  %Foreground sorts:
% 1.78/1.24  
% 1.78/1.24  
% 1.78/1.24  %Background operators:
% 1.78/1.24  
% 1.78/1.24  
% 1.78/1.24  %Foreground operators:
% 1.78/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.78/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.78/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.24  tff('#skF_7', type, '#skF_7': $i).
% 1.78/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.78/1.24  tff('#skF_5', type, '#skF_5': $i).
% 1.78/1.24  tff('#skF_6', type, '#skF_6': $i).
% 1.78/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.78/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.78/1.24  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 1.78/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.78/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.78/1.24  
% 1.95/1.25  tff(f_52, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_2)).
% 1.95/1.25  tff(f_41, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 1.95/1.25  tff(c_38, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | k1_relat_1('#skF_7')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.25  tff(c_45, plain, (k1_relat_1('#skF_7')!='#skF_5'), inference(splitLeft, [status(thm)], [c_38])).
% 1.95/1.25  tff(c_40, plain, (r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.25  tff(c_47, plain, (![A_24, B_25, D_26]: ('#skF_4'(A_24, B_25, k1_funct_2(A_24, B_25), D_26)=D_26 | ~r2_hidden(D_26, k1_funct_2(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.25  tff(c_50, plain, ('#skF_4'('#skF_5', '#skF_6', k1_funct_2('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_40, c_47])).
% 1.95/1.25  tff(c_70, plain, (![A_32, B_33, D_34]: (k1_relat_1('#skF_4'(A_32, B_33, k1_funct_2(A_32, B_33), D_34))=A_32 | ~r2_hidden(D_34, k1_funct_2(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.25  tff(c_82, plain, (k1_relat_1('#skF_7')='#skF_5' | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_70])).
% 1.95/1.25  tff(c_86, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_82])).
% 1.95/1.25  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_86])).
% 1.95/1.25  tff(c_89, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 1.95/1.25  tff(c_96, plain, (![A_38, B_39, D_40]: ('#skF_4'(A_38, B_39, k1_funct_2(A_38, B_39), D_40)=D_40 | ~r2_hidden(D_40, k1_funct_2(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.25  tff(c_99, plain, ('#skF_4'('#skF_5', '#skF_6', k1_funct_2('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_40, c_96])).
% 1.95/1.25  tff(c_146, plain, (![A_51, B_52, D_53]: (r1_tarski(k2_relat_1('#skF_4'(A_51, B_52, k1_funct_2(A_51, B_52), D_53)), B_52) | ~r2_hidden(D_53, k1_funct_2(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.25  tff(c_149, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_146])).
% 1.95/1.25  tff(c_151, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_149])).
% 1.95/1.25  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_151])).
% 1.95/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.25  
% 1.95/1.25  Inference rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Ref     : 0
% 1.95/1.25  #Sup     : 25
% 1.95/1.25  #Fact    : 0
% 1.95/1.25  #Define  : 0
% 1.95/1.25  #Split   : 1
% 1.95/1.25  #Chain   : 0
% 1.95/1.25  #Close   : 0
% 1.95/1.25  
% 1.95/1.25  Ordering : KBO
% 1.95/1.25  
% 1.95/1.25  Simplification rules
% 1.95/1.25  ----------------------
% 1.95/1.25  #Subsume      : 0
% 1.95/1.25  #Demod        : 14
% 1.95/1.25  #Tautology    : 15
% 1.95/1.25  #SimpNegUnit  : 2
% 1.95/1.25  #BackRed      : 0
% 1.95/1.25  
% 1.95/1.25  #Partial instantiations: 0
% 1.95/1.25  #Strategies tried      : 1
% 1.95/1.25  
% 1.95/1.25  Timing (in seconds)
% 1.95/1.25  ----------------------
% 1.95/1.25  Preprocessing        : 0.30
% 1.95/1.25  Parsing              : 0.14
% 1.95/1.25  CNF conversion       : 0.02
% 1.95/1.25  Main loop            : 0.13
% 1.95/1.25  Inferencing          : 0.04
% 1.95/1.25  Reduction            : 0.04
% 1.95/1.25  Demodulation         : 0.03
% 1.95/1.25  BG Simplification    : 0.02
% 1.95/1.25  Subsumption          : 0.02
% 1.95/1.25  Abstraction          : 0.01
% 1.95/1.25  MUC search           : 0.00
% 1.95/1.25  Cooper               : 0.00
% 1.95/1.25  Total                : 0.46
% 1.95/1.25  Index Insertion      : 0.00
% 1.95/1.25  Index Deletion       : 0.00
% 1.95/1.25  Index Matching       : 0.00
% 1.95/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
