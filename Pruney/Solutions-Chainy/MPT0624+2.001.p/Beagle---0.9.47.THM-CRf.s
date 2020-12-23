%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:15 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   40 (  51 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 ( 101 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_8 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & ! [D] :
                    ~ ( r2_hidden(D,k1_relat_1(B))
                      & C = k1_funct_1(B,D) ) )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_6',k2_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_46,c_4])).

tff(c_34,plain,(
    ! [C_49] :
      ( r2_hidden('#skF_8'(C_49),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_49,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_53,plain,(
    ! [C_58,B_59,A_60] :
      ( r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [C_49,B_59] :
      ( r2_hidden('#skF_8'(C_49),B_59)
      | ~ r1_tarski(k1_relat_1('#skF_7'),B_59)
      | ~ r2_hidden(C_49,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_30,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [C_49] :
      ( k1_funct_1('#skF_7','#skF_8'(C_49)) = C_49
      | ~ r2_hidden(C_49,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_73,plain,(
    ! [A_66,D_67] :
      ( r2_hidden(k1_funct_1(A_66,D_67),k2_relat_1(A_66))
      | ~ r2_hidden(D_67,k1_relat_1(A_66))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    ! [C_49] :
      ( r2_hidden(C_49,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(C_49),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(C_49,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_73])).

tff(c_82,plain,(
    ! [C_68] :
      ( r2_hidden(C_68,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(C_68),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_68,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_78])).

tff(c_86,plain,(
    ! [C_49] :
      ( r2_hidden(C_49,k2_relat_1('#skF_7'))
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_49,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_59,c_82])).

tff(c_94,plain,(
    ! [C_69] :
      ( r2_hidden(C_69,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_69,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_86])).

tff(c_120,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_74,k2_relat_1('#skF_7')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_94,c_4])).

tff(c_128,plain,(
    r1_tarski('#skF_6',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:24:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.16  
% 1.79/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.16  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_8 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 1.79/1.16  
% 1.79/1.16  %Foreground sorts:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Background operators:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Foreground operators:
% 1.79/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.16  tff('#skF_8', type, '#skF_8': $i > $i).
% 1.79/1.16  tff('#skF_7', type, '#skF_7': $i).
% 1.79/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.79/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.79/1.16  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.79/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.79/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.79/1.16  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.79/1.16  
% 1.89/1.17  tff(f_64, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, k1_relat_1(B)) & (C = k1_funct_1(B, D)))))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_funct_1)).
% 1.89/1.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.89/1.17  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 1.89/1.17  tff(c_26, plain, (~r1_tarski('#skF_6', k2_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.17  tff(c_46, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.17  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.17  tff(c_51, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_46, c_4])).
% 1.89/1.17  tff(c_34, plain, (![C_49]: (r2_hidden('#skF_8'(C_49), k1_relat_1('#skF_7')) | ~r2_hidden(C_49, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.17  tff(c_53, plain, (![C_58, B_59, A_60]: (r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.17  tff(c_59, plain, (![C_49, B_59]: (r2_hidden('#skF_8'(C_49), B_59) | ~r1_tarski(k1_relat_1('#skF_7'), B_59) | ~r2_hidden(C_49, '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_53])).
% 1.89/1.17  tff(c_30, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.17  tff(c_28, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.17  tff(c_32, plain, (![C_49]: (k1_funct_1('#skF_7', '#skF_8'(C_49))=C_49 | ~r2_hidden(C_49, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.89/1.17  tff(c_73, plain, (![A_66, D_67]: (r2_hidden(k1_funct_1(A_66, D_67), k2_relat_1(A_66)) | ~r2_hidden(D_67, k1_relat_1(A_66)) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.89/1.17  tff(c_78, plain, (![C_49]: (r2_hidden(C_49, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(C_49), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(C_49, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_73])).
% 1.89/1.17  tff(c_82, plain, (![C_68]: (r2_hidden(C_68, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(C_68), k1_relat_1('#skF_7')) | ~r2_hidden(C_68, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_78])).
% 1.89/1.17  tff(c_86, plain, (![C_49]: (r2_hidden(C_49, k2_relat_1('#skF_7')) | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_7')) | ~r2_hidden(C_49, '#skF_6'))), inference(resolution, [status(thm)], [c_59, c_82])).
% 1.89/1.17  tff(c_94, plain, (![C_69]: (r2_hidden(C_69, k2_relat_1('#skF_7')) | ~r2_hidden(C_69, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_86])).
% 1.89/1.17  tff(c_120, plain, (![A_74]: (r1_tarski(A_74, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_1'(A_74, k2_relat_1('#skF_7')), '#skF_6'))), inference(resolution, [status(thm)], [c_94, c_4])).
% 1.89/1.17  tff(c_128, plain, (r1_tarski('#skF_6', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_120])).
% 1.89/1.17  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_128])).
% 1.89/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.17  
% 1.89/1.17  Inference rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Ref     : 0
% 1.89/1.17  #Sup     : 20
% 1.89/1.17  #Fact    : 0
% 1.89/1.17  #Define  : 0
% 1.89/1.17  #Split   : 0
% 1.89/1.17  #Chain   : 0
% 1.89/1.17  #Close   : 0
% 1.89/1.17  
% 1.89/1.17  Ordering : KBO
% 1.89/1.17  
% 1.89/1.17  Simplification rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Subsume      : 3
% 1.89/1.17  #Demod        : 3
% 1.89/1.17  #Tautology    : 6
% 1.89/1.17  #SimpNegUnit  : 1
% 1.89/1.17  #BackRed      : 0
% 1.89/1.17  
% 1.89/1.17  #Partial instantiations: 0
% 1.89/1.17  #Strategies tried      : 1
% 1.89/1.17  
% 1.89/1.17  Timing (in seconds)
% 1.89/1.17  ----------------------
% 1.89/1.18  Preprocessing        : 0.28
% 1.89/1.18  Parsing              : 0.15
% 1.89/1.18  CNF conversion       : 0.03
% 1.89/1.18  Main loop            : 0.14
% 1.89/1.18  Inferencing          : 0.06
% 1.89/1.18  Reduction            : 0.04
% 1.89/1.18  Demodulation         : 0.03
% 1.89/1.18  BG Simplification    : 0.02
% 1.89/1.18  Subsumption          : 0.03
% 1.89/1.18  Abstraction          : 0.01
% 1.89/1.18  MUC search           : 0.00
% 1.89/1.18  Cooper               : 0.00
% 1.89/1.18  Total                : 0.44
% 1.89/1.18  Index Insertion      : 0.00
% 1.89/1.18  Index Deletion       : 0.00
% 1.89/1.18  Index Matching       : 0.00
% 1.89/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
