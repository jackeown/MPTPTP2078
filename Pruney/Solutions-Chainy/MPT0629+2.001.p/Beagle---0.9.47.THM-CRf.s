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
% DateTime   : Thu Dec  3 10:03:17 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  60 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k2_relat_1(k5_relat_1(C,B)))
             => r2_hidden(A,k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    r2_hidden('#skF_9',k2_relat_1(k5_relat_1('#skF_11','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [B_64,A_62] :
      ( k9_relat_1(B_64,k2_relat_1(A_62)) = k2_relat_1(k5_relat_1(A_62,B_64))
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,(
    ! [A_89,B_90,D_91] :
      ( r2_hidden(k4_tarski('#skF_4'(A_89,B_90,k9_relat_1(A_89,B_90),D_91),D_91),A_89)
      | ~ r2_hidden(D_91,k9_relat_1(A_89,B_90))
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [C_58,A_43,D_61] :
      ( r2_hidden(C_58,k2_relat_1(A_43))
      | ~ r2_hidden(k4_tarski(D_61,C_58),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,(
    ! [D_92,A_93,B_94] :
      ( r2_hidden(D_92,k2_relat_1(A_93))
      | ~ r2_hidden(D_92,k9_relat_1(A_93,B_94))
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_104,c_22])).

tff(c_161,plain,(
    ! [D_97,B_98,A_99] :
      ( r2_hidden(D_97,k2_relat_1(B_98))
      | ~ r2_hidden(D_97,k2_relat_1(k5_relat_1(A_99,B_98)))
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_115])).

tff(c_192,plain,
    ( r2_hidden('#skF_9',k2_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_36,c_161])).

tff(c_202,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_192])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:44:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.37  
% 2.21/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.37  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_3 > #skF_8 > #skF_7 > #skF_5
% 2.21/1.37  
% 2.21/1.37  %Foreground sorts:
% 2.21/1.37  
% 2.21/1.37  
% 2.21/1.37  %Background operators:
% 2.21/1.37  
% 2.21/1.37  
% 2.21/1.37  %Foreground operators:
% 2.21/1.37  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.21/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.21/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.21/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.37  tff('#skF_11', type, '#skF_11': $i).
% 2.21/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.21/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.21/1.37  tff('#skF_10', type, '#skF_10': $i).
% 2.21/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.21/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.21/1.37  tff('#skF_9', type, '#skF_9': $i).
% 2.21/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.21/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.21/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.37  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.21/1.37  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.21/1.37  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.21/1.37  
% 2.21/1.38  tff(f_67, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k2_relat_1(k5_relat_1(C, B))) => r2_hidden(A, k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_funct_1)).
% 2.21/1.38  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.21/1.38  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 2.21/1.38  tff(f_46, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.21/1.38  tff(c_34, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.38  tff(c_40, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.38  tff(c_44, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.38  tff(c_36, plain, (r2_hidden('#skF_9', k2_relat_1(k5_relat_1('#skF_11', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.21/1.38  tff(c_32, plain, (![B_64, A_62]: (k9_relat_1(B_64, k2_relat_1(A_62))=k2_relat_1(k5_relat_1(A_62, B_64)) | ~v1_relat_1(B_64) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.38  tff(c_104, plain, (![A_89, B_90, D_91]: (r2_hidden(k4_tarski('#skF_4'(A_89, B_90, k9_relat_1(A_89, B_90), D_91), D_91), A_89) | ~r2_hidden(D_91, k9_relat_1(A_89, B_90)) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.38  tff(c_22, plain, (![C_58, A_43, D_61]: (r2_hidden(C_58, k2_relat_1(A_43)) | ~r2_hidden(k4_tarski(D_61, C_58), A_43))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.21/1.38  tff(c_115, plain, (![D_92, A_93, B_94]: (r2_hidden(D_92, k2_relat_1(A_93)) | ~r2_hidden(D_92, k9_relat_1(A_93, B_94)) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_104, c_22])).
% 2.21/1.38  tff(c_161, plain, (![D_97, B_98, A_99]: (r2_hidden(D_97, k2_relat_1(B_98)) | ~r2_hidden(D_97, k2_relat_1(k5_relat_1(A_99, B_98))) | ~v1_relat_1(B_98) | ~v1_relat_1(B_98) | ~v1_relat_1(A_99))), inference(superposition, [status(thm), theory('equality')], [c_32, c_115])).
% 2.21/1.38  tff(c_192, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_36, c_161])).
% 2.21/1.38  tff(c_202, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_192])).
% 2.21/1.38  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_202])).
% 2.21/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.38  
% 2.21/1.38  Inference rules
% 2.21/1.38  ----------------------
% 2.21/1.38  #Ref     : 0
% 2.21/1.38  #Sup     : 35
% 2.21/1.38  #Fact    : 0
% 2.21/1.38  #Define  : 0
% 2.21/1.38  #Split   : 0
% 2.21/1.38  #Chain   : 0
% 2.21/1.38  #Close   : 0
% 2.21/1.38  
% 2.21/1.38  Ordering : KBO
% 2.21/1.38  
% 2.21/1.38  Simplification rules
% 2.21/1.38  ----------------------
% 2.21/1.38  #Subsume      : 1
% 2.21/1.38  #Demod        : 2
% 2.21/1.38  #Tautology    : 3
% 2.21/1.38  #SimpNegUnit  : 1
% 2.21/1.38  #BackRed      : 0
% 2.21/1.38  
% 2.21/1.38  #Partial instantiations: 0
% 2.21/1.38  #Strategies tried      : 1
% 2.21/1.38  
% 2.21/1.38  Timing (in seconds)
% 2.21/1.38  ----------------------
% 2.21/1.38  Preprocessing        : 0.32
% 2.21/1.38  Parsing              : 0.16
% 2.21/1.38  CNF conversion       : 0.03
% 2.21/1.38  Main loop            : 0.24
% 2.21/1.38  Inferencing          : 0.09
% 2.21/1.38  Reduction            : 0.07
% 2.21/1.38  Demodulation         : 0.05
% 2.21/1.38  BG Simplification    : 0.02
% 2.21/1.38  Subsumption          : 0.05
% 2.21/1.38  Abstraction          : 0.02
% 2.21/1.38  MUC search           : 0.00
% 2.21/1.38  Cooper               : 0.00
% 2.21/1.38  Total                : 0.58
% 2.21/1.39  Index Insertion      : 0.00
% 2.21/1.39  Index Deletion       : 0.00
% 2.21/1.39  Index Matching       : 0.00
% 2.21/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
