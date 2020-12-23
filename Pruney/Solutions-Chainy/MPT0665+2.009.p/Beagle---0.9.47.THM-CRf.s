%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:15 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  84 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(A,B) )
         => r2_hidden(k1_funct_1(C,A),k2_relat_1(k7_relat_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ! [A_39,B_40] :
      ( v1_relat_1(k7_relat_1(A_39,B_40))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [A_41,C_43] :
      ( r2_hidden(k4_tarski(A_41,k1_funct_1(C_43,A_41)),C_43)
      | ~ r2_hidden(A_41,k1_relat_1(C_43))
      | ~ v1_funct_1(C_43)
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_236,plain,(
    ! [D_94,E_95,A_96,B_97] :
      ( r2_hidden(k4_tarski(D_94,E_95),k7_relat_1(A_96,B_97))
      | ~ r2_hidden(k4_tarski(D_94,E_95),A_96)
      | ~ r2_hidden(D_94,B_97)
      | ~ v1_relat_1(k7_relat_1(A_96,B_97))
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k2_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(D_38,C_35),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_293,plain,(
    ! [E_102,A_103,B_104,D_105] :
      ( r2_hidden(E_102,k2_relat_1(k7_relat_1(A_103,B_104)))
      | ~ r2_hidden(k4_tarski(D_105,E_102),A_103)
      | ~ r2_hidden(D_105,B_104)
      | ~ v1_relat_1(k7_relat_1(A_103,B_104))
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_236,c_22])).

tff(c_497,plain,(
    ! [C_128,A_129,B_130] :
      ( r2_hidden(k1_funct_1(C_128,A_129),k2_relat_1(k7_relat_1(C_128,B_130)))
      | ~ r2_hidden(A_129,B_130)
      | ~ v1_relat_1(k7_relat_1(C_128,B_130))
      | ~ r2_hidden(A_129,k1_relat_1(C_128))
      | ~ v1_funct_1(C_128)
      | ~ v1_relat_1(C_128) ) ),
    inference(resolution,[status(thm)],[c_34,c_293])).

tff(c_40,plain,(
    ~ r2_hidden(k1_funct_1('#skF_11','#skF_9'),k2_relat_1(k7_relat_1('#skF_11','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_500,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_497,c_40])).

tff(c_509,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_500])).

tff(c_512,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_32,c_509])).

tff(c_516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:09:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.38  
% 2.65/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.38  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_3 > #skF_8 > #skF_7 > #skF_5
% 2.65/1.38  
% 2.65/1.38  %Foreground sorts:
% 2.65/1.38  
% 2.65/1.38  
% 2.65/1.38  %Background operators:
% 2.65/1.38  
% 2.65/1.38  
% 2.65/1.38  %Foreground operators:
% 2.65/1.38  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.65/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.65/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.38  tff('#skF_11', type, '#skF_11': $i).
% 2.65/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.65/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.65/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.65/1.38  tff('#skF_10', type, '#skF_10': $i).
% 2.65/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.65/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.65/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.65/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.38  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.65/1.38  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.65/1.38  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.65/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.38  
% 2.65/1.39  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(A, B)) => r2_hidden(k1_funct_1(C, A), k2_relat_1(k7_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_1)).
% 2.65/1.39  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.65/1.39  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.65/1.39  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 2.65/1.39  tff(f_47, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.65/1.39  tff(c_48, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.39  tff(c_32, plain, (![A_39, B_40]: (v1_relat_1(k7_relat_1(A_39, B_40)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.65/1.39  tff(c_46, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.39  tff(c_44, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.39  tff(c_42, plain, (r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.39  tff(c_34, plain, (![A_41, C_43]: (r2_hidden(k4_tarski(A_41, k1_funct_1(C_43, A_41)), C_43) | ~r2_hidden(A_41, k1_relat_1(C_43)) | ~v1_funct_1(C_43) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.39  tff(c_236, plain, (![D_94, E_95, A_96, B_97]: (r2_hidden(k4_tarski(D_94, E_95), k7_relat_1(A_96, B_97)) | ~r2_hidden(k4_tarski(D_94, E_95), A_96) | ~r2_hidden(D_94, B_97) | ~v1_relat_1(k7_relat_1(A_96, B_97)) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.39  tff(c_22, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k2_relat_1(A_20)) | ~r2_hidden(k4_tarski(D_38, C_35), A_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.39  tff(c_293, plain, (![E_102, A_103, B_104, D_105]: (r2_hidden(E_102, k2_relat_1(k7_relat_1(A_103, B_104))) | ~r2_hidden(k4_tarski(D_105, E_102), A_103) | ~r2_hidden(D_105, B_104) | ~v1_relat_1(k7_relat_1(A_103, B_104)) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_236, c_22])).
% 2.65/1.39  tff(c_497, plain, (![C_128, A_129, B_130]: (r2_hidden(k1_funct_1(C_128, A_129), k2_relat_1(k7_relat_1(C_128, B_130))) | ~r2_hidden(A_129, B_130) | ~v1_relat_1(k7_relat_1(C_128, B_130)) | ~r2_hidden(A_129, k1_relat_1(C_128)) | ~v1_funct_1(C_128) | ~v1_relat_1(C_128))), inference(resolution, [status(thm)], [c_34, c_293])).
% 2.65/1.39  tff(c_40, plain, (~r2_hidden(k1_funct_1('#skF_11', '#skF_9'), k2_relat_1(k7_relat_1('#skF_11', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.39  tff(c_500, plain, (~r2_hidden('#skF_9', '#skF_10') | ~v1_relat_1(k7_relat_1('#skF_11', '#skF_10')) | ~r2_hidden('#skF_9', k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_497, c_40])).
% 2.65/1.39  tff(c_509, plain, (~v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_500])).
% 2.65/1.39  tff(c_512, plain, (~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_32, c_509])).
% 2.65/1.39  tff(c_516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_512])).
% 2.65/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.39  
% 2.65/1.39  Inference rules
% 2.65/1.39  ----------------------
% 2.65/1.39  #Ref     : 0
% 2.65/1.39  #Sup     : 97
% 2.65/1.39  #Fact    : 0
% 2.65/1.39  #Define  : 0
% 2.65/1.39  #Split   : 0
% 2.65/1.39  #Chain   : 0
% 2.65/1.39  #Close   : 0
% 2.65/1.39  
% 2.65/1.39  Ordering : KBO
% 2.65/1.39  
% 2.65/1.39  Simplification rules
% 2.65/1.39  ----------------------
% 2.65/1.39  #Subsume      : 4
% 2.65/1.39  #Demod        : 5
% 2.65/1.39  #Tautology    : 16
% 2.65/1.39  #SimpNegUnit  : 0
% 2.65/1.39  #BackRed      : 0
% 2.65/1.39  
% 2.65/1.39  #Partial instantiations: 0
% 2.65/1.39  #Strategies tried      : 1
% 2.65/1.39  
% 2.65/1.39  Timing (in seconds)
% 2.65/1.39  ----------------------
% 2.65/1.39  Preprocessing        : 0.29
% 2.65/1.39  Parsing              : 0.14
% 2.65/1.39  CNF conversion       : 0.03
% 2.65/1.39  Main loop            : 0.34
% 2.65/1.39  Inferencing          : 0.14
% 2.65/1.39  Reduction            : 0.08
% 2.65/1.39  Demodulation         : 0.05
% 2.65/1.39  BG Simplification    : 0.02
% 2.65/1.39  Subsumption          : 0.07
% 2.65/1.39  Abstraction          : 0.02
% 2.65/1.39  MUC search           : 0.00
% 2.65/1.39  Cooper               : 0.00
% 2.65/1.39  Total                : 0.65
% 2.65/1.39  Index Insertion      : 0.00
% 2.65/1.39  Index Deletion       : 0.00
% 2.65/1.39  Index Matching       : 0.00
% 2.65/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
