%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:18 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  90 expanded)
%              Number of equality atoms :    2 (   3 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_11 > #skF_6 > #skF_4 > #skF_5 > #skF_3 > #skF_13 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k2_relat_1(k5_relat_1(C,B)))
             => r2_hidden(A,k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_44,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ! [A_119,B_120] :
      ( v1_relat_1(k5_relat_1(A_119,B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    r2_hidden('#skF_11',k2_relat_1(k5_relat_1('#skF_13','#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1,C_16] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,k2_relat_1(A_1),C_16),C_16),A_1)
      | ~ r2_hidden(C_16,k2_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_103,plain,(
    ! [A_158,B_159,E_160,D_161] :
      ( r2_hidden(k4_tarski('#skF_5'(k5_relat_1(A_158,B_159),B_159,E_160,A_158,D_161),E_160),B_159)
      | ~ r2_hidden(k4_tarski(D_161,E_160),k5_relat_1(A_158,B_159))
      | ~ v1_relat_1(k5_relat_1(A_158,B_159))
      | ~ v1_relat_1(B_159)
      | ~ v1_relat_1(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_115,plain,(
    ! [E_162,B_163,D_164,A_165] :
      ( r2_hidden(E_162,k2_relat_1(B_163))
      | ~ r2_hidden(k4_tarski(D_164,E_162),k5_relat_1(A_165,B_163))
      | ~ v1_relat_1(k5_relat_1(A_165,B_163))
      | ~ v1_relat_1(B_163)
      | ~ v1_relat_1(A_165) ) ),
    inference(resolution,[status(thm)],[c_103,c_4])).

tff(c_141,plain,(
    ! [C_166,B_167,A_168] :
      ( r2_hidden(C_166,k2_relat_1(B_167))
      | ~ v1_relat_1(k5_relat_1(A_168,B_167))
      | ~ v1_relat_1(B_167)
      | ~ v1_relat_1(A_168)
      | ~ r2_hidden(C_166,k2_relat_1(k5_relat_1(A_168,B_167))) ) ),
    inference(resolution,[status(thm)],[c_2,c_115])).

tff(c_180,plain,
    ( r2_hidden('#skF_11',k2_relat_1('#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_13','#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_36,c_141])).

tff(c_192,plain,
    ( r2_hidden('#skF_11',k2_relat_1('#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_180])).

tff(c_193,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_13','#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_192])).

tff(c_196,plain,
    ( ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_32,c_193])).

tff(c_200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_196])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:05:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > #nlpp > k2_relat_1 > #skF_11 > #skF_6 > #skF_4 > #skF_5 > #skF_3 > #skF_13 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_10
% 2.17/1.24  
% 2.17/1.24  %Foreground sorts:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Background operators:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Foreground operators:
% 2.17/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.24  tff('#skF_11', type, '#skF_11': $i).
% 2.17/1.24  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.17/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.17/1.24  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 2.17/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.17/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.24  tff('#skF_13', type, '#skF_13': $i).
% 2.17/1.24  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.17/1.24  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.17/1.24  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.17/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.24  tff('#skF_12', type, '#skF_12': $i).
% 2.17/1.24  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 2.17/1.24  
% 2.17/1.25  tff(f_71, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k2_relat_1(k5_relat_1(C, B))) => r2_hidden(A, k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_1)).
% 2.17/1.25  tff(f_57, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.17/1.25  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.17/1.25  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 2.17/1.25  tff(c_40, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.25  tff(c_44, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.25  tff(c_32, plain, (![A_119, B_120]: (v1_relat_1(k5_relat_1(A_119, B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.25  tff(c_34, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.25  tff(c_36, plain, (r2_hidden('#skF_11', k2_relat_1(k5_relat_1('#skF_13', '#skF_12')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.25  tff(c_2, plain, (![A_1, C_16]: (r2_hidden(k4_tarski('#skF_4'(A_1, k2_relat_1(A_1), C_16), C_16), A_1) | ~r2_hidden(C_16, k2_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.25  tff(c_103, plain, (![A_158, B_159, E_160, D_161]: (r2_hidden(k4_tarski('#skF_5'(k5_relat_1(A_158, B_159), B_159, E_160, A_158, D_161), E_160), B_159) | ~r2_hidden(k4_tarski(D_161, E_160), k5_relat_1(A_158, B_159)) | ~v1_relat_1(k5_relat_1(A_158, B_159)) | ~v1_relat_1(B_159) | ~v1_relat_1(A_158))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.25  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.25  tff(c_115, plain, (![E_162, B_163, D_164, A_165]: (r2_hidden(E_162, k2_relat_1(B_163)) | ~r2_hidden(k4_tarski(D_164, E_162), k5_relat_1(A_165, B_163)) | ~v1_relat_1(k5_relat_1(A_165, B_163)) | ~v1_relat_1(B_163) | ~v1_relat_1(A_165))), inference(resolution, [status(thm)], [c_103, c_4])).
% 2.17/1.25  tff(c_141, plain, (![C_166, B_167, A_168]: (r2_hidden(C_166, k2_relat_1(B_167)) | ~v1_relat_1(k5_relat_1(A_168, B_167)) | ~v1_relat_1(B_167) | ~v1_relat_1(A_168) | ~r2_hidden(C_166, k2_relat_1(k5_relat_1(A_168, B_167))))), inference(resolution, [status(thm)], [c_2, c_115])).
% 2.17/1.25  tff(c_180, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_12')) | ~v1_relat_1(k5_relat_1('#skF_13', '#skF_12')) | ~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_36, c_141])).
% 2.17/1.25  tff(c_192, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_12')) | ~v1_relat_1(k5_relat_1('#skF_13', '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_180])).
% 2.17/1.25  tff(c_193, plain, (~v1_relat_1(k5_relat_1('#skF_13', '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_34, c_192])).
% 2.17/1.25  tff(c_196, plain, (~v1_relat_1('#skF_12') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_32, c_193])).
% 2.17/1.25  tff(c_200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_196])).
% 2.17/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  Inference rules
% 2.17/1.25  ----------------------
% 2.17/1.25  #Ref     : 0
% 2.17/1.25  #Sup     : 30
% 2.17/1.25  #Fact    : 0
% 2.17/1.25  #Define  : 0
% 2.17/1.25  #Split   : 0
% 2.17/1.25  #Chain   : 0
% 2.17/1.25  #Close   : 0
% 2.17/1.25  
% 2.17/1.25  Ordering : KBO
% 2.17/1.25  
% 2.17/1.25  Simplification rules
% 2.17/1.25  ----------------------
% 2.17/1.25  #Subsume      : 0
% 2.17/1.25  #Demod        : 4
% 2.17/1.25  #Tautology    : 3
% 2.17/1.25  #SimpNegUnit  : 1
% 2.17/1.25  #BackRed      : 0
% 2.17/1.25  
% 2.17/1.25  #Partial instantiations: 0
% 2.17/1.25  #Strategies tried      : 1
% 2.17/1.25  
% 2.17/1.25  Timing (in seconds)
% 2.17/1.25  ----------------------
% 2.17/1.25  Preprocessing        : 0.29
% 2.17/1.25  Parsing              : 0.15
% 2.17/1.25  CNF conversion       : 0.03
% 2.17/1.25  Main loop            : 0.20
% 2.17/1.25  Inferencing          : 0.08
% 2.17/1.25  Reduction            : 0.05
% 2.17/1.25  Demodulation         : 0.04
% 2.17/1.25  BG Simplification    : 0.02
% 2.17/1.25  Subsumption          : 0.04
% 2.17/1.25  Abstraction          : 0.01
% 2.17/1.25  MUC search           : 0.00
% 2.17/1.25  Cooper               : 0.00
% 2.26/1.25  Total                : 0.51
% 2.26/1.25  Index Insertion      : 0.00
% 2.26/1.25  Index Deletion       : 0.00
% 2.26/1.25  Index Matching       : 0.00
% 2.26/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
