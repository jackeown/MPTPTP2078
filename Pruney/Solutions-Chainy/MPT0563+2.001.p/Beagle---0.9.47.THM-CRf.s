%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:13 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   40 (  42 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  61 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( v1_relat_1(k7_relat_1(A_25,B_26))
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden(k4_tarski(A_27,'#skF_6'(A_27,B_28,C_29)),C_29)
      | ~ r2_hidden(A_27,k10_relat_1(C_29,B_28))
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_33] :
      ( k7_relat_1(A_33,k1_relat_1(A_33)) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_91,plain,(
    ! [D_61,B_62,E_63,A_64] :
      ( r2_hidden(D_61,B_62)
      | ~ r2_hidden(k4_tarski(D_61,E_63),k7_relat_1(A_64,B_62))
      | ~ v1_relat_1(k7_relat_1(A_64,B_62))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_195,plain,(
    ! [D_89,A_90,E_91] :
      ( r2_hidden(D_89,k1_relat_1(A_90))
      | ~ r2_hidden(k4_tarski(D_89,E_91),A_90)
      | ~ v1_relat_1(k7_relat_1(A_90,k1_relat_1(A_90)))
      | ~ v1_relat_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_91])).

tff(c_202,plain,(
    ! [A_92,C_93,B_94] :
      ( r2_hidden(A_92,k1_relat_1(C_93))
      | ~ v1_relat_1(k7_relat_1(C_93,k1_relat_1(C_93)))
      | ~ r2_hidden(A_92,k10_relat_1(C_93,B_94))
      | ~ v1_relat_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_32,c_195])).

tff(c_209,plain,(
    ! [A_95,A_96,B_97] :
      ( r2_hidden(A_95,k1_relat_1(A_96))
      | ~ r2_hidden(A_95,k10_relat_1(A_96,B_97))
      | ~ v1_relat_1(A_96) ) ),
    inference(resolution,[status(thm)],[c_26,c_202])).

tff(c_245,plain,(
    ! [A_98,B_99,B_100] :
      ( r2_hidden('#skF_1'(k10_relat_1(A_98,B_99),B_100),k1_relat_1(A_98))
      | ~ v1_relat_1(A_98)
      | r1_tarski(k10_relat_1(A_98,B_99),B_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_209])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_278,plain,(
    ! [A_105,B_106] :
      ( ~ v1_relat_1(A_105)
      | r1_tarski(k10_relat_1(A_105,B_106),k1_relat_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_245,c_4])).

tff(c_38,plain,(
    ~ r1_tarski(k10_relat_1('#skF_8','#skF_7'),k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_283,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_278,c_38])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.27  
% 2.29/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.27  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1
% 2.29/1.27  
% 2.29/1.27  %Foreground sorts:
% 2.29/1.27  
% 2.29/1.27  
% 2.29/1.27  %Background operators:
% 2.29/1.27  
% 2.29/1.27  
% 2.29/1.27  %Foreground operators:
% 2.29/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.29/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.29/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.29/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.29/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.29/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.29/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.29/1.27  tff('#skF_8', type, '#skF_8': $i).
% 2.29/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.29/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.29/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.27  
% 2.29/1.28  tff(f_70, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.29/1.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.29/1.28  tff(f_50, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.29/1.28  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.29/1.28  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.29/1.28  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 2.29/1.28  tff(c_40, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.29/1.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.28  tff(c_26, plain, (![A_25, B_26]: (v1_relat_1(k7_relat_1(A_25, B_26)) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.29/1.28  tff(c_32, plain, (![A_27, B_28, C_29]: (r2_hidden(k4_tarski(A_27, '#skF_6'(A_27, B_28, C_29)), C_29) | ~r2_hidden(A_27, k10_relat_1(C_29, B_28)) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.29/1.28  tff(c_36, plain, (![A_33]: (k7_relat_1(A_33, k1_relat_1(A_33))=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.29/1.28  tff(c_91, plain, (![D_61, B_62, E_63, A_64]: (r2_hidden(D_61, B_62) | ~r2_hidden(k4_tarski(D_61, E_63), k7_relat_1(A_64, B_62)) | ~v1_relat_1(k7_relat_1(A_64, B_62)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.29/1.28  tff(c_195, plain, (![D_89, A_90, E_91]: (r2_hidden(D_89, k1_relat_1(A_90)) | ~r2_hidden(k4_tarski(D_89, E_91), A_90) | ~v1_relat_1(k7_relat_1(A_90, k1_relat_1(A_90))) | ~v1_relat_1(A_90) | ~v1_relat_1(A_90))), inference(superposition, [status(thm), theory('equality')], [c_36, c_91])).
% 2.29/1.28  tff(c_202, plain, (![A_92, C_93, B_94]: (r2_hidden(A_92, k1_relat_1(C_93)) | ~v1_relat_1(k7_relat_1(C_93, k1_relat_1(C_93))) | ~r2_hidden(A_92, k10_relat_1(C_93, B_94)) | ~v1_relat_1(C_93))), inference(resolution, [status(thm)], [c_32, c_195])).
% 2.29/1.28  tff(c_209, plain, (![A_95, A_96, B_97]: (r2_hidden(A_95, k1_relat_1(A_96)) | ~r2_hidden(A_95, k10_relat_1(A_96, B_97)) | ~v1_relat_1(A_96))), inference(resolution, [status(thm)], [c_26, c_202])).
% 2.29/1.28  tff(c_245, plain, (![A_98, B_99, B_100]: (r2_hidden('#skF_1'(k10_relat_1(A_98, B_99), B_100), k1_relat_1(A_98)) | ~v1_relat_1(A_98) | r1_tarski(k10_relat_1(A_98, B_99), B_100))), inference(resolution, [status(thm)], [c_6, c_209])).
% 2.29/1.28  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.28  tff(c_278, plain, (![A_105, B_106]: (~v1_relat_1(A_105) | r1_tarski(k10_relat_1(A_105, B_106), k1_relat_1(A_105)))), inference(resolution, [status(thm)], [c_245, c_4])).
% 2.29/1.28  tff(c_38, plain, (~r1_tarski(k10_relat_1('#skF_8', '#skF_7'), k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.29/1.28  tff(c_283, plain, (~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_278, c_38])).
% 2.29/1.28  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_283])).
% 2.29/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.28  
% 2.29/1.28  Inference rules
% 2.29/1.28  ----------------------
% 2.29/1.28  #Ref     : 0
% 2.29/1.28  #Sup     : 58
% 2.29/1.28  #Fact    : 0
% 2.29/1.28  #Define  : 0
% 2.29/1.28  #Split   : 0
% 2.29/1.28  #Chain   : 0
% 2.29/1.28  #Close   : 0
% 2.29/1.28  
% 2.29/1.28  Ordering : KBO
% 2.29/1.29  
% 2.29/1.29  Simplification rules
% 2.29/1.29  ----------------------
% 2.29/1.29  #Subsume      : 3
% 2.29/1.29  #Demod        : 1
% 2.29/1.29  #Tautology    : 8
% 2.29/1.29  #SimpNegUnit  : 0
% 2.29/1.29  #BackRed      : 0
% 2.29/1.29  
% 2.29/1.29  #Partial instantiations: 0
% 2.29/1.29  #Strategies tried      : 1
% 2.29/1.29  
% 2.29/1.29  Timing (in seconds)
% 2.29/1.29  ----------------------
% 2.29/1.29  Preprocessing        : 0.30
% 2.29/1.29  Parsing              : 0.15
% 2.29/1.29  CNF conversion       : 0.03
% 2.29/1.29  Main loop            : 0.25
% 2.29/1.29  Inferencing          : 0.10
% 2.29/1.29  Reduction            : 0.06
% 2.29/1.29  Demodulation         : 0.04
% 2.29/1.29  BG Simplification    : 0.02
% 2.29/1.29  Subsumption          : 0.06
% 2.29/1.29  Abstraction          : 0.01
% 2.29/1.29  MUC search           : 0.00
% 2.29/1.29  Cooper               : 0.00
% 2.29/1.29  Total                : 0.57
% 2.29/1.29  Index Insertion      : 0.00
% 2.29/1.29  Index Deletion       : 0.00
% 2.29/1.29  Index Matching       : 0.00
% 2.29/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
