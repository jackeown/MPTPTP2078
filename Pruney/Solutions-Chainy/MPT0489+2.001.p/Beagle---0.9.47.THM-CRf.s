%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:35 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  54 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(k7_relat_1(A_44,B_45))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [C_40,A_25] :
      ( r2_hidden(k4_tarski(C_40,'#skF_9'(A_25,k1_relat_1(A_25),C_40)),A_25)
      | ~ r2_hidden(C_40,k1_relat_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,(
    ! [D_73,B_74,E_75,A_76] :
      ( r2_hidden(D_73,B_74)
      | ~ r2_hidden(k4_tarski(D_73,E_75),k7_relat_1(A_76,B_74))
      | ~ v1_relat_1(k7_relat_1(A_76,B_74))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    ! [C_77,B_78,A_79] :
      ( r2_hidden(C_77,B_78)
      | ~ v1_relat_1(k7_relat_1(A_79,B_78))
      | ~ v1_relat_1(A_79)
      | ~ r2_hidden(C_77,k1_relat_1(k7_relat_1(A_79,B_78))) ) ),
    inference(resolution,[status(thm)],[c_26,c_80])).

tff(c_554,plain,(
    ! [A_155,B_156,B_157] :
      ( r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(A_155,B_156)),B_157),B_156)
      | ~ v1_relat_1(k7_relat_1(A_155,B_156))
      | ~ v1_relat_1(A_155)
      | r1_tarski(k1_relat_1(k7_relat_1(A_155,B_156)),B_157) ) ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_568,plain,(
    ! [A_158,B_159] :
      ( ~ v1_relat_1(k7_relat_1(A_158,B_159))
      | ~ v1_relat_1(A_158)
      | r1_tarski(k1_relat_1(k7_relat_1(A_158,B_159)),B_159) ) ),
    inference(resolution,[status(thm)],[c_554,c_4])).

tff(c_40,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_11','#skF_10')),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_582,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_568,c_40])).

tff(c_590,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_11','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_582])).

tff(c_593,plain,(
    ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_38,c_590])).

tff(c_597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.41  
% 2.71/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.41  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1
% 2.71/1.41  
% 2.71/1.41  %Foreground sorts:
% 2.71/1.41  
% 2.71/1.41  
% 2.71/1.41  %Background operators:
% 2.71/1.41  
% 2.71/1.41  
% 2.71/1.41  %Foreground operators:
% 2.71/1.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.41  tff('#skF_11', type, '#skF_11': $i).
% 2.71/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.71/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.71/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.71/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.71/1.41  tff('#skF_10', type, '#skF_10': $i).
% 2.71/1.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.71/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.71/1.41  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.71/1.41  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.71/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.71/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.41  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.71/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.71/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.71/1.41  
% 2.71/1.43  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.71/1.43  tff(f_58, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.71/1.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.71/1.43  tff(f_54, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.71/1.43  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 2.71/1.43  tff(c_42, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.43  tff(c_38, plain, (![A_44, B_45]: (v1_relat_1(k7_relat_1(A_44, B_45)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.71/1.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.43  tff(c_26, plain, (![C_40, A_25]: (r2_hidden(k4_tarski(C_40, '#skF_9'(A_25, k1_relat_1(A_25), C_40)), A_25) | ~r2_hidden(C_40, k1_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.71/1.43  tff(c_80, plain, (![D_73, B_74, E_75, A_76]: (r2_hidden(D_73, B_74) | ~r2_hidden(k4_tarski(D_73, E_75), k7_relat_1(A_76, B_74)) | ~v1_relat_1(k7_relat_1(A_76, B_74)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.71/1.43  tff(c_86, plain, (![C_77, B_78, A_79]: (r2_hidden(C_77, B_78) | ~v1_relat_1(k7_relat_1(A_79, B_78)) | ~v1_relat_1(A_79) | ~r2_hidden(C_77, k1_relat_1(k7_relat_1(A_79, B_78))))), inference(resolution, [status(thm)], [c_26, c_80])).
% 2.71/1.43  tff(c_554, plain, (![A_155, B_156, B_157]: (r2_hidden('#skF_1'(k1_relat_1(k7_relat_1(A_155, B_156)), B_157), B_156) | ~v1_relat_1(k7_relat_1(A_155, B_156)) | ~v1_relat_1(A_155) | r1_tarski(k1_relat_1(k7_relat_1(A_155, B_156)), B_157))), inference(resolution, [status(thm)], [c_6, c_86])).
% 2.71/1.43  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.71/1.43  tff(c_568, plain, (![A_158, B_159]: (~v1_relat_1(k7_relat_1(A_158, B_159)) | ~v1_relat_1(A_158) | r1_tarski(k1_relat_1(k7_relat_1(A_158, B_159)), B_159))), inference(resolution, [status(thm)], [c_554, c_4])).
% 2.71/1.43  tff(c_40, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_11', '#skF_10')), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.71/1.43  tff(c_582, plain, (~v1_relat_1(k7_relat_1('#skF_11', '#skF_10')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_568, c_40])).
% 2.71/1.43  tff(c_590, plain, (~v1_relat_1(k7_relat_1('#skF_11', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_582])).
% 2.71/1.43  tff(c_593, plain, (~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_38, c_590])).
% 2.71/1.43  tff(c_597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_593])).
% 2.71/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.43  
% 2.71/1.43  Inference rules
% 2.71/1.43  ----------------------
% 2.71/1.43  #Ref     : 0
% 2.71/1.43  #Sup     : 122
% 2.71/1.43  #Fact    : 0
% 2.71/1.43  #Define  : 0
% 2.71/1.43  #Split   : 0
% 2.71/1.43  #Chain   : 0
% 2.71/1.43  #Close   : 0
% 2.71/1.43  
% 2.71/1.43  Ordering : KBO
% 2.71/1.43  
% 2.71/1.43  Simplification rules
% 2.71/1.43  ----------------------
% 2.71/1.43  #Subsume      : 6
% 2.71/1.43  #Demod        : 4
% 2.71/1.43  #Tautology    : 15
% 2.71/1.43  #SimpNegUnit  : 0
% 2.71/1.43  #BackRed      : 0
% 2.71/1.43  
% 2.71/1.43  #Partial instantiations: 0
% 2.71/1.43  #Strategies tried      : 1
% 2.71/1.43  
% 2.71/1.43  Timing (in seconds)
% 2.71/1.43  ----------------------
% 3.03/1.43  Preprocessing        : 0.29
% 3.03/1.43  Parsing              : 0.15
% 3.03/1.43  CNF conversion       : 0.03
% 3.03/1.43  Main loop            : 0.37
% 3.03/1.43  Inferencing          : 0.15
% 3.03/1.43  Reduction            : 0.08
% 3.03/1.43  Demodulation         : 0.05
% 3.03/1.44  BG Simplification    : 0.02
% 3.03/1.44  Subsumption          : 0.09
% 3.03/1.44  Abstraction          : 0.02
% 3.03/1.44  MUC search           : 0.00
% 3.03/1.44  Cooper               : 0.00
% 3.03/1.44  Total                : 0.70
% 3.03/1.44  Index Insertion      : 0.00
% 3.03/1.44  Index Deletion       : 0.00
% 3.03/1.44  Index Matching       : 0.00
% 3.03/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
