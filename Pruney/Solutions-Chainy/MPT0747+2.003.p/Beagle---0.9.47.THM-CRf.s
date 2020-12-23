%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:23 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   48 (  64 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  98 expanded)
%              Number of equality atoms :    2 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A] :
      ( ! [B] :
          ( r2_hidden(B,A)
         => v3_ordinal1(B) )
     => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ~ ! [B] :
            ( r2_hidden(B,A)
          <=> v3_ordinal1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

tff(f_52,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_68,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_6'(A_45),A_45)
      | v3_ordinal1(k3_tarski(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [B_33] :
      ( v3_ordinal1(B_33)
      | ~ r2_hidden(B_33,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_77,plain,
    ( v3_ordinal1('#skF_6'('#skF_7'))
    | v3_ordinal1(k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_68,c_40])).

tff(c_78,plain,(
    v3_ordinal1(k3_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_32,plain,(
    ! [A_27] :
      ( v3_ordinal1(k1_ordinal1(A_27))
      | ~ v3_ordinal1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [B_26] : r2_hidden(B_26,k1_ordinal1(B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42,plain,(
    ! [B_33] :
      ( r2_hidden(B_33,'#skF_7')
      | ~ v3_ordinal1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_339,plain,(
    ! [C_79,A_80,D_81] :
      ( r2_hidden(C_79,k3_tarski(A_80))
      | ~ r2_hidden(D_81,A_80)
      | ~ r2_hidden(C_79,D_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_444,plain,(
    ! [C_87,B_88] :
      ( r2_hidden(C_87,k3_tarski('#skF_7'))
      | ~ r2_hidden(C_87,B_88)
      | ~ v3_ordinal1(B_88) ) ),
    inference(resolution,[status(thm)],[c_42,c_339])).

tff(c_469,plain,(
    ! [B_89] :
      ( r2_hidden(B_89,k3_tarski('#skF_7'))
      | ~ v3_ordinal1(k1_ordinal1(B_89)) ) ),
    inference(resolution,[status(thm)],[c_28,c_444])).

tff(c_92,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51,B_52),A_51)
      | r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    ! [A_53] : r1_tarski(A_53,A_53) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_63,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden(A_43,B_44)
      | r2_hidden(A_43,k1_ordinal1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    ! [B_31,A_30] :
      ( ~ r1_tarski(B_31,A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_67,plain,(
    ! [B_44,A_43] :
      ( ~ r1_tarski(k1_ordinal1(B_44),A_43)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_63,c_38])).

tff(c_116,plain,(
    ! [B_44] : ~ r2_hidden(k1_ordinal1(B_44),B_44) ),
    inference(resolution,[status(thm)],[c_107,c_67])).

tff(c_522,plain,(
    ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski('#skF_7')))) ),
    inference(resolution,[status(thm)],[c_469,c_116])).

tff(c_528,plain,(
    ~ v3_ordinal1(k1_ordinal1(k3_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_32,c_522])).

tff(c_531,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_32,c_528])).

tff(c_535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_531])).

tff(c_536,plain,(
    v3_ordinal1('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_34,plain,(
    ! [A_28] :
      ( ~ v3_ordinal1('#skF_6'(A_28))
      | v3_ordinal1(k3_tarski(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_537,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_540,plain,(
    ~ v3_ordinal1('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_537])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  %$ r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > k3_tarski > k1_ordinal1 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_1 > #skF_6 > #skF_4
% 2.09/1.30  
% 2.09/1.30  %Foreground sorts:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Background operators:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Foreground operators:
% 2.09/1.30  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.09/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.09/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.09/1.30  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.30  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.09/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.09/1.31  
% 2.09/1.32  tff(f_59, axiom, (![A]: ((![B]: (r2_hidden(B, A) => v3_ordinal1(B))) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_ordinal1)).
% 2.09/1.32  tff(f_71, negated_conjecture, ~(![A]: ~(![B]: (r2_hidden(B, A) <=> v3_ordinal1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_ordinal1)).
% 2.09/1.32  tff(f_52, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 2.09/1.32  tff(f_48, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 2.09/1.32  tff(f_42, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.09/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.09/1.32  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.09/1.32  tff(c_68, plain, (![A_45]: (r2_hidden('#skF_6'(A_45), A_45) | v3_ordinal1(k3_tarski(A_45)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.32  tff(c_40, plain, (![B_33]: (v3_ordinal1(B_33) | ~r2_hidden(B_33, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.09/1.32  tff(c_77, plain, (v3_ordinal1('#skF_6'('#skF_7')) | v3_ordinal1(k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_40])).
% 2.09/1.32  tff(c_78, plain, (v3_ordinal1(k3_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_77])).
% 2.09/1.32  tff(c_32, plain, (![A_27]: (v3_ordinal1(k1_ordinal1(A_27)) | ~v3_ordinal1(A_27))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.09/1.32  tff(c_28, plain, (![B_26]: (r2_hidden(B_26, k1_ordinal1(B_26)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.32  tff(c_42, plain, (![B_33]: (r2_hidden(B_33, '#skF_7') | ~v3_ordinal1(B_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.09/1.32  tff(c_339, plain, (![C_79, A_80, D_81]: (r2_hidden(C_79, k3_tarski(A_80)) | ~r2_hidden(D_81, A_80) | ~r2_hidden(C_79, D_81))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.09/1.32  tff(c_444, plain, (![C_87, B_88]: (r2_hidden(C_87, k3_tarski('#skF_7')) | ~r2_hidden(C_87, B_88) | ~v3_ordinal1(B_88))), inference(resolution, [status(thm)], [c_42, c_339])).
% 2.09/1.32  tff(c_469, plain, (![B_89]: (r2_hidden(B_89, k3_tarski('#skF_7')) | ~v3_ordinal1(k1_ordinal1(B_89)))), inference(resolution, [status(thm)], [c_28, c_444])).
% 2.09/1.32  tff(c_92, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51, B_52), A_51) | r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.32  tff(c_107, plain, (![A_53]: (r1_tarski(A_53, A_53))), inference(resolution, [status(thm)], [c_92, c_4])).
% 2.09/1.32  tff(c_63, plain, (![A_43, B_44]: (~r2_hidden(A_43, B_44) | r2_hidden(A_43, k1_ordinal1(B_44)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.32  tff(c_38, plain, (![B_31, A_30]: (~r1_tarski(B_31, A_30) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.32  tff(c_67, plain, (![B_44, A_43]: (~r1_tarski(k1_ordinal1(B_44), A_43) | ~r2_hidden(A_43, B_44))), inference(resolution, [status(thm)], [c_63, c_38])).
% 2.09/1.32  tff(c_116, plain, (![B_44]: (~r2_hidden(k1_ordinal1(B_44), B_44))), inference(resolution, [status(thm)], [c_107, c_67])).
% 2.09/1.32  tff(c_522, plain, (~v3_ordinal1(k1_ordinal1(k1_ordinal1(k3_tarski('#skF_7'))))), inference(resolution, [status(thm)], [c_469, c_116])).
% 2.09/1.32  tff(c_528, plain, (~v3_ordinal1(k1_ordinal1(k3_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_32, c_522])).
% 2.09/1.32  tff(c_531, plain, (~v3_ordinal1(k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_32, c_528])).
% 2.09/1.32  tff(c_535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_531])).
% 2.09/1.32  tff(c_536, plain, (v3_ordinal1('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_77])).
% 2.09/1.32  tff(c_34, plain, (![A_28]: (~v3_ordinal1('#skF_6'(A_28)) | v3_ordinal1(k3_tarski(A_28)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.32  tff(c_537, plain, (~v3_ordinal1(k3_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_77])).
% 2.09/1.32  tff(c_540, plain, (~v3_ordinal1('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_34, c_537])).
% 2.09/1.32  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_536, c_540])).
% 2.09/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.32  
% 2.09/1.32  Inference rules
% 2.09/1.32  ----------------------
% 2.09/1.32  #Ref     : 0
% 2.09/1.32  #Sup     : 106
% 2.09/1.32  #Fact    : 0
% 2.09/1.32  #Define  : 0
% 2.09/1.32  #Split   : 1
% 2.09/1.32  #Chain   : 0
% 2.09/1.32  #Close   : 0
% 2.09/1.32  
% 2.09/1.32  Ordering : KBO
% 2.09/1.32  
% 2.09/1.32  Simplification rules
% 2.09/1.32  ----------------------
% 2.09/1.32  #Subsume      : 14
% 2.09/1.32  #Demod        : 6
% 2.09/1.32  #Tautology    : 6
% 2.09/1.32  #SimpNegUnit  : 0
% 2.09/1.32  #BackRed      : 0
% 2.09/1.32  
% 2.09/1.32  #Partial instantiations: 0
% 2.09/1.32  #Strategies tried      : 1
% 2.09/1.32  
% 2.09/1.32  Timing (in seconds)
% 2.09/1.32  ----------------------
% 2.09/1.32  Preprocessing        : 0.27
% 2.09/1.32  Parsing              : 0.14
% 2.09/1.32  CNF conversion       : 0.02
% 2.09/1.32  Main loop            : 0.27
% 2.09/1.32  Inferencing          : 0.10
% 2.09/1.32  Reduction            : 0.07
% 2.09/1.32  Demodulation         : 0.05
% 2.09/1.32  BG Simplification    : 0.02
% 2.09/1.32  Subsumption          : 0.06
% 2.09/1.32  Abstraction          : 0.01
% 2.09/1.32  MUC search           : 0.00
% 2.09/1.32  Cooper               : 0.00
% 2.09/1.32  Total                : 0.57
% 2.09/1.32  Index Insertion      : 0.00
% 2.09/1.32  Index Deletion       : 0.00
% 2.09/1.32  Index Matching       : 0.00
% 2.09/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
