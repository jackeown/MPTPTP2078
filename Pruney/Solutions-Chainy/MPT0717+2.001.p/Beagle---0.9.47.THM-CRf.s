%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:40 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  79 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B) )
       => ! [C] :
            ( r2_hidden(C,k1_relat_1(B))
           => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_40,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    ! [A_43,D_44,B_45] :
      ( r2_hidden(k1_funct_1(A_43,D_44),B_45)
      | ~ r2_hidden(D_44,k10_relat_1(A_43,B_45))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_154,plain,(
    ! [A_58,D_59,B_60,B_61] :
      ( r2_hidden(k1_funct_1(A_58,D_59),B_60)
      | ~ r1_tarski(B_61,B_60)
      | ~ r2_hidden(D_59,k10_relat_1(A_58,B_61))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_249,plain,(
    ! [A_90,D_91,A_92,B_93] :
      ( r2_hidden(k1_funct_1(A_90,D_91),A_92)
      | ~ r2_hidden(D_91,k10_relat_1(A_90,k2_relat_1(B_93)))
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90)
      | ~ v5_relat_1(B_93,A_92)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_347,plain,(
    ! [A_104,D_105,A_106] :
      ( r2_hidden(k1_funct_1(A_104,D_105),A_106)
      | ~ r2_hidden(D_105,k1_relat_1(A_104))
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104)
      | ~ v5_relat_1(A_104,A_106)
      | ~ v1_relat_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_249])).

tff(c_32,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_362,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_347,c_32])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:24:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.32  
% 2.42/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.33  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.42/1.33  
% 2.42/1.33  %Foreground sorts:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Background operators:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Foreground operators:
% 2.42/1.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.42/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.42/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.42/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.42/1.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.42/1.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.33  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.42/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.42/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.33  
% 2.42/1.34  tff(f_68, negated_conjecture, ~(![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.42/1.34  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.42/1.34  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.42/1.34  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 2.42/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.42/1.34  tff(c_40, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.42/1.34  tff(c_38, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.42/1.34  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.42/1.34  tff(c_34, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.42/1.34  tff(c_12, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.42/1.34  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.42/1.34  tff(c_107, plain, (![A_43, D_44, B_45]: (r2_hidden(k1_funct_1(A_43, D_44), B_45) | ~r2_hidden(D_44, k10_relat_1(A_43, B_45)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.42/1.34  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.42/1.34  tff(c_154, plain, (![A_58, D_59, B_60, B_61]: (r2_hidden(k1_funct_1(A_58, D_59), B_60) | ~r1_tarski(B_61, B_60) | ~r2_hidden(D_59, k10_relat_1(A_58, B_61)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_107, c_2])).
% 2.42/1.34  tff(c_249, plain, (![A_90, D_91, A_92, B_93]: (r2_hidden(k1_funct_1(A_90, D_91), A_92) | ~r2_hidden(D_91, k10_relat_1(A_90, k2_relat_1(B_93))) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90) | ~v5_relat_1(B_93, A_92) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_10, c_154])).
% 2.42/1.34  tff(c_347, plain, (![A_104, D_105, A_106]: (r2_hidden(k1_funct_1(A_104, D_105), A_106) | ~r2_hidden(D_105, k1_relat_1(A_104)) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104) | ~v5_relat_1(A_104, A_106) | ~v1_relat_1(A_104) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_12, c_249])).
% 2.42/1.34  tff(c_32, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.42/1.34  tff(c_362, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_347, c_32])).
% 2.42/1.34  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_362])).
% 2.42/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  Inference rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Ref     : 0
% 2.42/1.34  #Sup     : 77
% 2.42/1.34  #Fact    : 0
% 2.42/1.34  #Define  : 0
% 2.42/1.34  #Split   : 0
% 2.42/1.34  #Chain   : 0
% 2.42/1.34  #Close   : 0
% 2.42/1.34  
% 2.42/1.34  Ordering : KBO
% 2.42/1.34  
% 2.42/1.34  Simplification rules
% 2.42/1.34  ----------------------
% 2.42/1.34  #Subsume      : 8
% 2.42/1.34  #Demod        : 9
% 2.42/1.34  #Tautology    : 9
% 2.42/1.34  #SimpNegUnit  : 0
% 2.42/1.34  #BackRed      : 0
% 2.42/1.34  
% 2.42/1.34  #Partial instantiations: 0
% 2.42/1.34  #Strategies tried      : 1
% 2.42/1.34  
% 2.42/1.34  Timing (in seconds)
% 2.42/1.34  ----------------------
% 2.42/1.34  Preprocessing        : 0.29
% 2.42/1.34  Parsing              : 0.15
% 2.42/1.34  CNF conversion       : 0.02
% 2.42/1.34  Main loop            : 0.29
% 2.42/1.34  Inferencing          : 0.11
% 2.42/1.34  Reduction            : 0.07
% 2.42/1.34  Demodulation         : 0.05
% 2.42/1.34  BG Simplification    : 0.02
% 2.42/1.34  Subsumption          : 0.07
% 2.42/1.34  Abstraction          : 0.01
% 2.42/1.34  MUC search           : 0.00
% 2.42/1.34  Cooper               : 0.00
% 2.42/1.34  Total                : 0.60
% 2.42/1.34  Index Insertion      : 0.00
% 2.42/1.34  Index Deletion       : 0.00
% 2.42/1.34  Index Matching       : 0.00
% 2.42/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
