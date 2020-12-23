%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:31 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   40 (  79 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 262 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B)
          & v5_ordinal1(B) )
       => ! [C] :
            ( v3_ordinal1(C)
           => ( v1_relat_1(k7_relat_1(B,C))
              & v5_relat_1(k7_relat_1(B,C),A)
              & v1_funct_1(k7_relat_1(B,C))
              & v5_ordinal1(k7_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_ordinal1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v5_ordinal1(A)
        & v3_ordinal1(B) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v5_relat_1(k7_relat_1(A,B),k2_relat_1(A))
        & v5_ordinal1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_ordinal1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v5_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc22_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_funct_1(k7_relat_1(A_1,B_2))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    v5_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62,plain,(
    ! [A_24,B_25] :
      ( v5_ordinal1(k7_relat_1(A_24,B_25))
      | ~ v3_ordinal1(B_25)
      | ~ v5_ordinal1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_39,plain,(
    ! [C_17,A_18,B_19] :
      ( v5_relat_1(k7_relat_1(C_17,A_18),B_19)
      | ~ v5_relat_1(C_17,B_19)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_29,plain,(
    ! [C_13,A_14,B_15] :
      ( v1_relat_1(k7_relat_1(C_13,A_14))
      | ~ v5_relat_1(C_13,B_15)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_31,plain,(
    ! [A_14] :
      ( v1_relat_1(k7_relat_1('#skF_2',A_14))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_29])).

tff(c_34,plain,(
    ! [A_14] : v1_relat_1(k7_relat_1('#skF_2',A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_31])).

tff(c_16,plain,
    ( ~ v5_ordinal1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_37,plain,
    ( ~ v5_ordinal1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_38,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_42,plain,
    ( ~ v5_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_39,c_38])).

tff(c_48,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_42])).

tff(c_49,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3'))
    | ~ v5_ordinal1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_57,plain,(
    ~ v5_ordinal1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_65,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v5_ordinal1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_57])).

tff(c_69,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_20,c_18,c_65])).

tff(c_70,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_74,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_70])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:45:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  %$ v5_relat_1 > v5_ordinal1 > v3_ordinal1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.69/1.15  
% 1.69/1.15  %Foreground sorts:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Background operators:
% 1.69/1.15  
% 1.69/1.15  
% 1.69/1.15  %Foreground operators:
% 1.69/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.69/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.15  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.69/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.15  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.69/1.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.15  
% 1.87/1.16  tff(f_75, negated_conjecture, ~(![A, B]: ((((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) & v5_ordinal1(B)) => (![C]: (v3_ordinal1(C) => (((v1_relat_1(k7_relat_1(B, C)) & v5_relat_1(k7_relat_1(B, C), A)) & v1_funct_1(k7_relat_1(B, C))) & v5_ordinal1(k7_relat_1(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_ordinal1)).
% 1.87/1.16  tff(f_33, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 1.87/1.16  tff(f_55, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v5_ordinal1(A)) & v3_ordinal1(B)) => ((v1_relat_1(k7_relat_1(A, B)) & v5_relat_1(k7_relat_1(A, B), k2_relat_1(A))) & v5_ordinal1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_ordinal1)).
% 1.87/1.16  tff(f_41, axiom, (![A, B, C]: ((v1_relat_1(C) & v5_relat_1(C, B)) => (v1_relat_1(k7_relat_1(C, A)) & v5_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc22_relat_1)).
% 1.87/1.16  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.87/1.16  tff(c_22, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.87/1.16  tff(c_2, plain, (![A_1, B_2]: (v1_funct_1(k7_relat_1(A_1, B_2)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.16  tff(c_20, plain, (v5_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.87/1.16  tff(c_18, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.87/1.16  tff(c_62, plain, (![A_24, B_25]: (v5_ordinal1(k7_relat_1(A_24, B_25)) | ~v3_ordinal1(B_25) | ~v5_ordinal1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.16  tff(c_24, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.87/1.16  tff(c_39, plain, (![C_17, A_18, B_19]: (v5_relat_1(k7_relat_1(C_17, A_18), B_19) | ~v5_relat_1(C_17, B_19) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.16  tff(c_29, plain, (![C_13, A_14, B_15]: (v1_relat_1(k7_relat_1(C_13, A_14)) | ~v5_relat_1(C_13, B_15) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.16  tff(c_31, plain, (![A_14]: (v1_relat_1(k7_relat_1('#skF_2', A_14)) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_29])).
% 1.87/1.16  tff(c_34, plain, (![A_14]: (v1_relat_1(k7_relat_1('#skF_2', A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_31])).
% 1.87/1.16  tff(c_16, plain, (~v5_ordinal1(k7_relat_1('#skF_2', '#skF_3')) | ~v1_funct_1(k7_relat_1('#skF_2', '#skF_3')) | ~v5_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.87/1.16  tff(c_37, plain, (~v5_ordinal1(k7_relat_1('#skF_2', '#skF_3')) | ~v1_funct_1(k7_relat_1('#skF_2', '#skF_3')) | ~v5_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 1.87/1.16  tff(c_38, plain, (~v5_relat_1(k7_relat_1('#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_37])).
% 1.87/1.16  tff(c_42, plain, (~v5_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_39, c_38])).
% 1.87/1.16  tff(c_48, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_42])).
% 1.87/1.16  tff(c_49, plain, (~v1_funct_1(k7_relat_1('#skF_2', '#skF_3')) | ~v5_ordinal1(k7_relat_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_37])).
% 1.87/1.16  tff(c_57, plain, (~v5_ordinal1(k7_relat_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_49])).
% 1.87/1.16  tff(c_65, plain, (~v3_ordinal1('#skF_3') | ~v5_ordinal1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_57])).
% 1.87/1.16  tff(c_69, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_20, c_18, c_65])).
% 1.87/1.16  tff(c_70, plain, (~v1_funct_1(k7_relat_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_49])).
% 1.87/1.16  tff(c_74, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_70])).
% 1.87/1.16  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_74])).
% 1.87/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.16  
% 1.87/1.16  Inference rules
% 1.87/1.16  ----------------------
% 1.87/1.16  #Ref     : 0
% 1.87/1.16  #Sup     : 7
% 1.87/1.16  #Fact    : 0
% 1.87/1.16  #Define  : 0
% 1.87/1.16  #Split   : 2
% 1.87/1.16  #Chain   : 0
% 1.87/1.16  #Close   : 0
% 1.87/1.16  
% 1.87/1.16  Ordering : KBO
% 1.87/1.16  
% 1.87/1.16  Simplification rules
% 1.87/1.16  ----------------------
% 1.87/1.16  #Subsume      : 1
% 1.87/1.16  #Demod        : 11
% 1.87/1.16  #Tautology    : 0
% 1.87/1.16  #SimpNegUnit  : 0
% 1.87/1.16  #BackRed      : 0
% 1.87/1.16  
% 1.87/1.16  #Partial instantiations: 0
% 1.87/1.16  #Strategies tried      : 1
% 1.87/1.16  
% 1.87/1.16  Timing (in seconds)
% 1.87/1.16  ----------------------
% 1.87/1.16  Preprocessing        : 0.28
% 1.87/1.17  Parsing              : 0.15
% 1.87/1.17  CNF conversion       : 0.02
% 1.87/1.17  Main loop            : 0.13
% 1.87/1.17  Inferencing          : 0.05
% 1.87/1.17  Reduction            : 0.03
% 1.87/1.17  Demodulation         : 0.03
% 1.87/1.17  BG Simplification    : 0.01
% 1.87/1.17  Subsumption          : 0.02
% 1.87/1.17  Abstraction          : 0.00
% 1.87/1.17  MUC search           : 0.00
% 1.87/1.17  Cooper               : 0.00
% 1.87/1.17  Total                : 0.44
% 1.87/1.17  Index Insertion      : 0.00
% 1.87/1.17  Index Deletion       : 0.00
% 1.87/1.17  Index Matching       : 0.00
% 1.87/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
