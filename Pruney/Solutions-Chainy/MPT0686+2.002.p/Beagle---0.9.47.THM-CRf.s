%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:32 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  85 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
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

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,D_17,B_13] :
      ( r2_hidden(k1_funct_1(A_6,D_17),B_13)
      | ~ r2_hidden(D_17,k10_relat_1(A_6,B_13))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_77,plain,(
    ! [A_33,D_34,B_35] :
      ( r2_hidden(k1_funct_1(A_33,D_34),B_35)
      | ~ r2_hidden(D_34,k10_relat_1(A_33,B_35))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_35,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_xboole_0(A_24,B_25)
      | ~ r2_hidden(C_26,B_25)
      | ~ r2_hidden(C_26,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [C_26] :
      ( ~ r2_hidden(C_26,'#skF_6')
      | ~ r2_hidden(C_26,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_35])).

tff(c_88,plain,(
    ! [A_36,D_37] :
      ( ~ r2_hidden(k1_funct_1(A_36,D_37),'#skF_6')
      | ~ r2_hidden(D_37,k10_relat_1(A_36,'#skF_5'))
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_77,c_38])).

tff(c_94,plain,(
    ! [D_38,A_39] :
      ( ~ r2_hidden(D_38,k10_relat_1(A_39,'#skF_5'))
      | ~ r2_hidden(D_38,k10_relat_1(A_39,'#skF_6'))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_10,c_88])).

tff(c_123,plain,(
    ! [A_51,B_52] :
      ( ~ r2_hidden('#skF_1'(k10_relat_1(A_51,'#skF_5'),B_52),k10_relat_1(A_51,'#skF_6'))
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51)
      | r1_xboole_0(k10_relat_1(A_51,'#skF_5'),B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_133,plain,(
    ! [A_54] :
      ( ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54)
      | r1_xboole_0(k10_relat_1(A_54,'#skF_5'),k10_relat_1(A_54,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_4,c_123])).

tff(c_26,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_4','#skF_5'),k10_relat_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_138,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_26])).

tff(c_143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.23  
% 1.80/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.23  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.80/1.23  
% 1.80/1.23  %Foreground sorts:
% 1.80/1.23  
% 1.80/1.23  
% 1.80/1.23  %Background operators:
% 1.80/1.23  
% 1.80/1.23  
% 1.80/1.23  %Foreground operators:
% 1.80/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.80/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.80/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.80/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.80/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.80/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.80/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.23  
% 1.99/1.24  tff(f_67, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_funct_1)).
% 1.99/1.24  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.99/1.24  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 1.99/1.24  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.24  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.24  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.24  tff(c_10, plain, (![A_6, D_17, B_13]: (r2_hidden(k1_funct_1(A_6, D_17), B_13) | ~r2_hidden(D_17, k10_relat_1(A_6, B_13)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.24  tff(c_77, plain, (![A_33, D_34, B_35]: (r2_hidden(k1_funct_1(A_33, D_34), B_35) | ~r2_hidden(D_34, k10_relat_1(A_33, B_35)) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.24  tff(c_28, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.24  tff(c_35, plain, (![A_24, B_25, C_26]: (~r1_xboole_0(A_24, B_25) | ~r2_hidden(C_26, B_25) | ~r2_hidden(C_26, A_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.99/1.24  tff(c_38, plain, (![C_26]: (~r2_hidden(C_26, '#skF_6') | ~r2_hidden(C_26, '#skF_5'))), inference(resolution, [status(thm)], [c_28, c_35])).
% 1.99/1.24  tff(c_88, plain, (![A_36, D_37]: (~r2_hidden(k1_funct_1(A_36, D_37), '#skF_6') | ~r2_hidden(D_37, k10_relat_1(A_36, '#skF_5')) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_77, c_38])).
% 1.99/1.24  tff(c_94, plain, (![D_38, A_39]: (~r2_hidden(D_38, k10_relat_1(A_39, '#skF_5')) | ~r2_hidden(D_38, k10_relat_1(A_39, '#skF_6')) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_10, c_88])).
% 1.99/1.24  tff(c_123, plain, (![A_51, B_52]: (~r2_hidden('#skF_1'(k10_relat_1(A_51, '#skF_5'), B_52), k10_relat_1(A_51, '#skF_6')) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51) | r1_xboole_0(k10_relat_1(A_51, '#skF_5'), B_52))), inference(resolution, [status(thm)], [c_6, c_94])).
% 1.99/1.24  tff(c_133, plain, (![A_54]: (~v1_funct_1(A_54) | ~v1_relat_1(A_54) | r1_xboole_0(k10_relat_1(A_54, '#skF_5'), k10_relat_1(A_54, '#skF_6')))), inference(resolution, [status(thm)], [c_4, c_123])).
% 1.99/1.24  tff(c_26, plain, (~r1_xboole_0(k10_relat_1('#skF_4', '#skF_5'), k10_relat_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.99/1.24  tff(c_138, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_26])).
% 1.99/1.24  tff(c_143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_138])).
% 1.99/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  Inference rules
% 1.99/1.24  ----------------------
% 1.99/1.24  #Ref     : 0
% 1.99/1.24  #Sup     : 20
% 1.99/1.24  #Fact    : 0
% 1.99/1.24  #Define  : 0
% 1.99/1.24  #Split   : 0
% 1.99/1.24  #Chain   : 0
% 1.99/1.24  #Close   : 0
% 1.99/1.24  
% 1.99/1.24  Ordering : KBO
% 1.99/1.24  
% 1.99/1.24  Simplification rules
% 1.99/1.24  ----------------------
% 1.99/1.24  #Subsume      : 3
% 1.99/1.24  #Demod        : 3
% 1.99/1.24  #Tautology    : 2
% 1.99/1.24  #SimpNegUnit  : 0
% 1.99/1.24  #BackRed      : 0
% 1.99/1.24  
% 1.99/1.24  #Partial instantiations: 0
% 1.99/1.24  #Strategies tried      : 1
% 1.99/1.24  
% 1.99/1.24  Timing (in seconds)
% 1.99/1.24  ----------------------
% 1.99/1.25  Preprocessing        : 0.28
% 1.99/1.25  Parsing              : 0.14
% 1.99/1.25  CNF conversion       : 0.02
% 1.99/1.25  Main loop            : 0.16
% 1.99/1.25  Inferencing          : 0.07
% 1.99/1.25  Reduction            : 0.04
% 1.99/1.25  Demodulation         : 0.03
% 1.99/1.25  BG Simplification    : 0.01
% 1.99/1.25  Subsumption          : 0.04
% 1.99/1.25  Abstraction          : 0.01
% 1.99/1.25  MUC search           : 0.00
% 1.99/1.25  Cooper               : 0.00
% 1.99/1.25  Total                : 0.46
% 1.99/1.25  Index Insertion      : 0.00
% 1.99/1.25  Index Deletion       : 0.00
% 1.99/1.25  Index Matching       : 0.00
% 1.99/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
