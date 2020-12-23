%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:20 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   40 (  90 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 247 expanded)
%              Number of equality atoms :    7 (  34 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
         => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( B = k8_relat_1(A,C)
          <=> ( ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                <=> ( r2_hidden(D,k1_relat_1(C))
                    & r2_hidden(k1_funct_1(C,D),A) ) )
              & ! [D] :
                  ( r2_hidden(D,k1_relat_1(B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

tff(c_38,plain,(
    k1_funct_1(k8_relat_1('#skF_5','#skF_6'),'#skF_4') != k1_funct_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    r2_hidden('#skF_4',k1_relat_1(k8_relat_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_47,plain,(
    ! [D_25,C_26,A_27] :
      ( r2_hidden(D_25,k1_relat_1(C_26))
      | ~ r2_hidden(D_25,k1_relat_1(k8_relat_1(A_27,C_26)))
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26)
      | ~ v1_funct_1(k8_relat_1(A_27,C_26))
      | ~ v1_relat_1(k8_relat_1(A_27,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_47])).

tff(c_53,plain,
    ( r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_50])).

tff(c_54,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_57,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_54])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_57])).

tff(c_63,plain,(
    v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_funct_1(k8_relat_1(A_1,B_2))
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_64,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_67,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_67])).

tff(c_73,plain,(
    v1_funct_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_81,plain,(
    ! [A_31,C_32,D_33] :
      ( k1_funct_1(k8_relat_1(A_31,C_32),D_33) = k1_funct_1(C_32,D_33)
      | ~ r2_hidden(D_33,k1_relat_1(k8_relat_1(A_31,C_32)))
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32)
      | ~ v1_funct_1(k8_relat_1(A_31,C_32))
      | ~ v1_relat_1(k8_relat_1(A_31,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_84,plain,
    ( k1_funct_1(k8_relat_1('#skF_5','#skF_6'),'#skF_4') = k1_funct_1('#skF_6','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1(k8_relat_1('#skF_5','#skF_6'))
    | ~ v1_relat_1(k8_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_87,plain,(
    k1_funct_1(k8_relat_1('#skF_5','#skF_6'),'#skF_4') = k1_funct_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_73,c_44,c_42,c_84])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:41:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.18  
% 1.99/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.18  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.99/1.18  
% 1.99/1.18  %Foreground sorts:
% 1.99/1.18  
% 1.99/1.18  
% 1.99/1.18  %Background operators:
% 1.99/1.18  
% 1.99/1.18  
% 1.99/1.18  %Foreground operators:
% 1.99/1.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.99/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.99/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.99/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.18  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.99/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.99/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.18  
% 1.99/1.19  tff(f_65, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 1.99/1.19  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_funct_1)).
% 1.99/1.19  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((B = k8_relat_1(A, C)) <=> ((![D]: (r2_hidden(D, k1_relat_1(B)) <=> (r2_hidden(D, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, D), A)))) & (![D]: (r2_hidden(D, k1_relat_1(B)) => (k1_funct_1(B, D) = k1_funct_1(C, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_funct_1)).
% 1.99/1.19  tff(c_38, plain, (k1_funct_1(k8_relat_1('#skF_5', '#skF_6'), '#skF_4')!=k1_funct_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.19  tff(c_44, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.19  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.19  tff(c_4, plain, (![A_1, B_2]: (v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.19  tff(c_40, plain, (r2_hidden('#skF_4', k1_relat_1(k8_relat_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.19  tff(c_47, plain, (![D_25, C_26, A_27]: (r2_hidden(D_25, k1_relat_1(C_26)) | ~r2_hidden(D_25, k1_relat_1(k8_relat_1(A_27, C_26))) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26) | ~v1_funct_1(k8_relat_1(A_27, C_26)) | ~v1_relat_1(k8_relat_1(A_27, C_26)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.19  tff(c_50, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_47])).
% 1.99/1.19  tff(c_53, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_50])).
% 1.99/1.19  tff(c_54, plain, (~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_53])).
% 1.99/1.19  tff(c_57, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_54])).
% 1.99/1.19  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_57])).
% 1.99/1.19  tff(c_63, plain, (v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_53])).
% 1.99/1.19  tff(c_2, plain, (![A_1, B_2]: (v1_funct_1(k8_relat_1(A_1, B_2)) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.19  tff(c_62, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_53])).
% 1.99/1.19  tff(c_64, plain, (~v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_62])).
% 1.99/1.19  tff(c_67, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_64])).
% 1.99/1.19  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_67])).
% 1.99/1.19  tff(c_73, plain, (v1_funct_1(k8_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_62])).
% 1.99/1.19  tff(c_81, plain, (![A_31, C_32, D_33]: (k1_funct_1(k8_relat_1(A_31, C_32), D_33)=k1_funct_1(C_32, D_33) | ~r2_hidden(D_33, k1_relat_1(k8_relat_1(A_31, C_32))) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32) | ~v1_funct_1(k8_relat_1(A_31, C_32)) | ~v1_relat_1(k8_relat_1(A_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.19  tff(c_84, plain, (k1_funct_1(k8_relat_1('#skF_5', '#skF_6'), '#skF_4')=k1_funct_1('#skF_6', '#skF_4') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1(k8_relat_1('#skF_5', '#skF_6')) | ~v1_relat_1(k8_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_81])).
% 1.99/1.19  tff(c_87, plain, (k1_funct_1(k8_relat_1('#skF_5', '#skF_6'), '#skF_4')=k1_funct_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_73, c_44, c_42, c_84])).
% 1.99/1.19  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_87])).
% 1.99/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.19  
% 1.99/1.19  Inference rules
% 1.99/1.19  ----------------------
% 1.99/1.19  #Ref     : 0
% 1.99/1.19  #Sup     : 5
% 1.99/1.19  #Fact    : 0
% 1.99/1.19  #Define  : 0
% 1.99/1.19  #Split   : 2
% 1.99/1.19  #Chain   : 0
% 1.99/1.19  #Close   : 0
% 1.99/1.19  
% 1.99/1.19  Ordering : KBO
% 1.99/1.19  
% 1.99/1.19  Simplification rules
% 1.99/1.19  ----------------------
% 1.99/1.19  #Subsume      : 0
% 1.99/1.19  #Demod        : 14
% 1.99/1.19  #Tautology    : 0
% 1.99/1.19  #SimpNegUnit  : 1
% 1.99/1.19  #BackRed      : 0
% 1.99/1.19  
% 1.99/1.19  #Partial instantiations: 0
% 1.99/1.19  #Strategies tried      : 1
% 1.99/1.19  
% 1.99/1.19  Timing (in seconds)
% 1.99/1.19  ----------------------
% 1.99/1.20  Preprocessing        : 0.30
% 1.99/1.20  Parsing              : 0.15
% 1.99/1.20  CNF conversion       : 0.03
% 1.99/1.20  Main loop            : 0.14
% 1.99/1.20  Inferencing          : 0.04
% 1.99/1.20  Reduction            : 0.04
% 1.99/1.20  Demodulation         : 0.03
% 1.99/1.20  BG Simplification    : 0.02
% 1.99/1.20  Subsumption          : 0.04
% 1.99/1.20  Abstraction          : 0.01
% 1.99/1.20  MUC search           : 0.00
% 1.99/1.20  Cooper               : 0.00
% 1.99/1.20  Total                : 0.46
% 1.99/1.20  Index Insertion      : 0.00
% 1.99/1.20  Index Deletion       : 0.00
% 1.99/1.20  Index Matching       : 0.00
% 1.99/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
