%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:50 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  77 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_31,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_27,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_30,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_43,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_41])).

tff(c_2,plain,(
    ! [A_1] : k10_relat_1(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_54,plain,(
    ! [B_18,A_19] :
      ( k10_relat_1(B_18,k1_tarski(A_19)) != k1_xboole_0
      | ~ r2_hidden(A_19,k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_57,plain,(
    ! [A_19] :
      ( k10_relat_1(k1_xboole_0,k1_tarski(A_19)) != k1_xboole_0
      | ~ r2_hidden(A_19,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_54])).

tff(c_59,plain,(
    ! [A_19] : ~ r2_hidden(A_19,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_2,c_57])).

tff(c_44,plain,(
    ! [A_16] : v1_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_46,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_44])).

tff(c_6,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_72,plain,(
    ! [A_23,B_24] :
      ( r2_hidden('#skF_1'(A_23,B_24),k1_relat_1(B_24))
      | v5_funct_1(B_24,A_23)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_1'(A_23,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_23)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_72])).

tff(c_77,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_1'(A_23,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_46,c_75])).

tff(c_80,plain,(
    ! [A_27] :
      ( v5_funct_1(k1_xboole_0,A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_77])).

tff(c_24,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_83,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_24])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:14:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.13  %$ v5_funct_1 > r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.13  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.66/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.66/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.66/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.66/1.13  
% 1.66/1.14  tff(f_65, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 1.66/1.14  tff(f_31, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.66/1.14  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.66/1.14  tff(f_27, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.66/1.14  tff(f_30, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.66/1.14  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 1.66/1.14  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 1.66/1.14  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.66/1.14  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.66/1.14  tff(c_8, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.14  tff(c_41, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.66/1.14  tff(c_43, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_41])).
% 1.66/1.14  tff(c_2, plain, (![A_1]: (k10_relat_1(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.14  tff(c_4, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.66/1.14  tff(c_54, plain, (![B_18, A_19]: (k10_relat_1(B_18, k1_tarski(A_19))!=k1_xboole_0 | ~r2_hidden(A_19, k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.66/1.14  tff(c_57, plain, (![A_19]: (k10_relat_1(k1_xboole_0, k1_tarski(A_19))!=k1_xboole_0 | ~r2_hidden(A_19, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_54])).
% 1.66/1.14  tff(c_59, plain, (![A_19]: (~r2_hidden(A_19, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_2, c_57])).
% 1.66/1.14  tff(c_44, plain, (![A_16]: (v1_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.66/1.14  tff(c_46, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_44])).
% 1.66/1.14  tff(c_6, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.66/1.14  tff(c_72, plain, (![A_23, B_24]: (r2_hidden('#skF_1'(A_23, B_24), k1_relat_1(B_24)) | v5_funct_1(B_24, A_23) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.66/1.14  tff(c_75, plain, (![A_23]: (r2_hidden('#skF_1'(A_23, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_23) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_6, c_72])).
% 1.66/1.14  tff(c_77, plain, (![A_23]: (r2_hidden('#skF_1'(A_23, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_46, c_75])).
% 1.66/1.14  tff(c_80, plain, (![A_27]: (v5_funct_1(k1_xboole_0, A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(negUnitSimplification, [status(thm)], [c_59, c_77])).
% 1.66/1.14  tff(c_24, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.66/1.14  tff(c_83, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_80, c_24])).
% 1.66/1.14  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_83])).
% 1.66/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  Inference rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Ref     : 0
% 1.66/1.14  #Sup     : 15
% 1.66/1.14  #Fact    : 0
% 1.66/1.14  #Define  : 0
% 1.66/1.14  #Split   : 0
% 1.66/1.14  #Chain   : 0
% 1.66/1.14  #Close   : 0
% 1.66/1.14  
% 1.66/1.14  Ordering : KBO
% 1.66/1.14  
% 1.66/1.14  Simplification rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Subsume      : 0
% 1.66/1.14  #Demod        : 8
% 1.66/1.14  #Tautology    : 10
% 1.66/1.14  #SimpNegUnit  : 2
% 1.66/1.14  #BackRed      : 0
% 1.66/1.14  
% 1.66/1.14  #Partial instantiations: 0
% 1.66/1.14  #Strategies tried      : 1
% 1.66/1.14  
% 1.66/1.14  Timing (in seconds)
% 1.66/1.14  ----------------------
% 1.81/1.14  Preprocessing        : 0.27
% 1.81/1.14  Parsing              : 0.15
% 1.81/1.14  CNF conversion       : 0.02
% 1.81/1.14  Main loop            : 0.12
% 1.81/1.14  Inferencing          : 0.05
% 1.81/1.14  Reduction            : 0.03
% 1.81/1.15  Demodulation         : 0.02
% 1.81/1.15  BG Simplification    : 0.01
% 1.81/1.15  Subsumption          : 0.02
% 1.81/1.15  Abstraction          : 0.00
% 1.81/1.15  MUC search           : 0.00
% 1.81/1.15  Cooper               : 0.00
% 1.81/1.15  Total                : 0.41
% 1.81/1.15  Index Insertion      : 0.00
% 1.81/1.15  Index Deletion       : 0.00
% 1.81/1.15  Index Matching       : 0.00
% 1.81/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
