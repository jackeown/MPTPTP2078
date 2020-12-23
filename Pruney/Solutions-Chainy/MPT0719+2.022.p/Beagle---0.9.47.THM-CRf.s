%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:46 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   45 (  55 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   63 (  80 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_34,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_37,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_57,axiom,(
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

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_46,plain,(
    ! [A_18] :
      ( v1_relat_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_46])).

tff(c_8,plain,(
    ! [A_3] : k10_relat_1(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [B_21,A_22] :
      ( k10_relat_1(B_21,k1_tarski(A_22)) != k1_xboole_0
      | ~ r2_hidden(A_22,k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_68,plain,(
    ! [A_22] :
      ( k10_relat_1(k1_xboole_0,k1_tarski(A_22)) != k1_xboole_0
      | ~ r2_hidden(A_22,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_65])).

tff(c_70,plain,(
    ! [A_22] : ~ r2_hidden(A_22,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8,c_68])).

tff(c_51,plain,(
    ! [A_19] :
      ( v1_funct_1(A_19)
      | ~ v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_51])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),k1_relat_1(B_27))
      | v5_funct_1(B_27,A_26)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_86,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_26)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_83])).

tff(c_88,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_55,c_86])).

tff(c_90,plain,(
    ! [A_28] :
      ( v5_funct_1(k1_xboole_0,A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_88])).

tff(c_26,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_26])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:43:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.16  
% 1.78/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.16  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.78/1.16  
% 1.78/1.16  %Foreground sorts:
% 1.78/1.16  
% 1.78/1.16  
% 1.78/1.16  %Background operators:
% 1.78/1.16  
% 1.78/1.16  
% 1.78/1.16  %Foreground operators:
% 1.78/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.16  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.78/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.78/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.78/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.78/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.78/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.78/1.16  
% 1.85/1.18  tff(f_71, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 1.85/1.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.85/1.18  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.85/1.18  tff(f_34, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.85/1.18  tff(f_37, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.85/1.18  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 1.85/1.18  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.85/1.18  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 1.85/1.18  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.85/1.18  tff(c_28, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.85/1.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.85/1.18  tff(c_46, plain, (![A_18]: (v1_relat_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.18  tff(c_50, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_46])).
% 1.85/1.18  tff(c_8, plain, (![A_3]: (k10_relat_1(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.18  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.85/1.18  tff(c_65, plain, (![B_21, A_22]: (k10_relat_1(B_21, k1_tarski(A_22))!=k1_xboole_0 | ~r2_hidden(A_22, k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.85/1.18  tff(c_68, plain, (![A_22]: (k10_relat_1(k1_xboole_0, k1_tarski(A_22))!=k1_xboole_0 | ~r2_hidden(A_22, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_65])).
% 1.85/1.18  tff(c_70, plain, (![A_22]: (~r2_hidden(A_22, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8, c_68])).
% 1.85/1.18  tff(c_51, plain, (![A_19]: (v1_funct_1(A_19) | ~v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.18  tff(c_55, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_51])).
% 1.85/1.18  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.85/1.18  tff(c_83, plain, (![A_26, B_27]: (r2_hidden('#skF_1'(A_26, B_27), k1_relat_1(B_27)) | v5_funct_1(B_27, A_26) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.85/1.18  tff(c_86, plain, (![A_26]: (r2_hidden('#skF_1'(A_26, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_26) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(superposition, [status(thm), theory('equality')], [c_12, c_83])).
% 1.85/1.18  tff(c_88, plain, (![A_26]: (r2_hidden('#skF_1'(A_26, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_55, c_86])).
% 1.85/1.18  tff(c_90, plain, (![A_28]: (v5_funct_1(k1_xboole_0, A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(negUnitSimplification, [status(thm)], [c_70, c_88])).
% 1.85/1.18  tff(c_26, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.85/1.18  tff(c_93, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_90, c_26])).
% 1.85/1.18  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_93])).
% 1.85/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.18  
% 1.85/1.18  Inference rules
% 1.85/1.18  ----------------------
% 1.85/1.18  #Ref     : 0
% 1.85/1.18  #Sup     : 15
% 1.85/1.18  #Fact    : 0
% 1.85/1.18  #Define  : 0
% 1.85/1.18  #Split   : 0
% 1.85/1.18  #Chain   : 0
% 1.85/1.18  #Close   : 0
% 1.85/1.18  
% 1.85/1.18  Ordering : KBO
% 1.85/1.18  
% 1.85/1.18  Simplification rules
% 1.85/1.18  ----------------------
% 1.85/1.18  #Subsume      : 0
% 1.85/1.18  #Demod        : 8
% 1.85/1.18  #Tautology    : 10
% 1.85/1.18  #SimpNegUnit  : 2
% 1.85/1.18  #BackRed      : 0
% 1.85/1.18  
% 1.85/1.18  #Partial instantiations: 0
% 1.85/1.18  #Strategies tried      : 1
% 1.85/1.18  
% 1.85/1.18  Timing (in seconds)
% 1.85/1.18  ----------------------
% 1.85/1.18  Preprocessing        : 0.29
% 1.85/1.18  Parsing              : 0.15
% 1.85/1.18  CNF conversion       : 0.02
% 1.85/1.18  Main loop            : 0.11
% 1.85/1.18  Inferencing          : 0.05
% 1.85/1.18  Reduction            : 0.03
% 1.85/1.18  Demodulation         : 0.03
% 1.85/1.18  BG Simplification    : 0.01
% 1.85/1.18  Subsumption          : 0.02
% 1.85/1.18  Abstraction          : 0.01
% 1.85/1.18  MUC search           : 0.00
% 1.85/1.18  Cooper               : 0.00
% 1.85/1.18  Total                : 0.43
% 1.85/1.18  Index Insertion      : 0.00
% 1.85/1.18  Index Deletion       : 0.00
% 1.85/1.18  Index Matching       : 0.00
% 1.85/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
