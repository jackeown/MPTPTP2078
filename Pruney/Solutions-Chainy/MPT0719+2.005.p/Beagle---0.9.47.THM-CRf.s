%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:43 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   39 (  45 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  68 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_39,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_18] :
      ( v1_relat_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_40])).

tff(c_35,plain,(
    ! [A_17] :
      ( v1_funct_1(A_17)
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_39,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_2'(A_22,B_23),k1_relat_1(B_23))
      | v5_funct_1(B_23,A_22)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_57,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_2'(A_22,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_22)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_61,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_2'(A_24,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_39,c_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_68,plain,(
    ! [A_25] :
      ( v5_funct_1(k1_xboole_0,A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_64])).

tff(c_22,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_71,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_22])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:49:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.88/1.21  
% 1.88/1.21  %Foreground sorts:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Background operators:
% 1.88/1.21  
% 1.88/1.21  
% 1.88/1.21  %Foreground operators:
% 1.88/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.21  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.88/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.21  
% 1.88/1.23  tff(f_66, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.88/1.23  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.88/1.23  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.88/1.23  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.88/1.23  tff(f_39, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.88/1.23  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.88/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.88/1.23  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.23  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.23  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.23  tff(c_40, plain, (![A_18]: (v1_relat_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.88/1.23  tff(c_44, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_40])).
% 1.88/1.23  tff(c_35, plain, (![A_17]: (v1_funct_1(A_17) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.88/1.23  tff(c_39, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_35])).
% 1.88/1.23  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.88/1.23  tff(c_51, plain, (![A_22, B_23]: (r2_hidden('#skF_2'(A_22, B_23), k1_relat_1(B_23)) | v5_funct_1(B_23, A_22) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.88/1.23  tff(c_57, plain, (![A_22]: (r2_hidden('#skF_2'(A_22, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_22) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_12, c_51])).
% 1.88/1.23  tff(c_61, plain, (![A_24]: (r2_hidden('#skF_2'(A_24, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_39, c_57])).
% 1.88/1.23  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.23  tff(c_64, plain, (![A_24]: (~v1_xboole_0(k1_xboole_0) | v5_funct_1(k1_xboole_0, A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(resolution, [status(thm)], [c_61, c_2])).
% 1.88/1.23  tff(c_68, plain, (![A_25]: (v5_funct_1(k1_xboole_0, A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_64])).
% 1.88/1.23  tff(c_22, plain, (~v5_funct_1(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.88/1.23  tff(c_71, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_22])).
% 1.88/1.23  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_71])).
% 1.88/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.23  
% 1.88/1.23  Inference rules
% 1.88/1.23  ----------------------
% 1.88/1.23  #Ref     : 0
% 1.88/1.23  #Sup     : 11
% 1.88/1.23  #Fact    : 0
% 1.88/1.23  #Define  : 0
% 1.88/1.23  #Split   : 0
% 1.88/1.23  #Chain   : 0
% 1.88/1.23  #Close   : 0
% 1.88/1.23  
% 1.88/1.23  Ordering : KBO
% 1.88/1.23  
% 1.88/1.23  Simplification rules
% 1.88/1.23  ----------------------
% 1.88/1.23  #Subsume      : 1
% 1.88/1.23  #Demod        : 5
% 1.88/1.23  #Tautology    : 5
% 1.88/1.23  #SimpNegUnit  : 0
% 1.88/1.23  #BackRed      : 0
% 1.88/1.23  
% 1.88/1.23  #Partial instantiations: 0
% 1.88/1.23  #Strategies tried      : 1
% 1.88/1.23  
% 1.88/1.23  Timing (in seconds)
% 1.88/1.23  ----------------------
% 2.02/1.23  Preprocessing        : 0.31
% 2.02/1.23  Parsing              : 0.18
% 2.02/1.23  CNF conversion       : 0.02
% 2.02/1.23  Main loop            : 0.13
% 2.02/1.23  Inferencing          : 0.06
% 2.02/1.23  Reduction            : 0.04
% 2.02/1.23  Demodulation         : 0.03
% 2.02/1.23  BG Simplification    : 0.01
% 2.02/1.23  Subsumption          : 0.02
% 2.02/1.23  Abstraction          : 0.00
% 2.02/1.23  MUC search           : 0.00
% 2.02/1.23  Cooper               : 0.00
% 2.02/1.23  Total                : 0.48
% 2.02/1.23  Index Insertion      : 0.00
% 2.02/1.23  Index Deletion       : 0.00
% 2.02/1.23  Index Matching       : 0.00
% 2.02/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
