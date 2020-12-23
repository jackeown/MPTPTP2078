%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:45 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   42 (  46 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  65 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_28,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_40,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_60,axiom,(
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

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_46,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden(A_19,B_20)
      | ~ r1_xboole_0(k1_tarski(A_19),B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [A_19] : ~ r2_hidden(A_19,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_46])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    ! [A_17] :
      ( v1_relat_1(A_17)
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_36])).

tff(c_41,plain,(
    ! [A_18] :
      ( v1_funct_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_45,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_41])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_1'(A_22,B_23),k1_relat_1(B_23))
      | v5_funct_1(B_23,A_22)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_56,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_1'(A_22,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_22)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_53])).

tff(c_58,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_1'(A_22,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_45,c_56])).

tff(c_60,plain,(
    ! [A_24] :
      ( v5_funct_1(k1_xboole_0,A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_58])).

tff(c_22,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_63,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_22])).

tff(c_67,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.04  
% 1.60/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.04  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.60/1.04  
% 1.60/1.04  %Foreground sorts:
% 1.60/1.04  
% 1.60/1.04  
% 1.60/1.04  %Background operators:
% 1.60/1.04  
% 1.60/1.04  
% 1.60/1.04  %Foreground operators:
% 1.60/1.04  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.60/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.04  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.60/1.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.04  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.04  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.60/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.60/1.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.60/1.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.04  
% 1.74/1.05  tff(f_67, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 1.74/1.05  tff(f_28, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.74/1.05  tff(f_33, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.74/1.05  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.74/1.05  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.74/1.05  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.74/1.05  tff(f_40, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.74/1.05  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 1.74/1.05  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.74/1.05  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.74/1.05  tff(c_4, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.74/1.05  tff(c_46, plain, (![A_19, B_20]: (~r2_hidden(A_19, B_20) | ~r1_xboole_0(k1_tarski(A_19), B_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.74/1.05  tff(c_51, plain, (![A_19]: (~r2_hidden(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_46])).
% 1.74/1.05  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.74/1.05  tff(c_36, plain, (![A_17]: (v1_relat_1(A_17) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.74/1.05  tff(c_40, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_36])).
% 1.74/1.05  tff(c_41, plain, (![A_18]: (v1_funct_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.74/1.05  tff(c_45, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_41])).
% 1.74/1.05  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.74/1.05  tff(c_53, plain, (![A_22, B_23]: (r2_hidden('#skF_1'(A_22, B_23), k1_relat_1(B_23)) | v5_funct_1(B_23, A_22) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.74/1.05  tff(c_56, plain, (![A_22]: (r2_hidden('#skF_1'(A_22, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_22) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_12, c_53])).
% 1.74/1.05  tff(c_58, plain, (![A_22]: (r2_hidden('#skF_1'(A_22, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_45, c_56])).
% 1.74/1.05  tff(c_60, plain, (![A_24]: (v5_funct_1(k1_xboole_0, A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(negUnitSimplification, [status(thm)], [c_51, c_58])).
% 1.74/1.05  tff(c_22, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.74/1.05  tff(c_63, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_22])).
% 1.74/1.05  tff(c_67, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_63])).
% 1.74/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.05  
% 1.74/1.05  Inference rules
% 1.74/1.05  ----------------------
% 1.74/1.05  #Ref     : 0
% 1.74/1.05  #Sup     : 9
% 1.74/1.05  #Fact    : 0
% 1.74/1.05  #Define  : 0
% 1.74/1.05  #Split   : 0
% 1.74/1.05  #Chain   : 0
% 1.74/1.05  #Close   : 0
% 1.74/1.05  
% 1.74/1.05  Ordering : KBO
% 1.74/1.05  
% 1.74/1.05  Simplification rules
% 1.74/1.05  ----------------------
% 1.74/1.05  #Subsume      : 0
% 1.74/1.05  #Demod        : 4
% 1.74/1.05  #Tautology    : 4
% 1.74/1.05  #SimpNegUnit  : 1
% 1.74/1.05  #BackRed      : 0
% 1.74/1.05  
% 1.74/1.05  #Partial instantiations: 0
% 1.74/1.05  #Strategies tried      : 1
% 1.74/1.05  
% 1.74/1.05  Timing (in seconds)
% 1.74/1.05  ----------------------
% 1.74/1.05  Preprocessing        : 0.25
% 1.74/1.05  Parsing              : 0.14
% 1.74/1.05  CNF conversion       : 0.02
% 1.74/1.05  Main loop            : 0.11
% 1.74/1.05  Inferencing          : 0.05
% 1.74/1.05  Reduction            : 0.03
% 1.74/1.05  Demodulation         : 0.02
% 1.74/1.05  BG Simplification    : 0.01
% 1.74/1.05  Subsumption          : 0.01
% 1.74/1.05  Abstraction          : 0.00
% 1.74/1.05  MUC search           : 0.00
% 1.74/1.05  Cooper               : 0.00
% 1.74/1.05  Total                : 0.38
% 1.74/1.05  Index Insertion      : 0.00
% 1.74/1.05  Index Deletion       : 0.00
% 1.74/1.05  Index Matching       : 0.00
% 1.74/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
