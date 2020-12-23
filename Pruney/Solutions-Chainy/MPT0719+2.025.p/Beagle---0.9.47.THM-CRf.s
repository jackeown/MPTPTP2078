%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:46 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  65 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_28,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
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

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_57,plain,(
    ! [A_24,C_25,B_26] :
      ( ~ r2_hidden(A_24,C_25)
      | ~ r1_xboole_0(k2_tarski(A_24,B_26),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_24] : ~ r2_hidden(A_24,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_43,plain,(
    ! [A_21] :
      ( v1_funct_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_47,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_64,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_1'(A_28,B_29),k1_relat_1(B_29))
      | v5_funct_1(B_29,A_28)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_67,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_28)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_64])).

tff(c_69,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_47,c_67])).

tff(c_72,plain,(
    ! [A_33] :
      ( v5_funct_1(k1_xboole_0,A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_69])).

tff(c_24,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_75,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_24])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:23:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  
% 1.69/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.16  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.69/1.16  
% 1.69/1.16  %Foreground sorts:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Background operators:
% 1.69/1.16  
% 1.69/1.16  
% 1.69/1.16  %Foreground operators:
% 1.69/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.16  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.69/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.69/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.69/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.69/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.16  
% 1.69/1.17  tff(f_69, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.69/1.17  tff(f_28, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.69/1.17  tff(f_35, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.69/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.69/1.17  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.69/1.17  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.69/1.17  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.69/1.17  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.69/1.17  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.69/1.17  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.69/1.17  tff(c_4, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.69/1.17  tff(c_57, plain, (![A_24, C_25, B_26]: (~r2_hidden(A_24, C_25) | ~r1_xboole_0(k2_tarski(A_24, B_26), C_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.17  tff(c_62, plain, (![A_24]: (~r2_hidden(A_24, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_57])).
% 1.69/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.69/1.17  tff(c_38, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.17  tff(c_42, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_38])).
% 1.69/1.17  tff(c_43, plain, (![A_21]: (v1_funct_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.69/1.17  tff(c_47, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_43])).
% 1.69/1.17  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.69/1.17  tff(c_64, plain, (![A_28, B_29]: (r2_hidden('#skF_1'(A_28, B_29), k1_relat_1(B_29)) | v5_funct_1(B_29, A_28) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.69/1.17  tff(c_67, plain, (![A_28]: (r2_hidden('#skF_1'(A_28, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_28) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_14, c_64])).
% 1.69/1.17  tff(c_69, plain, (![A_28]: (r2_hidden('#skF_1'(A_28, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_47, c_67])).
% 1.69/1.17  tff(c_72, plain, (![A_33]: (v5_funct_1(k1_xboole_0, A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(negUnitSimplification, [status(thm)], [c_62, c_69])).
% 1.69/1.17  tff(c_24, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.69/1.17  tff(c_75, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_72, c_24])).
% 1.69/1.17  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_75])).
% 1.69/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  Inference rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Ref     : 0
% 1.69/1.17  #Sup     : 11
% 1.69/1.17  #Fact    : 0
% 1.69/1.17  #Define  : 0
% 1.69/1.17  #Split   : 0
% 1.69/1.17  #Chain   : 0
% 1.69/1.17  #Close   : 0
% 1.69/1.17  
% 1.69/1.17  Ordering : KBO
% 1.69/1.17  
% 1.69/1.17  Simplification rules
% 1.69/1.17  ----------------------
% 1.69/1.17  #Subsume      : 0
% 1.69/1.17  #Demod        : 4
% 1.69/1.17  #Tautology    : 6
% 1.69/1.17  #SimpNegUnit  : 1
% 1.69/1.17  #BackRed      : 0
% 1.69/1.17  
% 1.69/1.17  #Partial instantiations: 0
% 1.69/1.17  #Strategies tried      : 1
% 1.69/1.17  
% 1.69/1.17  Timing (in seconds)
% 1.69/1.17  ----------------------
% 1.69/1.18  Preprocessing        : 0.29
% 1.69/1.18  Parsing              : 0.15
% 1.69/1.18  CNF conversion       : 0.02
% 1.69/1.18  Main loop            : 0.11
% 1.69/1.18  Inferencing          : 0.05
% 1.69/1.18  Reduction            : 0.03
% 1.69/1.18  Demodulation         : 0.03
% 1.69/1.18  BG Simplification    : 0.01
% 1.69/1.18  Subsumption          : 0.01
% 1.69/1.18  Abstraction          : 0.01
% 1.88/1.18  MUC search           : 0.00
% 1.88/1.18  Cooper               : 0.00
% 1.88/1.18  Total                : 0.43
% 1.88/1.18  Index Insertion      : 0.00
% 1.88/1.18  Index Deletion       : 0.00
% 1.88/1.18  Index Matching       : 0.00
% 1.88/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
