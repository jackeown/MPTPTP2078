%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:28 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 ( 101 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_49,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_66,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v5_ordinal1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_18,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_45,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_47,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_45])).

tff(c_12,plain,(
    ! [B_5] : v5_relat_1(k1_xboole_0,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_2')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_36,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_34])).

tff(c_50,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_36])).

tff(c_51,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_32,plain,(
    ! [A_9] : v1_relat_1('#skF_1'(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_9] : v5_relat_1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    ! [B_24,A_25] :
      ( r1_tarski(k2_relat_1(B_24),A_25)
      | ~ v5_relat_1(B_24,A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_109,plain,(
    ! [B_29] :
      ( k2_relat_1(B_29) = k1_xboole_0
      | ~ v5_relat_1(B_29,k1_xboole_0)
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_113,plain,
    ( k2_relat_1('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1('#skF_1'(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_30,c_109])).

tff(c_120,plain,(
    k2_relat_1('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_113])).

tff(c_63,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,(
    ! [A_9] :
      ( k2_relat_1('#skF_1'(A_9)) != k1_xboole_0
      | '#skF_1'(A_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_166,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_76])).

tff(c_26,plain,(
    ! [A_9] : v5_ordinal1('#skF_1'(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_181,plain,(
    v5_ordinal1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_26])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_181])).

tff(c_194,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_196,plain,(
    ! [A_33] : v1_funct_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_198,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_196])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:47:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  
% 1.81/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 1.81/1.18  
% 1.81/1.18  %Foreground sorts:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Background operators:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Foreground operators:
% 1.81/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.81/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.18  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.81/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.18  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.81/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.81/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.18  
% 1.81/1.19  tff(f_49, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.81/1.19  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.81/1.19  tff(f_40, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l222_relat_1)).
% 1.81/1.19  tff(f_75, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.81/1.19  tff(f_66, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) & v5_ordinal1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_ordinal1)).
% 1.81/1.19  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.81/1.19  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.81/1.19  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.81/1.19  tff(c_18, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.19  tff(c_45, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.19  tff(c_47, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_45])).
% 1.81/1.19  tff(c_12, plain, (![B_5]: (v5_relat_1(k1_xboole_0, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.19  tff(c_34, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_2') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.81/1.19  tff(c_36, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_34])).
% 1.81/1.19  tff(c_50, plain, (~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_47, c_36])).
% 1.81/1.19  tff(c_51, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_50])).
% 1.81/1.19  tff(c_32, plain, (![A_9]: (v1_relat_1('#skF_1'(A_9)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.81/1.19  tff(c_30, plain, (![A_9]: (v5_relat_1('#skF_1'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.81/1.19  tff(c_92, plain, (![B_24, A_25]: (r1_tarski(k2_relat_1(B_24), A_25) | ~v5_relat_1(B_24, A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.81/1.19  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.81/1.19  tff(c_109, plain, (![B_29]: (k2_relat_1(B_29)=k1_xboole_0 | ~v5_relat_1(B_29, k1_xboole_0) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_92, c_4])).
% 1.81/1.19  tff(c_113, plain, (k2_relat_1('#skF_1'(k1_xboole_0))=k1_xboole_0 | ~v1_relat_1('#skF_1'(k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_109])).
% 1.81/1.19  tff(c_120, plain, (k2_relat_1('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_113])).
% 1.81/1.19  tff(c_63, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.81/1.19  tff(c_76, plain, (![A_9]: (k2_relat_1('#skF_1'(A_9))!=k1_xboole_0 | '#skF_1'(A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_63])).
% 1.81/1.19  tff(c_166, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_120, c_76])).
% 1.81/1.19  tff(c_26, plain, (![A_9]: (v5_ordinal1('#skF_1'(A_9)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.81/1.19  tff(c_181, plain, (v5_ordinal1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166, c_26])).
% 1.81/1.19  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_181])).
% 1.81/1.19  tff(c_194, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_50])).
% 1.81/1.19  tff(c_196, plain, (![A_33]: (v1_funct_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.19  tff(c_198, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_196])).
% 1.81/1.19  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_198])).
% 1.81/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  Inference rules
% 1.81/1.19  ----------------------
% 1.81/1.19  #Ref     : 0
% 1.81/1.19  #Sup     : 36
% 1.81/1.19  #Fact    : 0
% 1.81/1.19  #Define  : 0
% 1.81/1.20  #Split   : 1
% 1.81/1.20  #Chain   : 0
% 1.81/1.20  #Close   : 0
% 1.81/1.20  
% 1.81/1.20  Ordering : KBO
% 1.81/1.20  
% 1.81/1.20  Simplification rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Subsume      : 0
% 1.81/1.20  #Demod        : 21
% 1.81/1.20  #Tautology    : 20
% 1.81/1.20  #SimpNegUnit  : 2
% 1.81/1.20  #BackRed      : 1
% 1.81/1.20  
% 1.81/1.20  #Partial instantiations: 0
% 1.81/1.20  #Strategies tried      : 1
% 1.81/1.20  
% 1.81/1.20  Timing (in seconds)
% 1.81/1.20  ----------------------
% 1.81/1.20  Preprocessing        : 0.27
% 1.81/1.20  Parsing              : 0.15
% 1.81/1.20  CNF conversion       : 0.02
% 1.81/1.20  Main loop            : 0.15
% 1.81/1.20  Inferencing          : 0.06
% 1.81/1.20  Reduction            : 0.05
% 1.81/1.20  Demodulation         : 0.03
% 1.81/1.20  BG Simplification    : 0.01
% 1.81/1.20  Subsumption          : 0.02
% 1.81/1.20  Abstraction          : 0.01
% 1.81/1.20  MUC search           : 0.00
% 1.81/1.20  Cooper               : 0.00
% 1.81/1.20  Total                : 0.45
% 1.81/1.20  Index Insertion      : 0.00
% 1.81/1.20  Index Deletion       : 0.00
% 1.81/1.20  Index Matching       : 0.00
% 1.81/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
