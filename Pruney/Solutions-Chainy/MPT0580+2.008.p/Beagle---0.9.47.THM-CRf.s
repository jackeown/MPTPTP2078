%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:57 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   60 (  95 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 177 expanded)
%              Number of equality atoms :   28 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > k1_enumset1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v3_relat_1,type,(
    v3_relat_1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v3_relat_1(A)
        <=> ! [B] :
              ( r2_hidden(B,k2_relat_1(A))
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v3_relat_1(A)
      <=> r1_tarski(k2_relat_1(A),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

tff(c_42,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v3_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_53,plain,(
    ~ v3_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    ! [A_30,B_31] : k1_enumset1(A_30,A_30,B_31) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [E_12,A_6,C_8] : r2_hidden(E_12,k1_enumset1(A_6,E_12,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_86,plain,(
    ! [A_33,B_34] : r2_hidden(A_33,k2_tarski(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_12])).

tff(c_89,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_86])).

tff(c_97,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),A_38)
      | r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [B_19] :
      ( v3_relat_1('#skF_4')
      | k1_xboole_0 = B_19
      | ~ r2_hidden(B_19,k2_relat_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_84,plain,(
    ! [B_19] :
      ( k1_xboole_0 = B_19
      | ~ r2_hidden(B_19,k2_relat_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_52])).

tff(c_219,plain,(
    ! [B_72] :
      ( '#skF_1'(k2_relat_1('#skF_4'),B_72) = k1_xboole_0
      | r1_tarski(k2_relat_1('#skF_4'),B_72) ) ),
    inference(resolution,[status(thm)],[c_97,c_84])).

tff(c_36,plain,(
    ! [A_16] :
      ( v3_relat_1(A_16)
      | ~ r1_tarski(k2_relat_1(A_16),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_223,plain,
    ( v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_1'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_219,c_36])).

tff(c_226,plain,
    ( v3_relat_1('#skF_4')
    | '#skF_1'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_223])).

tff(c_227,plain,(
    '#skF_1'(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_226])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_231,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_4])).

tff(c_238,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_231])).

tff(c_242,plain,
    ( v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_238,c_36])).

tff(c_245,plain,(
    v3_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_242])).

tff(c_247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_245])).

tff(c_248,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_249,plain,(
    v3_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_38,plain,(
    ! [A_16] :
      ( r1_tarski(k2_relat_1(A_16),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,
    ( r2_hidden('#skF_5',k2_relat_1('#skF_4'))
    | ~ v3_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_263,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_44])).

tff(c_304,plain,(
    ! [C_96,B_97,A_98] :
      ( r2_hidden(C_96,B_97)
      | ~ r2_hidden(C_96,A_98)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_329,plain,(
    ! [B_99] :
      ( r2_hidden('#skF_5',B_99)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_99) ) ),
    inference(resolution,[status(thm)],[c_263,c_304])).

tff(c_333,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_xboole_0))
    | ~ v3_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_329])).

tff(c_340,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_249,c_333])).

tff(c_34,plain,(
    ! [A_14,B_15] : k1_enumset1(A_14,A_14,B_15) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_385,plain,(
    ! [E_110,C_111,B_112,A_113] :
      ( E_110 = C_111
      | E_110 = B_112
      | E_110 = A_113
      | ~ r2_hidden(E_110,k1_enumset1(A_113,B_112,C_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_453,plain,(
    ! [E_129,B_130,A_131] :
      ( E_129 = B_130
      | E_129 = A_131
      | E_129 = A_131
      | ~ r2_hidden(E_129,k2_tarski(A_131,B_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_385])).

tff(c_478,plain,(
    ! [E_136,A_137] :
      ( E_136 = A_137
      | E_136 = A_137
      | E_136 = A_137
      | ~ r2_hidden(E_136,k1_tarski(A_137)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_453])).

tff(c_485,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_340,c_478])).

tff(c_497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_248,c_248,c_485])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.38  
% 2.39/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.38  %$ r2_hidden > r1_tarski > v3_relat_1 > v1_relat_1 > k1_enumset1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.39/1.38  
% 2.39/1.38  %Foreground sorts:
% 2.39/1.38  
% 2.39/1.38  
% 2.39/1.38  %Background operators:
% 2.39/1.38  
% 2.39/1.38  
% 2.39/1.38  %Foreground operators:
% 2.39/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.38  tff(v3_relat_1, type, v3_relat_1: $i > $o).
% 2.39/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.39/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.39/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.39/1.38  
% 2.39/1.39  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> (![B]: (r2_hidden(B, k2_relat_1(A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t184_relat_1)).
% 2.39/1.39  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.39/1.39  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.39/1.39  tff(f_47, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.39/1.39  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.39/1.39  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (v3_relat_1(A) <=> r1_tarski(k2_relat_1(A), k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_relat_1)).
% 2.39/1.39  tff(c_42, plain, (k1_xboole_0!='#skF_5' | ~v3_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.39  tff(c_53, plain, (~v3_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 2.39/1.39  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.39  tff(c_32, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.39/1.39  tff(c_66, plain, (![A_30, B_31]: (k1_enumset1(A_30, A_30, B_31)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.39  tff(c_12, plain, (![E_12, A_6, C_8]: (r2_hidden(E_12, k1_enumset1(A_6, E_12, C_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.39  tff(c_86, plain, (![A_33, B_34]: (r2_hidden(A_33, k2_tarski(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_12])).
% 2.39/1.39  tff(c_89, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_86])).
% 2.39/1.39  tff(c_97, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), A_38) | r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.39/1.39  tff(c_52, plain, (![B_19]: (v3_relat_1('#skF_4') | k1_xboole_0=B_19 | ~r2_hidden(B_19, k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.39  tff(c_84, plain, (![B_19]: (k1_xboole_0=B_19 | ~r2_hidden(B_19, k2_relat_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_53, c_52])).
% 2.39/1.39  tff(c_219, plain, (![B_72]: ('#skF_1'(k2_relat_1('#skF_4'), B_72)=k1_xboole_0 | r1_tarski(k2_relat_1('#skF_4'), B_72))), inference(resolution, [status(thm)], [c_97, c_84])).
% 2.39/1.39  tff(c_36, plain, (![A_16]: (v3_relat_1(A_16) | ~r1_tarski(k2_relat_1(A_16), k1_tarski(k1_xboole_0)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.39/1.39  tff(c_223, plain, (v3_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_1'(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_219, c_36])).
% 2.39/1.39  tff(c_226, plain, (v3_relat_1('#skF_4') | '#skF_1'(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_223])).
% 2.39/1.39  tff(c_227, plain, ('#skF_1'(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_53, c_226])).
% 2.39/1.39  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.39/1.39  tff(c_231, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_227, c_4])).
% 2.39/1.39  tff(c_238, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_231])).
% 2.39/1.39  tff(c_242, plain, (v3_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_238, c_36])).
% 2.39/1.39  tff(c_245, plain, (v3_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_242])).
% 2.39/1.39  tff(c_247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_245])).
% 2.39/1.39  tff(c_248, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_42])).
% 2.39/1.39  tff(c_249, plain, (v3_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 2.39/1.39  tff(c_38, plain, (![A_16]: (r1_tarski(k2_relat_1(A_16), k1_tarski(k1_xboole_0)) | ~v3_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.39/1.39  tff(c_44, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4')) | ~v3_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.39/1.39  tff(c_263, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_44])).
% 2.39/1.39  tff(c_304, plain, (![C_96, B_97, A_98]: (r2_hidden(C_96, B_97) | ~r2_hidden(C_96, A_98) | ~r1_tarski(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.39/1.39  tff(c_329, plain, (![B_99]: (r2_hidden('#skF_5', B_99) | ~r1_tarski(k2_relat_1('#skF_4'), B_99))), inference(resolution, [status(thm)], [c_263, c_304])).
% 2.39/1.39  tff(c_333, plain, (r2_hidden('#skF_5', k1_tarski(k1_xboole_0)) | ~v3_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_329])).
% 2.39/1.39  tff(c_340, plain, (r2_hidden('#skF_5', k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_249, c_333])).
% 2.39/1.39  tff(c_34, plain, (![A_14, B_15]: (k1_enumset1(A_14, A_14, B_15)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.39/1.39  tff(c_385, plain, (![E_110, C_111, B_112, A_113]: (E_110=C_111 | E_110=B_112 | E_110=A_113 | ~r2_hidden(E_110, k1_enumset1(A_113, B_112, C_111)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.39/1.39  tff(c_453, plain, (![E_129, B_130, A_131]: (E_129=B_130 | E_129=A_131 | E_129=A_131 | ~r2_hidden(E_129, k2_tarski(A_131, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_385])).
% 2.39/1.39  tff(c_478, plain, (![E_136, A_137]: (E_136=A_137 | E_136=A_137 | E_136=A_137 | ~r2_hidden(E_136, k1_tarski(A_137)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_453])).
% 2.39/1.39  tff(c_485, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_340, c_478])).
% 2.39/1.39  tff(c_497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248, c_248, c_248, c_485])).
% 2.39/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.39  
% 2.39/1.39  Inference rules
% 2.39/1.39  ----------------------
% 2.39/1.39  #Ref     : 0
% 2.39/1.39  #Sup     : 92
% 2.39/1.39  #Fact    : 0
% 2.39/1.39  #Define  : 0
% 2.39/1.39  #Split   : 1
% 2.39/1.39  #Chain   : 0
% 2.39/1.39  #Close   : 0
% 2.39/1.39  
% 2.39/1.39  Ordering : KBO
% 2.39/1.39  
% 2.39/1.39  Simplification rules
% 2.39/1.39  ----------------------
% 2.39/1.39  #Subsume      : 14
% 2.39/1.39  #Demod        : 26
% 2.39/1.39  #Tautology    : 42
% 2.39/1.39  #SimpNegUnit  : 4
% 2.39/1.39  #BackRed      : 0
% 2.39/1.39  
% 2.39/1.39  #Partial instantiations: 0
% 2.39/1.39  #Strategies tried      : 1
% 2.39/1.39  
% 2.39/1.39  Timing (in seconds)
% 2.39/1.39  ----------------------
% 2.39/1.40  Preprocessing        : 0.31
% 2.39/1.40  Parsing              : 0.16
% 2.39/1.40  CNF conversion       : 0.02
% 2.39/1.40  Main loop            : 0.24
% 2.39/1.40  Inferencing          : 0.09
% 2.39/1.40  Reduction            : 0.07
% 2.39/1.40  Demodulation         : 0.05
% 2.39/1.40  BG Simplification    : 0.02
% 2.39/1.40  Subsumption          : 0.04
% 2.39/1.40  Abstraction          : 0.01
% 2.39/1.40  MUC search           : 0.00
% 2.39/1.40  Cooper               : 0.00
% 2.39/1.40  Total                : 0.58
% 2.39/1.40  Index Insertion      : 0.00
% 2.39/1.40  Index Deletion       : 0.00
% 2.39/1.40  Index Matching       : 0.00
% 2.39/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
