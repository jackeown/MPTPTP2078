%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:37 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 111 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :   69 ( 157 expanded)
%              Number of equality atoms :   25 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_106,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_30,plain,(
    ! [C_28] : r2_hidden(C_28,k1_tarski(C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_104,plain,(
    ! [B_77,A_78] :
      ( ~ r2_hidden(B_77,A_78)
      | ~ v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [C_28] : ~ v1_xboole_0(k1_tarski(C_28)) ),
    inference(resolution,[status(thm)],[c_30,c_104])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_116,plain,(
    ! [C_82,A_83] :
      ( C_82 = A_83
      | ~ r2_hidden(C_82,k1_tarski(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_120,plain,(
    ! [A_83] :
      ( '#skF_1'(k1_tarski(A_83)) = A_83
      | v1_xboole_0(k1_tarski(A_83)) ) ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_126,plain,(
    ! [A_83] : '#skF_1'(k1_tarski(A_83)) = A_83 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_120])).

tff(c_22,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_193,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,B_95)
      | ~ r2_hidden(C_96,k3_xboole_0(A_94,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_211,plain,(
    ! [A_97,C_98] :
      ( ~ r1_xboole_0(A_97,A_97)
      | ~ r2_hidden(C_98,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_193])).

tff(c_214,plain,(
    ! [C_98] : ~ r2_hidden(C_98,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_211])).

tff(c_64,plain,(
    ! [B_70] : r1_tarski(k1_xboole_0,k1_tarski(B_70)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_159,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,B_90) = A_89
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_172,plain,(
    ! [B_70] : k3_xboole_0(k1_xboole_0,k1_tarski(B_70)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_159])).

tff(c_460,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_2'(A_125,B_126),k3_xboole_0(A_125,B_126))
      | r1_xboole_0(A_125,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_472,plain,(
    ! [B_70] :
      ( r2_hidden('#skF_2'(k1_xboole_0,k1_tarski(B_70)),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,k1_tarski(B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_460])).

tff(c_482,plain,(
    ! [B_70] : r1_xboole_0(k1_xboole_0,k1_tarski(B_70)) ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_472])).

tff(c_68,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_445,plain,(
    ! [B_123,A_124] :
      ( k1_tarski(B_123) = A_124
      | k1_xboole_0 = A_124
      | ~ r1_tarski(A_124,k1_tarski(B_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_457,plain,
    ( k1_tarski('#skF_5') = k1_tarski('#skF_6')
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_445])).

tff(c_484,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_457])).

tff(c_171,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_159])).

tff(c_196,plain,(
    ! [C_96] :
      ( ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6'))
      | ~ r2_hidden(C_96,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_193])).

tff(c_276,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_487,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_276])).

tff(c_494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_487])).

tff(c_495,plain,(
    k1_tarski('#skF_5') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_457])).

tff(c_528,plain,(
    '#skF_1'(k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_126])).

tff(c_554,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_528])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_554])).

tff(c_559,plain,(
    ! [C_128] : ~ r2_hidden(C_128,k1_tarski('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_563,plain,(
    v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_559])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.30  
% 2.61/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.61/1.31  
% 2.61/1.31  %Foreground sorts:
% 2.61/1.31  
% 2.61/1.31  
% 2.61/1.31  %Background operators:
% 2.61/1.31  
% 2.61/1.31  
% 2.61/1.31  %Foreground operators:
% 2.61/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.61/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.61/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.61/1.31  
% 2.61/1.32  tff(f_80, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.61/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.61/1.32  tff(f_111, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.61/1.32  tff(f_71, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.61/1.32  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.61/1.32  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.61/1.32  tff(f_106, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.61/1.32  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.61/1.32  tff(c_30, plain, (![C_28]: (r2_hidden(C_28, k1_tarski(C_28)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.61/1.32  tff(c_104, plain, (![B_77, A_78]: (~r2_hidden(B_77, A_78) | ~v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.32  tff(c_108, plain, (![C_28]: (~v1_xboole_0(k1_tarski(C_28)))), inference(resolution, [status(thm)], [c_30, c_104])).
% 2.61/1.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.32  tff(c_66, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.61/1.32  tff(c_116, plain, (![C_82, A_83]: (C_82=A_83 | ~r2_hidden(C_82, k1_tarski(A_83)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.61/1.32  tff(c_120, plain, (![A_83]: ('#skF_1'(k1_tarski(A_83))=A_83 | v1_xboole_0(k1_tarski(A_83)))), inference(resolution, [status(thm)], [c_4, c_116])).
% 2.61/1.32  tff(c_126, plain, (![A_83]: ('#skF_1'(k1_tarski(A_83))=A_83)), inference(negUnitSimplification, [status(thm)], [c_108, c_120])).
% 2.61/1.32  tff(c_22, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.61/1.32  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.32  tff(c_193, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, B_95) | ~r2_hidden(C_96, k3_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.32  tff(c_211, plain, (![A_97, C_98]: (~r1_xboole_0(A_97, A_97) | ~r2_hidden(C_98, A_97))), inference(superposition, [status(thm), theory('equality')], [c_6, c_193])).
% 2.61/1.32  tff(c_214, plain, (![C_98]: (~r2_hidden(C_98, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_211])).
% 2.61/1.32  tff(c_64, plain, (![B_70]: (r1_tarski(k1_xboole_0, k1_tarski(B_70)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.61/1.32  tff(c_159, plain, (![A_89, B_90]: (k3_xboole_0(A_89, B_90)=A_89 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.61/1.32  tff(c_172, plain, (![B_70]: (k3_xboole_0(k1_xboole_0, k1_tarski(B_70))=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_159])).
% 2.61/1.32  tff(c_460, plain, (![A_125, B_126]: (r2_hidden('#skF_2'(A_125, B_126), k3_xboole_0(A_125, B_126)) | r1_xboole_0(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.61/1.32  tff(c_472, plain, (![B_70]: (r2_hidden('#skF_2'(k1_xboole_0, k1_tarski(B_70)), k1_xboole_0) | r1_xboole_0(k1_xboole_0, k1_tarski(B_70)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_460])).
% 2.61/1.32  tff(c_482, plain, (![B_70]: (r1_xboole_0(k1_xboole_0, k1_tarski(B_70)))), inference(negUnitSimplification, [status(thm)], [c_214, c_472])).
% 2.61/1.32  tff(c_68, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.61/1.32  tff(c_445, plain, (![B_123, A_124]: (k1_tarski(B_123)=A_124 | k1_xboole_0=A_124 | ~r1_tarski(A_124, k1_tarski(B_123)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.61/1.32  tff(c_457, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6') | k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_68, c_445])).
% 2.61/1.32  tff(c_484, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_457])).
% 2.61/1.32  tff(c_171, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_68, c_159])).
% 2.61/1.32  tff(c_196, plain, (![C_96]: (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6')) | ~r2_hidden(C_96, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_171, c_193])).
% 2.61/1.32  tff(c_276, plain, (~r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_196])).
% 2.61/1.32  tff(c_487, plain, (~r1_xboole_0(k1_xboole_0, k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_484, c_276])).
% 2.61/1.32  tff(c_494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_482, c_487])).
% 2.61/1.32  tff(c_495, plain, (k1_tarski('#skF_5')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_457])).
% 2.61/1.32  tff(c_528, plain, ('#skF_1'(k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_495, c_126])).
% 2.61/1.32  tff(c_554, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_528])).
% 2.61/1.32  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_554])).
% 2.61/1.32  tff(c_559, plain, (![C_128]: (~r2_hidden(C_128, k1_tarski('#skF_5')))), inference(splitRight, [status(thm)], [c_196])).
% 2.61/1.32  tff(c_563, plain, (v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_4, c_559])).
% 2.61/1.32  tff(c_570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_563])).
% 2.61/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.32  
% 2.61/1.32  Inference rules
% 2.61/1.32  ----------------------
% 2.61/1.32  #Ref     : 0
% 2.61/1.32  #Sup     : 119
% 2.61/1.32  #Fact    : 0
% 2.61/1.32  #Define  : 0
% 2.61/1.32  #Split   : 2
% 2.61/1.32  #Chain   : 0
% 2.61/1.32  #Close   : 0
% 2.61/1.32  
% 2.61/1.32  Ordering : KBO
% 2.61/1.32  
% 2.61/1.32  Simplification rules
% 2.61/1.32  ----------------------
% 2.61/1.32  #Subsume      : 13
% 2.61/1.32  #Demod        : 59
% 2.61/1.32  #Tautology    : 76
% 2.61/1.32  #SimpNegUnit  : 9
% 2.61/1.32  #BackRed      : 11
% 2.61/1.32  
% 2.61/1.32  #Partial instantiations: 0
% 2.61/1.32  #Strategies tried      : 1
% 2.61/1.32  
% 2.61/1.32  Timing (in seconds)
% 2.61/1.32  ----------------------
% 2.61/1.32  Preprocessing        : 0.33
% 2.61/1.32  Parsing              : 0.18
% 2.61/1.32  CNF conversion       : 0.02
% 2.61/1.32  Main loop            : 0.24
% 2.61/1.32  Inferencing          : 0.08
% 2.61/1.32  Reduction            : 0.08
% 2.61/1.32  Demodulation         : 0.05
% 2.61/1.32  BG Simplification    : 0.02
% 2.61/1.32  Subsumption          : 0.04
% 2.61/1.32  Abstraction          : 0.01
% 2.61/1.32  MUC search           : 0.00
% 2.61/1.32  Cooper               : 0.00
% 2.61/1.32  Total                : 0.60
% 2.61/1.32  Index Insertion      : 0.00
% 2.61/1.32  Index Deletion       : 0.00
% 2.61/1.32  Index Matching       : 0.00
% 2.61/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
