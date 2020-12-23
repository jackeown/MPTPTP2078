%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:19 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 183 expanded)
%              Number of leaves         :   27 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 438 expanded)
%              Number of equality atoms :   65 ( 364 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_38,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_73,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_36,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_63,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_78,plain,(
    ! [A_33,B_34] : r1_tarski(A_33,k2_xboole_0(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_78])).

tff(c_324,plain,(
    ! [B_62,A_63] :
      ( k1_tarski(B_62) = A_63
      | k1_xboole_0 = A_63
      | ~ r1_tarski(A_63,k1_tarski(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_330,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_81,c_324])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_63,c_330])).

tff(c_343,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_441,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_tarski(A_78,k2_xboole_0(C_79,B_80))
      | ~ r1_tarski(A_78,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_449,plain,(
    ! [A_78] :
      ( r1_tarski(A_78,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_78,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_441])).

tff(c_344,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_28,plain,(
    ! [B_25,A_24] :
      ( k1_tarski(B_25) = A_24
      | k1_xboole_0 = A_24
      | ~ r1_tarski(A_24,k1_tarski(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_616,plain,(
    ! [B_96,A_97] :
      ( k1_tarski(B_96) = A_97
      | A_97 = '#skF_2'
      | ~ r1_tarski(A_97,k1_tarski(B_96)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_28])).

tff(c_632,plain,(
    ! [A_98] :
      ( k1_tarski('#skF_1') = A_98
      | A_98 = '#skF_2'
      | ~ r1_tarski(A_98,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_449,c_616])).

tff(c_636,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_632])).

tff(c_639,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_636])).

tff(c_14,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_345,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_14])).

tff(c_12,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_346,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_344,c_12])).

tff(c_486,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_503,plain,(
    ! [A_8] : k5_xboole_0(A_8,'#skF_2') = k4_xboole_0(A_8,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_486])).

tff(c_507,plain,(
    ! [A_87] : k5_xboole_0(A_87,'#skF_2') = A_87 ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_503])).

tff(c_455,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k4_xboole_0(B_83,A_82)) = k2_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_464,plain,(
    ! [A_9] : k5_xboole_0('#skF_2',A_9) = k2_xboole_0('#skF_2',A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_455])).

tff(c_514,plain,(
    k2_xboole_0('#skF_2','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_464])).

tff(c_653,plain,(
    k2_xboole_0('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_639,c_639,c_514])).

tff(c_658,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_42])).

tff(c_717,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_658])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_717])).

tff(c_720,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_721,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_40,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_750,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_721,c_40])).

tff(c_728,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_42])).

tff(c_889,plain,(
    ! [A_122,C_123,B_124] :
      ( r1_tarski(A_122,k2_xboole_0(C_123,B_124))
      | ~ r1_tarski(A_122,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_901,plain,(
    ! [A_122] :
      ( r1_tarski(A_122,'#skF_2')
      | ~ r1_tarski(A_122,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_889])).

tff(c_986,plain,(
    ! [B_133,A_134] :
      ( k1_tarski(B_133) = A_134
      | k1_xboole_0 = A_134
      | ~ r1_tarski(A_134,k1_tarski(B_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_989,plain,(
    ! [A_134] :
      ( k1_tarski('#skF_1') = A_134
      | k1_xboole_0 = A_134
      | ~ r1_tarski(A_134,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_986])).

tff(c_1002,plain,(
    ! [A_135] :
      ( A_135 = '#skF_2'
      | k1_xboole_0 = A_135
      | ~ r1_tarski(A_135,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_989])).

tff(c_1022,plain,(
    ! [A_136] :
      ( A_136 = '#skF_2'
      | k1_xboole_0 = A_136
      | ~ r1_tarski(A_136,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_901,c_1002])).

tff(c_1026,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_1022])).

tff(c_1030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_720,c_750,c_1026])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:59:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.45  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.78/1.45  
% 2.78/1.45  %Foreground sorts:
% 2.78/1.45  
% 2.78/1.45  
% 2.78/1.45  %Background operators:
% 2.78/1.45  
% 2.78/1.45  
% 2.78/1.45  %Foreground operators:
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.78/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.78/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.78/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.45  
% 3.06/1.46  tff(f_80, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.06/1.46  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.06/1.46  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.06/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.06/1.46  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.06/1.46  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.06/1.46  tff(f_39, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.06/1.46  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.06/1.46  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.06/1.46  tff(c_38, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.06/1.46  tff(c_73, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_38])).
% 3.06/1.46  tff(c_36, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.06/1.46  tff(c_63, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_36])).
% 3.06/1.46  tff(c_42, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.06/1.46  tff(c_78, plain, (![A_33, B_34]: (r1_tarski(A_33, k2_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.06/1.46  tff(c_81, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_78])).
% 3.06/1.46  tff(c_324, plain, (![B_62, A_63]: (k1_tarski(B_62)=A_63 | k1_xboole_0=A_63 | ~r1_tarski(A_63, k1_tarski(B_62)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.06/1.46  tff(c_330, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_81, c_324])).
% 3.06/1.46  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_63, c_330])).
% 3.06/1.46  tff(c_343, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 3.06/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.46  tff(c_441, plain, (![A_78, C_79, B_80]: (r1_tarski(A_78, k2_xboole_0(C_79, B_80)) | ~r1_tarski(A_78, B_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.46  tff(c_449, plain, (![A_78]: (r1_tarski(A_78, k1_tarski('#skF_1')) | ~r1_tarski(A_78, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_441])).
% 3.06/1.46  tff(c_344, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 3.06/1.46  tff(c_28, plain, (![B_25, A_24]: (k1_tarski(B_25)=A_24 | k1_xboole_0=A_24 | ~r1_tarski(A_24, k1_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.06/1.46  tff(c_616, plain, (![B_96, A_97]: (k1_tarski(B_96)=A_97 | A_97='#skF_2' | ~r1_tarski(A_97, k1_tarski(B_96)))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_28])).
% 3.06/1.46  tff(c_632, plain, (![A_98]: (k1_tarski('#skF_1')=A_98 | A_98='#skF_2' | ~r1_tarski(A_98, '#skF_3'))), inference(resolution, [status(thm)], [c_449, c_616])).
% 3.06/1.46  tff(c_636, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_6, c_632])).
% 3.06/1.46  tff(c_639, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_343, c_636])).
% 3.06/1.46  tff(c_14, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.46  tff(c_345, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_344, c_14])).
% 3.06/1.46  tff(c_12, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.06/1.46  tff(c_346, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_344, c_12])).
% 3.06/1.46  tff(c_486, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.06/1.46  tff(c_503, plain, (![A_8]: (k5_xboole_0(A_8, '#skF_2')=k4_xboole_0(A_8, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_346, c_486])).
% 3.06/1.46  tff(c_507, plain, (![A_87]: (k5_xboole_0(A_87, '#skF_2')=A_87)), inference(demodulation, [status(thm), theory('equality')], [c_345, c_503])).
% 3.06/1.46  tff(c_455, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k4_xboole_0(B_83, A_82))=k2_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.06/1.46  tff(c_464, plain, (![A_9]: (k5_xboole_0('#skF_2', A_9)=k2_xboole_0('#skF_2', A_9))), inference(superposition, [status(thm), theory('equality')], [c_345, c_455])).
% 3.06/1.46  tff(c_514, plain, (k2_xboole_0('#skF_2', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_507, c_464])).
% 3.06/1.46  tff(c_653, plain, (k2_xboole_0('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_639, c_639, c_639, c_514])).
% 3.06/1.46  tff(c_658, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_639, c_42])).
% 3.06/1.46  tff(c_717, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_658])).
% 3.06/1.46  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_717])).
% 3.06/1.46  tff(c_720, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.06/1.46  tff(c_721, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 3.06/1.46  tff(c_40, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.06/1.46  tff(c_750, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_721, c_721, c_40])).
% 3.06/1.46  tff(c_728, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_721, c_42])).
% 3.06/1.46  tff(c_889, plain, (![A_122, C_123, B_124]: (r1_tarski(A_122, k2_xboole_0(C_123, B_124)) | ~r1_tarski(A_122, B_124))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.46  tff(c_901, plain, (![A_122]: (r1_tarski(A_122, '#skF_2') | ~r1_tarski(A_122, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_728, c_889])).
% 3.06/1.46  tff(c_986, plain, (![B_133, A_134]: (k1_tarski(B_133)=A_134 | k1_xboole_0=A_134 | ~r1_tarski(A_134, k1_tarski(B_133)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.06/1.46  tff(c_989, plain, (![A_134]: (k1_tarski('#skF_1')=A_134 | k1_xboole_0=A_134 | ~r1_tarski(A_134, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_721, c_986])).
% 3.06/1.46  tff(c_1002, plain, (![A_135]: (A_135='#skF_2' | k1_xboole_0=A_135 | ~r1_tarski(A_135, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_721, c_989])).
% 3.06/1.46  tff(c_1022, plain, (![A_136]: (A_136='#skF_2' | k1_xboole_0=A_136 | ~r1_tarski(A_136, '#skF_3'))), inference(resolution, [status(thm)], [c_901, c_1002])).
% 3.06/1.46  tff(c_1026, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_1022])).
% 3.06/1.46  tff(c_1030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_720, c_750, c_1026])).
% 3.06/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.46  
% 3.06/1.46  Inference rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Ref     : 0
% 3.06/1.46  #Sup     : 232
% 3.06/1.46  #Fact    : 0
% 3.06/1.46  #Define  : 0
% 3.06/1.46  #Split   : 4
% 3.06/1.46  #Chain   : 0
% 3.06/1.46  #Close   : 0
% 3.06/1.46  
% 3.06/1.46  Ordering : KBO
% 3.06/1.46  
% 3.06/1.46  Simplification rules
% 3.06/1.46  ----------------------
% 3.06/1.46  #Subsume      : 9
% 3.06/1.46  #Demod        : 71
% 3.06/1.46  #Tautology    : 145
% 3.06/1.46  #SimpNegUnit  : 9
% 3.06/1.46  #BackRed      : 18
% 3.06/1.46  
% 3.06/1.46  #Partial instantiations: 0
% 3.06/1.46  #Strategies tried      : 1
% 3.06/1.46  
% 3.06/1.46  Timing (in seconds)
% 3.06/1.46  ----------------------
% 3.06/1.46  Preprocessing        : 0.30
% 3.06/1.46  Parsing              : 0.16
% 3.06/1.46  CNF conversion       : 0.02
% 3.06/1.46  Main loop            : 0.37
% 3.06/1.46  Inferencing          : 0.14
% 3.06/1.46  Reduction            : 0.12
% 3.06/1.46  Demodulation         : 0.08
% 3.06/1.46  BG Simplification    : 0.02
% 3.06/1.47  Subsumption          : 0.06
% 3.06/1.47  Abstraction          : 0.02
% 3.06/1.47  MUC search           : 0.00
% 3.06/1.47  Cooper               : 0.00
% 3.06/1.47  Total                : 0.70
% 3.06/1.47  Index Insertion      : 0.00
% 3.06/1.47  Index Deletion       : 0.00
% 3.06/1.47  Index Matching       : 0.00
% 3.06/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
