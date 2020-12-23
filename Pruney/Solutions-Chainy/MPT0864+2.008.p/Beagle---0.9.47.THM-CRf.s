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
% DateTime   : Thu Dec  3 10:09:09 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 177 expanded)
%              Number of leaves         :   30 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 ( 253 expanded)
%              Number of equality atoms :   53 ( 221 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_42,plain,(
    k4_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_61,plain,(
    ! [A_47,B_48] : k1_mcart_1(k4_tarski(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_61])).

tff(c_40,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_40])).

tff(c_91,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_93,plain,(
    k4_tarski('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_42])).

tff(c_147,plain,(
    ! [A_67,B_68] : k2_zfmisc_1(k1_tarski(A_67),k1_tarski(B_68)) = k1_tarski(k4_tarski(A_67,B_68)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [B_34,A_33] :
      ( k2_zfmisc_1(k1_tarski(B_34),A_33) != k1_xboole_0
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_168,plain,(
    ! [A_69,B_70] :
      ( k1_tarski(k4_tarski(A_69,B_70)) != k1_xboole_0
      | k1_tarski(B_70) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_28])).

tff(c_171,plain,
    ( k1_tarski('#skF_1') != k1_xboole_0
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_168])).

tff(c_172,plain,(
    k1_tarski('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_35,B_36] :
      ( ~ r1_tarski(A_35,k2_zfmisc_1(A_35,B_36))
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_187,plain,(
    ! [A_77,B_78] :
      ( ~ r1_tarski(k1_tarski(A_77),k1_tarski(k4_tarski(A_77,B_78)))
      | k1_tarski(A_77) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_32])).

tff(c_190,plain,
    ( ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1'))
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_187])).

tff(c_192,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_190])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_192])).

tff(c_195,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_50,plain,(
    ! [A_46] : k2_tarski(A_46,A_46) = k1_tarski(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_31,B_32] : ~ v1_xboole_0(k2_tarski(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_55,plain,(
    ! [A_46] : ~ v1_xboole_0(k1_tarski(A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_24])).

tff(c_209,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_55])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_209])).

tff(c_215,plain,(
    k2_mcart_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_78,plain,(
    ! [A_50,B_51] : k2_mcart_1(k4_tarski(A_50,B_51)) = B_51 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_87,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_78])).

tff(c_221,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_87])).

tff(c_226,plain,(
    k4_tarski('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_42])).

tff(c_272,plain,(
    ! [A_94,B_95] : k2_zfmisc_1(k1_tarski(A_94),k1_tarski(B_95)) = k1_tarski(k4_tarski(A_94,B_95)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_33,B_34] :
      ( k2_zfmisc_1(A_33,k1_tarski(B_34)) != k1_xboole_0
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_297,plain,(
    ! [A_98,B_99] :
      ( k1_tarski(k4_tarski(A_98,B_99)) != k1_xboole_0
      | k1_tarski(A_98) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_26])).

tff(c_300,plain,
    ( k1_tarski('#skF_1') != k1_xboole_0
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_297])).

tff(c_301,plain,(
    k1_tarski('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_30,plain,(
    ! [A_35,B_36] :
      ( ~ r1_tarski(A_35,k2_zfmisc_1(B_36,A_35))
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_316,plain,(
    ! [B_106,A_107] :
      ( ~ r1_tarski(k1_tarski(B_106),k1_tarski(k4_tarski(A_107,B_106)))
      | k1_tarski(B_106) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_30])).

tff(c_319,plain,
    ( ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1'))
    | k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_316])).

tff(c_321,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_319])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_321])).

tff(c_324,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_338,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_55])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  %$ r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.31  
% 2.09/1.31  %Foreground sorts:
% 2.09/1.31  
% 2.09/1.31  
% 2.09/1.31  %Background operators:
% 2.09/1.31  
% 2.09/1.31  
% 2.09/1.31  %Foreground operators:
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.09/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.09/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.09/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.31  
% 2.09/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.09/1.33  tff(f_80, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.09/1.33  tff(f_70, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.09/1.33  tff(f_66, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 2.09/1.33  tff(f_58, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.09/1.33  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.09/1.33  tff(f_64, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.09/1.33  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.33  tff(f_49, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 2.09/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.09/1.33  tff(c_42, plain, (k4_tarski('#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.09/1.33  tff(c_61, plain, (![A_47, B_48]: (k1_mcart_1(k4_tarski(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.33  tff(c_70, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_42, c_61])).
% 2.09/1.33  tff(c_40, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.09/1.33  tff(c_90, plain, (k2_mcart_1('#skF_1')='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_40])).
% 2.09/1.33  tff(c_91, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_90])).
% 2.09/1.33  tff(c_93, plain, (k4_tarski('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_42])).
% 2.09/1.33  tff(c_147, plain, (![A_67, B_68]: (k2_zfmisc_1(k1_tarski(A_67), k1_tarski(B_68))=k1_tarski(k4_tarski(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.33  tff(c_28, plain, (![B_34, A_33]: (k2_zfmisc_1(k1_tarski(B_34), A_33)!=k1_xboole_0 | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.33  tff(c_168, plain, (![A_69, B_70]: (k1_tarski(k4_tarski(A_69, B_70))!=k1_xboole_0 | k1_tarski(B_70)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_147, c_28])).
% 2.09/1.33  tff(c_171, plain, (k1_tarski('#skF_1')!=k1_xboole_0 | k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93, c_168])).
% 2.09/1.33  tff(c_172, plain, (k1_tarski('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_171])).
% 2.09/1.33  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.33  tff(c_32, plain, (![A_35, B_36]: (~r1_tarski(A_35, k2_zfmisc_1(A_35, B_36)) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.33  tff(c_187, plain, (![A_77, B_78]: (~r1_tarski(k1_tarski(A_77), k1_tarski(k4_tarski(A_77, B_78))) | k1_tarski(A_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_147, c_32])).
% 2.09/1.33  tff(c_190, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1')) | k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_93, c_187])).
% 2.09/1.33  tff(c_192, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_190])).
% 2.09/1.33  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_192])).
% 2.09/1.33  tff(c_195, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_171])).
% 2.09/1.33  tff(c_50, plain, (![A_46]: (k2_tarski(A_46, A_46)=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.09/1.33  tff(c_24, plain, (![A_31, B_32]: (~v1_xboole_0(k2_tarski(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.33  tff(c_55, plain, (![A_46]: (~v1_xboole_0(k1_tarski(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_24])).
% 2.09/1.33  tff(c_209, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_195, c_55])).
% 2.09/1.33  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_209])).
% 2.09/1.33  tff(c_215, plain, (k2_mcart_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_90])).
% 2.09/1.33  tff(c_78, plain, (![A_50, B_51]: (k2_mcart_1(k4_tarski(A_50, B_51))=B_51)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.33  tff(c_87, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_42, c_78])).
% 2.09/1.33  tff(c_221, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_215, c_87])).
% 2.09/1.33  tff(c_226, plain, (k4_tarski('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_221, c_42])).
% 2.09/1.33  tff(c_272, plain, (![A_94, B_95]: (k2_zfmisc_1(k1_tarski(A_94), k1_tarski(B_95))=k1_tarski(k4_tarski(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.33  tff(c_26, plain, (![A_33, B_34]: (k2_zfmisc_1(A_33, k1_tarski(B_34))!=k1_xboole_0 | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.33  tff(c_297, plain, (![A_98, B_99]: (k1_tarski(k4_tarski(A_98, B_99))!=k1_xboole_0 | k1_tarski(A_98)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_272, c_26])).
% 2.09/1.33  tff(c_300, plain, (k1_tarski('#skF_1')!=k1_xboole_0 | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_226, c_297])).
% 2.09/1.33  tff(c_301, plain, (k1_tarski('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_300])).
% 2.09/1.33  tff(c_30, plain, (![A_35, B_36]: (~r1_tarski(A_35, k2_zfmisc_1(B_36, A_35)) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.09/1.33  tff(c_316, plain, (![B_106, A_107]: (~r1_tarski(k1_tarski(B_106), k1_tarski(k4_tarski(A_107, B_106))) | k1_tarski(B_106)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_272, c_30])).
% 2.09/1.33  tff(c_319, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1')) | k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_226, c_316])).
% 2.09/1.33  tff(c_321, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_319])).
% 2.09/1.33  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_301, c_321])).
% 2.09/1.33  tff(c_324, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_300])).
% 2.09/1.33  tff(c_338, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_324, c_55])).
% 2.09/1.33  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_338])).
% 2.09/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.33  
% 2.09/1.33  Inference rules
% 2.09/1.33  ----------------------
% 2.09/1.33  #Ref     : 0
% 2.09/1.33  #Sup     : 80
% 2.09/1.33  #Fact    : 0
% 2.09/1.33  #Define  : 0
% 2.09/1.33  #Split   : 4
% 2.09/1.33  #Chain   : 0
% 2.09/1.33  #Close   : 0
% 2.09/1.33  
% 2.09/1.33  Ordering : KBO
% 2.09/1.33  
% 2.09/1.33  Simplification rules
% 2.09/1.33  ----------------------
% 2.09/1.33  #Subsume      : 1
% 2.09/1.33  #Demod        : 16
% 2.09/1.33  #Tautology    : 52
% 2.09/1.33  #SimpNegUnit  : 3
% 2.09/1.33  #BackRed      : 4
% 2.09/1.33  
% 2.09/1.33  #Partial instantiations: 0
% 2.09/1.33  #Strategies tried      : 1
% 2.09/1.33  
% 2.09/1.33  Timing (in seconds)
% 2.09/1.33  ----------------------
% 2.36/1.33  Preprocessing        : 0.33
% 2.36/1.33  Parsing              : 0.18
% 2.36/1.33  CNF conversion       : 0.02
% 2.36/1.33  Main loop            : 0.19
% 2.36/1.33  Inferencing          : 0.07
% 2.36/1.33  Reduction            : 0.06
% 2.36/1.33  Demodulation         : 0.04
% 2.36/1.33  BG Simplification    : 0.01
% 2.36/1.33  Subsumption          : 0.03
% 2.36/1.33  Abstraction          : 0.01
% 2.36/1.33  MUC search           : 0.00
% 2.36/1.33  Cooper               : 0.00
% 2.36/1.33  Total                : 0.55
% 2.36/1.33  Index Insertion      : 0.00
% 2.36/1.33  Index Deletion       : 0.00
% 2.36/1.33  Index Matching       : 0.00
% 2.36/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
