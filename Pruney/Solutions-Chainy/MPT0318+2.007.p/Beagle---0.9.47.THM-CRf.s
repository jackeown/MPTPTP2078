%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:03 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 146 expanded)
%              Number of leaves         :   26 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 198 expanded)
%              Number of equality atoms :   44 ( 120 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_58])).

tff(c_46,plain,(
    ! [B_24] : k2_zfmisc_1(k1_xboole_0,B_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    ! [B_24] : k2_zfmisc_1('#skF_2',B_24) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_46])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_65,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_99,plain,
    ( k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')) = '#skF_2'
    | k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_48])).

tff(c_100,plain,(
    k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_42,plain,(
    ! [B_24,A_23] :
      ( k1_xboole_0 = B_24
      | k1_xboole_0 = A_23
      | k2_zfmisc_1(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_157,plain,(
    ! [B_48,A_49] :
      ( B_48 = '#skF_2'
      | A_49 = '#skF_2'
      | k2_zfmisc_1(A_49,B_48) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_62,c_42])).

tff(c_160,plain,
    ( '#skF_5' = '#skF_2'
    | k1_tarski('#skF_6') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_157])).

tff(c_169,plain,(
    k1_tarski('#skF_6') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_160])).

tff(c_34,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_136,plain,(
    ! [A_46,B_47] : k1_enumset1(A_46,A_46,B_47) = k2_tarski(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,(
    ! [E_33,A_34,B_35] : r2_hidden(E_33,k1_enumset1(A_34,B_35,E_33)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_34,B_35,E_33] : ~ v1_xboole_0(k1_enumset1(A_34,B_35,E_33)) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_180,plain,(
    ! [A_50,B_51] : ~ v1_xboole_0(k2_tarski(A_50,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_119])).

tff(c_183,plain,(
    ! [A_52] : ~ v1_xboole_0(k1_tarski(A_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_180])).

tff(c_185,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_183])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_185])).

tff(c_189,plain,(
    k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_251,plain,(
    ! [B_74,A_75] :
      ( B_74 = '#skF_2'
      | A_75 = '#skF_2'
      | k2_zfmisc_1(A_75,B_74) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_62,c_42])).

tff(c_254,plain,
    ( k1_tarski('#skF_6') = '#skF_2'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_251])).

tff(c_263,plain,(
    k1_tarski('#skF_6') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_254])).

tff(c_190,plain,(
    k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_5') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_268,plain,(
    k2_zfmisc_1('#skF_2','#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_190])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.28  %$ r2_hidden > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.07/1.28  
% 2.07/1.28  %Foreground sorts:
% 2.07/1.28  
% 2.07/1.28  
% 2.07/1.28  %Background operators:
% 2.07/1.28  
% 2.07/1.28  
% 2.07/1.28  %Foreground operators:
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.07/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.07/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.07/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.28  
% 2.07/1.29  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.07/1.29  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.07/1.29  tff(f_66, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.07/1.29  tff(f_76, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.07/1.29  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.07/1.29  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.07/1.29  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.07/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.07/1.29  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.29  tff(c_58, plain, (![A_26]: (k1_xboole_0=A_26 | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.29  tff(c_62, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_58])).
% 2.07/1.29  tff(c_46, plain, (![B_24]: (k2_zfmisc_1(k1_xboole_0, B_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.07/1.29  tff(c_70, plain, (![B_24]: (k2_zfmisc_1('#skF_2', B_24)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_46])).
% 2.07/1.29  tff(c_50, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.07/1.29  tff(c_65, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50])).
% 2.07/1.29  tff(c_48, plain, (k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.07/1.29  tff(c_99, plain, (k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))='#skF_2' | k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_48])).
% 2.07/1.29  tff(c_100, plain, (k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_99])).
% 2.07/1.29  tff(c_42, plain, (![B_24, A_23]: (k1_xboole_0=B_24 | k1_xboole_0=A_23 | k2_zfmisc_1(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.07/1.29  tff(c_157, plain, (![B_48, A_49]: (B_48='#skF_2' | A_49='#skF_2' | k2_zfmisc_1(A_49, B_48)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_62, c_42])).
% 2.07/1.29  tff(c_160, plain, ('#skF_5'='#skF_2' | k1_tarski('#skF_6')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_100, c_157])).
% 2.07/1.29  tff(c_169, plain, (k1_tarski('#skF_6')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_65, c_160])).
% 2.07/1.29  tff(c_34, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.07/1.29  tff(c_136, plain, (![A_46, B_47]: (k1_enumset1(A_46, A_46, B_47)=k2_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.29  tff(c_115, plain, (![E_33, A_34, B_35]: (r2_hidden(E_33, k1_enumset1(A_34, B_35, E_33)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.29  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.29  tff(c_119, plain, (![A_34, B_35, E_33]: (~v1_xboole_0(k1_enumset1(A_34, B_35, E_33)))), inference(resolution, [status(thm)], [c_115, c_2])).
% 2.07/1.29  tff(c_180, plain, (![A_50, B_51]: (~v1_xboole_0(k2_tarski(A_50, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_136, c_119])).
% 2.07/1.29  tff(c_183, plain, (![A_52]: (~v1_xboole_0(k1_tarski(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_180])).
% 2.07/1.29  tff(c_185, plain, (~v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_169, c_183])).
% 2.07/1.29  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_185])).
% 2.07/1.29  tff(c_189, plain, (k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))='#skF_2'), inference(splitRight, [status(thm)], [c_99])).
% 2.07/1.29  tff(c_251, plain, (![B_74, A_75]: (B_74='#skF_2' | A_75='#skF_2' | k2_zfmisc_1(A_75, B_74)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_62, c_42])).
% 2.07/1.29  tff(c_254, plain, (k1_tarski('#skF_6')='#skF_2' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_189, c_251])).
% 2.07/1.29  tff(c_263, plain, (k1_tarski('#skF_6')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_65, c_254])).
% 2.07/1.29  tff(c_190, plain, (k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_5')!='#skF_2'), inference(splitRight, [status(thm)], [c_99])).
% 2.07/1.29  tff(c_268, plain, (k2_zfmisc_1('#skF_2', '#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_190])).
% 2.07/1.29  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_268])).
% 2.07/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.29  
% 2.07/1.29  Inference rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Ref     : 0
% 2.07/1.29  #Sup     : 51
% 2.07/1.29  #Fact    : 0
% 2.07/1.29  #Define  : 0
% 2.07/1.29  #Split   : 1
% 2.07/1.29  #Chain   : 0
% 2.07/1.29  #Close   : 0
% 2.07/1.29  
% 2.07/1.29  Ordering : KBO
% 2.07/1.29  
% 2.07/1.29  Simplification rules
% 2.07/1.29  ----------------------
% 2.07/1.29  #Subsume      : 4
% 2.07/1.29  #Demod        : 20
% 2.07/1.29  #Tautology    : 32
% 2.07/1.29  #SimpNegUnit  : 2
% 2.07/1.29  #BackRed      : 6
% 2.07/1.29  
% 2.07/1.29  #Partial instantiations: 0
% 2.07/1.29  #Strategies tried      : 1
% 2.07/1.29  
% 2.07/1.29  Timing (in seconds)
% 2.07/1.29  ----------------------
% 2.07/1.29  Preprocessing        : 0.33
% 2.07/1.29  Parsing              : 0.17
% 2.07/1.29  CNF conversion       : 0.02
% 2.07/1.29  Main loop            : 0.17
% 2.07/1.29  Inferencing          : 0.05
% 2.07/1.29  Reduction            : 0.05
% 2.07/1.29  Demodulation         : 0.04
% 2.07/1.29  BG Simplification    : 0.01
% 2.07/1.29  Subsumption          : 0.03
% 2.07/1.29  Abstraction          : 0.01
% 2.07/1.29  MUC search           : 0.00
% 2.07/1.29  Cooper               : 0.00
% 2.07/1.29  Total                : 0.52
% 2.07/1.29  Index Insertion      : 0.00
% 2.07/1.29  Index Deletion       : 0.00
% 2.07/1.29  Index Matching       : 0.00
% 2.07/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
