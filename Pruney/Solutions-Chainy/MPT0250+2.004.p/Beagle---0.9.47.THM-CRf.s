%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:32 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   55 (  79 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  77 expanded)
%              Number of equality atoms :   27 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_68,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_58,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_224,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    ! [E_23,A_17,B_18] : r2_hidden(E_23,k1_enumset1(A_17,B_18,E_23)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_242,plain,(
    ! [B_63,A_64] : r2_hidden(B_63,k2_tarski(A_64,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_36])).

tff(c_251,plain,(
    ! [A_24] : r2_hidden(A_24,k1_tarski(A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_242])).

tff(c_32,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_183,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_327,plain,(
    ! [B_73,A_74] : k3_tarski(k2_tarski(B_73,A_74)) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_183])).

tff(c_66,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_333,plain,(
    ! [B_73,A_74] : k2_xboole_0(B_73,A_74) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_66])).

tff(c_30,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_152,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = A_13 ),
    inference(resolution,[status(thm)],[c_30,c_152])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_162,plain,(
    k3_xboole_0(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') = k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_152])).

tff(c_276,plain,(
    k3_xboole_0('#skF_6',k2_xboole_0(k1_tarski('#skF_5'),'#skF_6')) = k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_162])).

tff(c_499,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_163,c_333,c_276])).

tff(c_355,plain,(
    ! [B_75,A_76] : k2_xboole_0(B_75,A_76) = k2_xboole_0(A_76,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_66])).

tff(c_370,plain,(
    ! [A_76,B_75] : k3_xboole_0(A_76,k2_xboole_0(B_75,A_76)) = A_76 ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_163])).

tff(c_505,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_370])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_574,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,'#skF_6')
      | ~ r2_hidden(D_89,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_6])).

tff(c_578,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_251,c_574])).

tff(c_582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:52:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.35  
% 2.48/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.35  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.48/1.35  
% 2.48/1.35  %Foreground sorts:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Background operators:
% 2.48/1.35  
% 2.48/1.35  
% 2.48/1.35  %Foreground operators:
% 2.48/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.48/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.48/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.48/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.35  
% 2.48/1.36  tff(f_80, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.48/1.36  tff(f_67, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.48/1.36  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.48/1.36  tff(f_65, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.48/1.36  tff(f_50, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.48/1.36  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.48/1.36  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.48/1.36  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.48/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.48/1.36  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.48/1.36  tff(c_68, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.48/1.36  tff(c_58, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.48/1.36  tff(c_224, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.48/1.36  tff(c_36, plain, (![E_23, A_17, B_18]: (r2_hidden(E_23, k1_enumset1(A_17, B_18, E_23)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.36  tff(c_242, plain, (![B_63, A_64]: (r2_hidden(B_63, k2_tarski(A_64, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_36])).
% 2.48/1.36  tff(c_251, plain, (![A_24]: (r2_hidden(A_24, k1_tarski(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_242])).
% 2.48/1.36  tff(c_32, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.48/1.36  tff(c_183, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.36  tff(c_327, plain, (![B_73, A_74]: (k3_tarski(k2_tarski(B_73, A_74))=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_32, c_183])).
% 2.48/1.36  tff(c_66, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.48/1.36  tff(c_333, plain, (![B_73, A_74]: (k2_xboole_0(B_73, A_74)=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_327, c_66])).
% 2.48/1.36  tff(c_30, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.48/1.36  tff(c_152, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.48/1.36  tff(c_163, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k2_xboole_0(A_13, B_14))=A_13)), inference(resolution, [status(thm)], [c_30, c_152])).
% 2.48/1.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.36  tff(c_70, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.48/1.36  tff(c_162, plain, (k3_xboole_0(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')=k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_70, c_152])).
% 2.48/1.36  tff(c_276, plain, (k3_xboole_0('#skF_6', k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'))=k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2, c_162])).
% 2.48/1.36  tff(c_499, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_163, c_333, c_276])).
% 2.48/1.36  tff(c_355, plain, (![B_75, A_76]: (k2_xboole_0(B_75, A_76)=k2_xboole_0(A_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_327, c_66])).
% 2.48/1.36  tff(c_370, plain, (![A_76, B_75]: (k3_xboole_0(A_76, k2_xboole_0(B_75, A_76))=A_76)), inference(superposition, [status(thm), theory('equality')], [c_355, c_163])).
% 2.48/1.36  tff(c_505, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_499, c_370])).
% 2.48/1.36  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.48/1.36  tff(c_574, plain, (![D_89]: (r2_hidden(D_89, '#skF_6') | ~r2_hidden(D_89, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_505, c_6])).
% 2.48/1.36  tff(c_578, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_251, c_574])).
% 2.48/1.36  tff(c_582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_578])).
% 2.48/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.36  
% 2.48/1.36  Inference rules
% 2.48/1.36  ----------------------
% 2.48/1.36  #Ref     : 0
% 2.48/1.36  #Sup     : 130
% 2.48/1.36  #Fact    : 0
% 2.48/1.36  #Define  : 0
% 2.48/1.36  #Split   : 0
% 2.48/1.36  #Chain   : 0
% 2.48/1.36  #Close   : 0
% 2.48/1.36  
% 2.48/1.36  Ordering : KBO
% 2.48/1.36  
% 2.48/1.36  Simplification rules
% 2.48/1.36  ----------------------
% 2.48/1.36  #Subsume      : 4
% 2.48/1.36  #Demod        : 43
% 2.48/1.36  #Tautology    : 96
% 2.48/1.36  #SimpNegUnit  : 1
% 2.48/1.36  #BackRed      : 3
% 2.48/1.36  
% 2.48/1.36  #Partial instantiations: 0
% 2.48/1.36  #Strategies tried      : 1
% 2.48/1.36  
% 2.48/1.36  Timing (in seconds)
% 2.48/1.36  ----------------------
% 2.48/1.37  Preprocessing        : 0.33
% 2.48/1.37  Parsing              : 0.17
% 2.48/1.37  CNF conversion       : 0.02
% 2.48/1.37  Main loop            : 0.27
% 2.48/1.37  Inferencing          : 0.08
% 2.48/1.37  Reduction            : 0.10
% 2.48/1.37  Demodulation         : 0.08
% 2.48/1.37  BG Simplification    : 0.02
% 2.48/1.37  Subsumption          : 0.05
% 2.48/1.37  Abstraction          : 0.02
% 2.48/1.37  MUC search           : 0.00
% 2.48/1.37  Cooper               : 0.00
% 2.48/1.37  Total                : 0.63
% 2.48/1.37  Index Insertion      : 0.00
% 2.48/1.37  Index Deletion       : 0.00
% 2.48/1.37  Index Matching       : 0.00
% 2.48/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
