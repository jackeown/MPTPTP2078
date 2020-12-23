%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:34 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   55 (  66 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  65 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_68,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_162,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ! [E_21,A_15,C_17] : r2_hidden(E_21,k1_enumset1(A_15,E_21,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_180,plain,(
    ! [A_57,B_58] : r2_hidden(A_57,k2_tarski(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_36])).

tff(c_189,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_180])).

tff(c_28,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_119,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_274,plain,(
    ! [A_70,B_71] : k3_tarski(k2_tarski(A_70,B_71)) = k2_xboole_0(B_71,A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_119])).

tff(c_66,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_283,plain,(
    ! [B_71,A_70] : k2_xboole_0(B_71,A_70) = k2_xboole_0(A_70,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_66])).

tff(c_70,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_304,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k1_tarski('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_70])).

tff(c_432,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(B_84,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_434,plain,
    ( k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_304,c_432])).

tff(c_447,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_434])).

tff(c_305,plain,(
    ! [B_72,A_73] : k2_xboole_0(B_72,A_73) = k2_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_66])).

tff(c_191,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_206,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(resolution,[status(thm)],[c_28,c_191])).

tff(c_323,plain,(
    ! [B_72,A_73] : k3_xboole_0(B_72,k2_xboole_0(A_73,B_72)) = B_72 ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_206])).

tff(c_473,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_323])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_516,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,'#skF_6')
      | ~ r2_hidden(D_89,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_4])).

tff(c_520,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_189,c_516])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.31  
% 2.24/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.31  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.24/1.31  
% 2.24/1.31  %Foreground sorts:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Background operators:
% 2.24/1.31  
% 2.24/1.31  
% 2.24/1.31  %Foreground operators:
% 2.24/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.24/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.24/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.24/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.31  
% 2.24/1.32  tff(f_82, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.24/1.32  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.24/1.32  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.24/1.32  tff(f_63, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.24/1.32  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.24/1.32  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.24/1.32  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.24/1.32  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.24/1.32  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.24/1.32  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.24/1.32  tff(c_68, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.24/1.32  tff(c_56, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.24/1.32  tff(c_162, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.24/1.32  tff(c_36, plain, (![E_21, A_15, C_17]: (r2_hidden(E_21, k1_enumset1(A_15, E_21, C_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.24/1.32  tff(c_180, plain, (![A_57, B_58]: (r2_hidden(A_57, k2_tarski(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_36])).
% 2.24/1.32  tff(c_189, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_180])).
% 2.24/1.32  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.32  tff(c_30, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.24/1.32  tff(c_119, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.24/1.32  tff(c_274, plain, (![A_70, B_71]: (k3_tarski(k2_tarski(A_70, B_71))=k2_xboole_0(B_71, A_70))), inference(superposition, [status(thm), theory('equality')], [c_30, c_119])).
% 2.24/1.32  tff(c_66, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.24/1.32  tff(c_283, plain, (![B_71, A_70]: (k2_xboole_0(B_71, A_70)=k2_xboole_0(A_70, B_71))), inference(superposition, [status(thm), theory('equality')], [c_274, c_66])).
% 2.24/1.32  tff(c_70, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.24/1.32  tff(c_304, plain, (r1_tarski(k2_xboole_0('#skF_6', k1_tarski('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_283, c_70])).
% 2.24/1.32  tff(c_432, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(B_84, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.24/1.32  tff(c_434, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_304, c_432])).
% 2.24/1.32  tff(c_447, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_434])).
% 2.24/1.32  tff(c_305, plain, (![B_72, A_73]: (k2_xboole_0(B_72, A_73)=k2_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_274, c_66])).
% 2.24/1.32  tff(c_191, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.24/1.32  tff(c_206, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(resolution, [status(thm)], [c_28, c_191])).
% 2.24/1.32  tff(c_323, plain, (![B_72, A_73]: (k3_xboole_0(B_72, k2_xboole_0(A_73, B_72))=B_72)), inference(superposition, [status(thm), theory('equality')], [c_305, c_206])).
% 2.24/1.32  tff(c_473, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_447, c_323])).
% 2.24/1.32  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.24/1.32  tff(c_516, plain, (![D_89]: (r2_hidden(D_89, '#skF_6') | ~r2_hidden(D_89, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_473, c_4])).
% 2.24/1.32  tff(c_520, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_189, c_516])).
% 2.24/1.32  tff(c_524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_520])).
% 2.24/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.32  
% 2.24/1.32  Inference rules
% 2.24/1.32  ----------------------
% 2.24/1.32  #Ref     : 0
% 2.24/1.32  #Sup     : 114
% 2.24/1.32  #Fact    : 0
% 2.24/1.32  #Define  : 0
% 2.24/1.32  #Split   : 1
% 2.24/1.32  #Chain   : 0
% 2.24/1.32  #Close   : 0
% 2.24/1.32  
% 2.24/1.32  Ordering : KBO
% 2.24/1.32  
% 2.24/1.32  Simplification rules
% 2.24/1.32  ----------------------
% 2.24/1.32  #Subsume      : 2
% 2.24/1.32  #Demod        : 35
% 2.24/1.32  #Tautology    : 83
% 2.24/1.32  #SimpNegUnit  : 1
% 2.24/1.32  #BackRed      : 4
% 2.24/1.32  
% 2.24/1.32  #Partial instantiations: 0
% 2.24/1.32  #Strategies tried      : 1
% 2.24/1.32  
% 2.24/1.32  Timing (in seconds)
% 2.24/1.32  ----------------------
% 2.55/1.32  Preprocessing        : 0.32
% 2.55/1.32  Parsing              : 0.16
% 2.55/1.32  CNF conversion       : 0.03
% 2.55/1.32  Main loop            : 0.26
% 2.55/1.32  Inferencing          : 0.08
% 2.55/1.32  Reduction            : 0.09
% 2.55/1.32  Demodulation         : 0.07
% 2.55/1.32  BG Simplification    : 0.02
% 2.55/1.32  Subsumption          : 0.05
% 2.55/1.32  Abstraction          : 0.02
% 2.55/1.32  MUC search           : 0.00
% 2.55/1.32  Cooper               : 0.00
% 2.55/1.32  Total                : 0.61
% 2.55/1.33  Index Insertion      : 0.00
% 2.55/1.33  Index Deletion       : 0.00
% 2.55/1.33  Index Matching       : 0.00
% 2.55/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
