%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:56 EST 2020

% Result     : Theorem 4.53s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :   69 (  84 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 (  82 expanded)
%              Number of equality atoms :   36 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_93,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_95,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_68,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    ! [A_25] : k2_xboole_0(A_25,k1_xboole_0) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_755,plain,(
    ! [A_114,B_115] : k2_xboole_0(k3_xboole_0(A_114,B_115),k4_xboole_0(A_114,B_115)) = A_114 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_95,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_34,B_35] : r1_tarski(A_34,k2_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_110,plain,(
    ! [A_56,B_55] : r1_tarski(A_56,k2_xboole_0(B_55,A_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_50])).

tff(c_834,plain,(
    ! [A_118,B_119] : r1_tarski(k4_xboole_0(A_118,B_119),A_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_110])).

tff(c_148,plain,(
    ! [A_57] : k2_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_40])).

tff(c_160,plain,(
    ! [A_57] : r1_tarski(k1_xboole_0,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_50])).

tff(c_521,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ r1_tarski(B_96,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_537,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ r1_tarski(A_57,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_160,c_521])).

tff(c_847,plain,(
    ! [B_119] : k4_xboole_0(k1_xboole_0,B_119) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_834,c_537])).

tff(c_117,plain,(
    ! [A_56] : k2_xboole_0(k1_xboole_0,A_56) = A_56 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_40])).

tff(c_1022,plain,(
    ! [A_123,B_124] : k4_xboole_0(k2_xboole_0(A_123,B_124),B_124) = k4_xboole_0(A_123,B_124) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1066,plain,(
    ! [A_56] : k4_xboole_0(k1_xboole_0,A_56) = k4_xboole_0(A_56,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_1022])).

tff(c_1085,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_1066])).

tff(c_36,plain,(
    ! [B_22] : r1_tarski(B_22,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_278,plain,(
    ! [A_69,B_70] :
      ( k3_xboole_0(A_69,B_70) = A_69
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_294,plain,(
    ! [B_22] : k3_xboole_0(B_22,B_22) = B_22 ),
    inference(resolution,[status(thm)],[c_36,c_278])).

tff(c_1152,plain,(
    ! [A_127,B_128] : k5_xboole_0(A_127,k3_xboole_0(A_127,B_128)) = k4_xboole_0(A_127,B_128) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1170,plain,(
    ! [B_22] : k5_xboole_0(B_22,B_22) = k4_xboole_0(B_22,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_1152])).

tff(c_1174,plain,(
    ! [B_22] : k5_xboole_0(B_22,B_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_1170])).

tff(c_372,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_tarski(A_76),B_77)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3649,plain,(
    ! [A_256,B_257] :
      ( k3_xboole_0(k1_tarski(A_256),B_257) = k1_tarski(A_256)
      | ~ r2_hidden(A_256,B_257) ) ),
    inference(resolution,[status(thm)],[c_372,c_42])).

tff(c_38,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3686,plain,(
    ! [A_256,B_257] :
      ( k5_xboole_0(k1_tarski(A_256),k1_tarski(A_256)) = k4_xboole_0(k1_tarski(A_256),B_257)
      | ~ r2_hidden(A_256,B_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3649,c_38])).

tff(c_3803,plain,(
    ! [A_260,B_261] :
      ( k4_xboole_0(k1_tarski(A_260),B_261) = k1_xboole_0
      | ~ r2_hidden(A_260,B_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1174,c_3686])).

tff(c_44,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k4_xboole_0(B_29,A_28)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3852,plain,(
    ! [B_261,A_260] :
      ( k2_xboole_0(B_261,k1_tarski(A_260)) = k2_xboole_0(B_261,k1_xboole_0)
      | ~ r2_hidden(A_260,B_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3803,c_44])).

tff(c_4083,plain,(
    ! [B_264,A_265] :
      ( k2_xboole_0(B_264,k1_tarski(A_265)) = B_264
      | ~ r2_hidden(A_265,B_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3852])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_70,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_4187,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4083,c_70])).

tff(c_4236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.53/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.84  
% 4.53/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 4.53/1.84  
% 4.53/1.84  %Foreground sorts:
% 4.53/1.84  
% 4.53/1.84  
% 4.53/1.84  %Background operators:
% 4.53/1.84  
% 4.53/1.84  
% 4.53/1.84  %Foreground operators:
% 4.53/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.53/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.53/1.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.53/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.53/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.53/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.53/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.53/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.53/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.53/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.53/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.53/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.53/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.53/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.53/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.53/1.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.53/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.53/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.53/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.53/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.53/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.53/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.53/1.84  
% 4.53/1.85  tff(f_114, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 4.53/1.85  tff(f_83, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.53/1.85  tff(f_93, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.53/1.85  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.53/1.85  tff(f_95, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.53/1.85  tff(f_79, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.53/1.85  tff(f_91, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.53/1.85  tff(f_87, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.53/1.85  tff(f_81, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.53/1.85  tff(f_107, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.53/1.85  tff(f_89, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.53/1.85  tff(c_68, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.53/1.85  tff(c_40, plain, (![A_25]: (k2_xboole_0(A_25, k1_xboole_0)=A_25)), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.53/1.85  tff(c_755, plain, (![A_114, B_115]: (k2_xboole_0(k3_xboole_0(A_114, B_115), k4_xboole_0(A_114, B_115))=A_114)), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.53/1.85  tff(c_95, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.53/1.85  tff(c_50, plain, (![A_34, B_35]: (r1_tarski(A_34, k2_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.53/1.85  tff(c_110, plain, (![A_56, B_55]: (r1_tarski(A_56, k2_xboole_0(B_55, A_56)))), inference(superposition, [status(thm), theory('equality')], [c_95, c_50])).
% 4.53/1.85  tff(c_834, plain, (![A_118, B_119]: (r1_tarski(k4_xboole_0(A_118, B_119), A_118))), inference(superposition, [status(thm), theory('equality')], [c_755, c_110])).
% 4.53/1.85  tff(c_148, plain, (![A_57]: (k2_xboole_0(k1_xboole_0, A_57)=A_57)), inference(superposition, [status(thm), theory('equality')], [c_95, c_40])).
% 4.53/1.85  tff(c_160, plain, (![A_57]: (r1_tarski(k1_xboole_0, A_57))), inference(superposition, [status(thm), theory('equality')], [c_148, c_50])).
% 4.53/1.85  tff(c_521, plain, (![B_96, A_97]: (B_96=A_97 | ~r1_tarski(B_96, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.53/1.85  tff(c_537, plain, (![A_57]: (k1_xboole_0=A_57 | ~r1_tarski(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_160, c_521])).
% 4.53/1.85  tff(c_847, plain, (![B_119]: (k4_xboole_0(k1_xboole_0, B_119)=k1_xboole_0)), inference(resolution, [status(thm)], [c_834, c_537])).
% 4.53/1.85  tff(c_117, plain, (![A_56]: (k2_xboole_0(k1_xboole_0, A_56)=A_56)), inference(superposition, [status(thm), theory('equality')], [c_95, c_40])).
% 4.53/1.85  tff(c_1022, plain, (![A_123, B_124]: (k4_xboole_0(k2_xboole_0(A_123, B_124), B_124)=k4_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.53/1.85  tff(c_1066, plain, (![A_56]: (k4_xboole_0(k1_xboole_0, A_56)=k4_xboole_0(A_56, A_56))), inference(superposition, [status(thm), theory('equality')], [c_117, c_1022])).
% 4.53/1.85  tff(c_1085, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_847, c_1066])).
% 4.53/1.85  tff(c_36, plain, (![B_22]: (r1_tarski(B_22, B_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.53/1.85  tff(c_278, plain, (![A_69, B_70]: (k3_xboole_0(A_69, B_70)=A_69 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.53/1.85  tff(c_294, plain, (![B_22]: (k3_xboole_0(B_22, B_22)=B_22)), inference(resolution, [status(thm)], [c_36, c_278])).
% 4.53/1.85  tff(c_1152, plain, (![A_127, B_128]: (k5_xboole_0(A_127, k3_xboole_0(A_127, B_128))=k4_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.53/1.85  tff(c_1170, plain, (![B_22]: (k5_xboole_0(B_22, B_22)=k4_xboole_0(B_22, B_22))), inference(superposition, [status(thm), theory('equality')], [c_294, c_1152])).
% 4.53/1.85  tff(c_1174, plain, (![B_22]: (k5_xboole_0(B_22, B_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_1170])).
% 4.53/1.85  tff(c_372, plain, (![A_76, B_77]: (r1_tarski(k1_tarski(A_76), B_77) | ~r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.53/1.85  tff(c_42, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.53/1.85  tff(c_3649, plain, (![A_256, B_257]: (k3_xboole_0(k1_tarski(A_256), B_257)=k1_tarski(A_256) | ~r2_hidden(A_256, B_257))), inference(resolution, [status(thm)], [c_372, c_42])).
% 4.53/1.85  tff(c_38, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.53/1.85  tff(c_3686, plain, (![A_256, B_257]: (k5_xboole_0(k1_tarski(A_256), k1_tarski(A_256))=k4_xboole_0(k1_tarski(A_256), B_257) | ~r2_hidden(A_256, B_257))), inference(superposition, [status(thm), theory('equality')], [c_3649, c_38])).
% 4.53/1.85  tff(c_3803, plain, (![A_260, B_261]: (k4_xboole_0(k1_tarski(A_260), B_261)=k1_xboole_0 | ~r2_hidden(A_260, B_261))), inference(demodulation, [status(thm), theory('equality')], [c_1174, c_3686])).
% 4.53/1.85  tff(c_44, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k4_xboole_0(B_29, A_28))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.53/1.85  tff(c_3852, plain, (![B_261, A_260]: (k2_xboole_0(B_261, k1_tarski(A_260))=k2_xboole_0(B_261, k1_xboole_0) | ~r2_hidden(A_260, B_261))), inference(superposition, [status(thm), theory('equality')], [c_3803, c_44])).
% 4.53/1.85  tff(c_4083, plain, (![B_264, A_265]: (k2_xboole_0(B_264, k1_tarski(A_265))=B_264 | ~r2_hidden(A_265, B_264))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3852])).
% 4.53/1.85  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.53/1.85  tff(c_66, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.53/1.85  tff(c_70, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_66])).
% 4.53/1.85  tff(c_4187, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4083, c_70])).
% 4.53/1.85  tff(c_4236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_4187])).
% 4.53/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.85  
% 4.53/1.85  Inference rules
% 4.53/1.85  ----------------------
% 4.53/1.85  #Ref     : 0
% 4.53/1.85  #Sup     : 1056
% 4.53/1.85  #Fact    : 0
% 4.53/1.85  #Define  : 0
% 4.53/1.85  #Split   : 1
% 4.53/1.85  #Chain   : 0
% 4.53/1.85  #Close   : 0
% 4.53/1.85  
% 4.53/1.85  Ordering : KBO
% 4.53/1.85  
% 4.53/1.85  Simplification rules
% 4.53/1.85  ----------------------
% 4.53/1.85  #Subsume      : 212
% 4.53/1.85  #Demod        : 712
% 4.53/1.85  #Tautology    : 611
% 4.53/1.85  #SimpNegUnit  : 9
% 4.53/1.85  #BackRed      : 10
% 4.53/1.85  
% 4.53/1.85  #Partial instantiations: 0
% 4.53/1.85  #Strategies tried      : 1
% 4.53/1.85  
% 4.53/1.85  Timing (in seconds)
% 4.53/1.85  ----------------------
% 4.53/1.85  Preprocessing        : 0.35
% 4.53/1.85  Parsing              : 0.18
% 4.68/1.85  CNF conversion       : 0.02
% 4.68/1.85  Main loop            : 0.74
% 4.68/1.85  Inferencing          : 0.25
% 4.68/1.85  Reduction            : 0.30
% 4.68/1.85  Demodulation         : 0.24
% 4.68/1.85  BG Simplification    : 0.03
% 4.68/1.85  Subsumption          : 0.12
% 4.68/1.85  Abstraction          : 0.04
% 4.68/1.85  MUC search           : 0.00
% 4.68/1.85  Cooper               : 0.00
% 4.68/1.85  Total                : 1.12
% 4.68/1.85  Index Insertion      : 0.00
% 4.68/1.85  Index Deletion       : 0.00
% 4.68/1.86  Index Matching       : 0.00
% 4.68/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
