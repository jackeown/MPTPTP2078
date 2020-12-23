%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:01 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   52 (  87 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   45 (  87 expanded)
%              Number of equality atoms :   39 (  80 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_46,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [A_36,B_37,C_38] : k2_enumset1(A_36,A_36,B_37,C_38) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_312,plain,(
    ! [A_89,B_90,C_91,D_92] : k2_xboole_0(k2_tarski(A_89,B_90),k2_tarski(C_91,D_92)) = k2_enumset1(A_89,B_90,C_91,D_92) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_321,plain,(
    ! [A_33,C_91,D_92] : k2_xboole_0(k1_tarski(A_33),k2_tarski(C_91,D_92)) = k2_enumset1(A_33,A_33,C_91,D_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_312])).

tff(c_327,plain,(
    ! [A_33,C_91,D_92] : k2_xboole_0(k1_tarski(A_33),k2_tarski(C_91,D_92)) = k1_enumset1(A_33,C_91,D_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_321])).

tff(c_40,plain,(
    ! [A_34,B_35] : k1_enumset1(A_34,A_34,B_35) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_130,plain,(
    ! [A_71,B_72,C_73,D_74] : k2_xboole_0(k1_tarski(A_71),k1_enumset1(B_72,C_73,D_74)) = k2_enumset1(A_71,B_72,C_73,D_74) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_139,plain,(
    ! [A_71,A_34,B_35] : k2_xboole_0(k1_tarski(A_71),k2_tarski(A_34,B_35)) = k2_enumset1(A_71,A_34,A_34,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_130])).

tff(c_461,plain,(
    ! [A_103,A_104,B_105] : k2_enumset1(A_103,A_104,A_104,B_105) = k1_enumset1(A_103,A_104,B_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_139])).

tff(c_142,plain,(
    ! [A_75,A_76,B_77] : k2_xboole_0(k1_tarski(A_75),k2_tarski(A_76,B_77)) = k2_enumset1(A_75,A_76,A_76,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_130])).

tff(c_249,plain,(
    ! [A_87,A_88] : k2_xboole_0(k1_tarski(A_87),k1_tarski(A_88)) = k2_enumset1(A_87,A_88,A_88,A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_142])).

tff(c_48,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_273,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_4','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_48])).

tff(c_474,plain,(
    k1_enumset1('#skF_3','#skF_4','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_273])).

tff(c_8,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_524,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_8])).

tff(c_152,plain,(
    ! [A_76,B_77] : k2_xboole_0(k1_tarski(A_76),k2_tarski(A_76,B_77)) = k1_enumset1(A_76,A_76,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_42])).

tff(c_172,plain,(
    ! [A_78,B_79] : k2_xboole_0(k1_tarski(A_78),k2_tarski(A_78,B_79)) = k2_tarski(A_78,B_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_152])).

tff(c_188,plain,(
    ! [A_33] : k2_xboole_0(k1_tarski(A_33),k1_tarski(A_33)) = k2_tarski(A_33,A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_172])).

tff(c_191,plain,(
    ! [A_33] : k2_xboole_0(k1_tarski(A_33),k1_tarski(A_33)) = k1_tarski(A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_188])).

tff(c_329,plain,(
    ! [A_93] : k2_enumset1(A_93,A_93,A_93,A_93) = k1_tarski(A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_249])).

tff(c_372,plain,(
    ! [A_94] : k1_enumset1(A_94,A_94,A_94) = k1_tarski(A_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_42])).

tff(c_6,plain,(
    ! [E_11,C_7,B_6,A_5] :
      ( E_11 = C_7
      | E_11 = B_6
      | E_11 = A_5
      | ~ r2_hidden(E_11,k1_enumset1(A_5,B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_743,plain,(
    ! [E_123,A_124] :
      ( E_123 = A_124
      | E_123 = A_124
      | E_123 = A_124
      | ~ r2_hidden(E_123,k1_tarski(A_124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_6])).

tff(c_746,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_524,c_743])).

tff(c_753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_46,c_746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.36  
% 2.63/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.37  %$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.63/1.37  
% 2.63/1.37  %Foreground sorts:
% 2.63/1.37  
% 2.63/1.37  
% 2.63/1.37  %Background operators:
% 2.63/1.37  
% 2.63/1.37  
% 2.63/1.37  %Foreground operators:
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.63/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.63/1.37  
% 2.63/1.38  tff(f_65, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.63/1.38  tff(f_58, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.63/1.38  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.63/1.38  tff(f_46, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.63/1.38  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.63/1.38  tff(f_50, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.63/1.38  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.63/1.38  tff(c_46, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.38  tff(c_42, plain, (![A_36, B_37, C_38]: (k2_enumset1(A_36, A_36, B_37, C_38)=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.63/1.38  tff(c_38, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.63/1.38  tff(c_312, plain, (![A_89, B_90, C_91, D_92]: (k2_xboole_0(k2_tarski(A_89, B_90), k2_tarski(C_91, D_92))=k2_enumset1(A_89, B_90, C_91, D_92))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.63/1.38  tff(c_321, plain, (![A_33, C_91, D_92]: (k2_xboole_0(k1_tarski(A_33), k2_tarski(C_91, D_92))=k2_enumset1(A_33, A_33, C_91, D_92))), inference(superposition, [status(thm), theory('equality')], [c_38, c_312])).
% 2.63/1.38  tff(c_327, plain, (![A_33, C_91, D_92]: (k2_xboole_0(k1_tarski(A_33), k2_tarski(C_91, D_92))=k1_enumset1(A_33, C_91, D_92))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_321])).
% 2.63/1.38  tff(c_40, plain, (![A_34, B_35]: (k1_enumset1(A_34, A_34, B_35)=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.63/1.38  tff(c_130, plain, (![A_71, B_72, C_73, D_74]: (k2_xboole_0(k1_tarski(A_71), k1_enumset1(B_72, C_73, D_74))=k2_enumset1(A_71, B_72, C_73, D_74))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.63/1.38  tff(c_139, plain, (![A_71, A_34, B_35]: (k2_xboole_0(k1_tarski(A_71), k2_tarski(A_34, B_35))=k2_enumset1(A_71, A_34, A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_40, c_130])).
% 2.63/1.38  tff(c_461, plain, (![A_103, A_104, B_105]: (k2_enumset1(A_103, A_104, A_104, B_105)=k1_enumset1(A_103, A_104, B_105))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_139])).
% 2.63/1.38  tff(c_142, plain, (![A_75, A_76, B_77]: (k2_xboole_0(k1_tarski(A_75), k2_tarski(A_76, B_77))=k2_enumset1(A_75, A_76, A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_40, c_130])).
% 2.63/1.38  tff(c_249, plain, (![A_87, A_88]: (k2_xboole_0(k1_tarski(A_87), k1_tarski(A_88))=k2_enumset1(A_87, A_88, A_88, A_88))), inference(superposition, [status(thm), theory('equality')], [c_38, c_142])).
% 2.63/1.38  tff(c_48, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.63/1.38  tff(c_273, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_4', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_249, c_48])).
% 2.63/1.38  tff(c_474, plain, (k1_enumset1('#skF_3', '#skF_4', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_461, c_273])).
% 2.63/1.38  tff(c_8, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.63/1.38  tff(c_524, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_474, c_8])).
% 2.63/1.38  tff(c_152, plain, (![A_76, B_77]: (k2_xboole_0(k1_tarski(A_76), k2_tarski(A_76, B_77))=k1_enumset1(A_76, A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_142, c_42])).
% 2.63/1.38  tff(c_172, plain, (![A_78, B_79]: (k2_xboole_0(k1_tarski(A_78), k2_tarski(A_78, B_79))=k2_tarski(A_78, B_79))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_152])).
% 2.63/1.38  tff(c_188, plain, (![A_33]: (k2_xboole_0(k1_tarski(A_33), k1_tarski(A_33))=k2_tarski(A_33, A_33))), inference(superposition, [status(thm), theory('equality')], [c_38, c_172])).
% 2.63/1.38  tff(c_191, plain, (![A_33]: (k2_xboole_0(k1_tarski(A_33), k1_tarski(A_33))=k1_tarski(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_188])).
% 2.63/1.38  tff(c_329, plain, (![A_93]: (k2_enumset1(A_93, A_93, A_93, A_93)=k1_tarski(A_93))), inference(superposition, [status(thm), theory('equality')], [c_191, c_249])).
% 2.63/1.38  tff(c_372, plain, (![A_94]: (k1_enumset1(A_94, A_94, A_94)=k1_tarski(A_94))), inference(superposition, [status(thm), theory('equality')], [c_329, c_42])).
% 2.63/1.38  tff(c_6, plain, (![E_11, C_7, B_6, A_5]: (E_11=C_7 | E_11=B_6 | E_11=A_5 | ~r2_hidden(E_11, k1_enumset1(A_5, B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.63/1.38  tff(c_743, plain, (![E_123, A_124]: (E_123=A_124 | E_123=A_124 | E_123=A_124 | ~r2_hidden(E_123, k1_tarski(A_124)))), inference(superposition, [status(thm), theory('equality')], [c_372, c_6])).
% 2.63/1.38  tff(c_746, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_524, c_743])).
% 2.63/1.38  tff(c_753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_46, c_746])).
% 2.63/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.38  
% 2.63/1.38  Inference rules
% 2.63/1.38  ----------------------
% 2.63/1.38  #Ref     : 0
% 2.63/1.38  #Sup     : 167
% 2.63/1.38  #Fact    : 0
% 2.63/1.38  #Define  : 0
% 2.63/1.38  #Split   : 0
% 2.63/1.38  #Chain   : 0
% 2.63/1.38  #Close   : 0
% 2.63/1.38  
% 2.63/1.38  Ordering : KBO
% 2.63/1.38  
% 2.63/1.38  Simplification rules
% 2.63/1.38  ----------------------
% 2.63/1.38  #Subsume      : 3
% 2.63/1.38  #Demod        : 99
% 2.63/1.38  #Tautology    : 128
% 2.63/1.38  #SimpNegUnit  : 3
% 2.63/1.38  #BackRed      : 2
% 2.63/1.38  
% 2.63/1.38  #Partial instantiations: 0
% 2.63/1.38  #Strategies tried      : 1
% 2.63/1.38  
% 2.63/1.38  Timing (in seconds)
% 2.63/1.38  ----------------------
% 2.80/1.38  Preprocessing        : 0.32
% 2.80/1.38  Parsing              : 0.16
% 2.80/1.38  CNF conversion       : 0.02
% 2.80/1.38  Main loop            : 0.29
% 2.80/1.38  Inferencing          : 0.12
% 2.80/1.38  Reduction            : 0.10
% 2.80/1.38  Demodulation         : 0.08
% 2.80/1.38  BG Simplification    : 0.02
% 2.80/1.38  Subsumption          : 0.04
% 2.80/1.38  Abstraction          : 0.02
% 2.80/1.38  MUC search           : 0.00
% 2.80/1.38  Cooper               : 0.00
% 2.80/1.38  Total                : 0.65
% 2.80/1.38  Index Insertion      : 0.00
% 2.80/1.38  Index Deletion       : 0.00
% 2.80/1.38  Index Matching       : 0.00
% 2.80/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
