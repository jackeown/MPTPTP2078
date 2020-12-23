%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:02 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   50 (  69 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  72 expanded)
%              Number of equality atoms :   38 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k4_enumset1(A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_42,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_176,plain,(
    ! [D_73,E_74,B_72,C_71,A_75] : k4_enumset1(A_75,A_75,B_72,C_71,D_73,E_74) = k3_enumset1(A_75,B_72,C_71,D_73,E_74) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [A_35,B_36] : k4_enumset1(A_35,A_35,A_35,A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_187,plain,(
    ! [D_73,E_74] : k3_enumset1(D_73,D_73,D_73,D_73,E_74) = k2_tarski(D_73,E_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_40])).

tff(c_257,plain,(
    ! [F_97,E_94,A_95,D_96,B_93,C_98] : k2_xboole_0(k3_enumset1(A_95,B_93,C_98,D_96,E_94),k1_tarski(F_97)) = k4_enumset1(A_95,B_93,C_98,D_96,E_94,F_97) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_273,plain,(
    ! [D_99,E_100,F_101] : k4_enumset1(D_99,D_99,D_99,D_99,E_100,F_101) = k2_xboole_0(k2_tarski(D_99,E_100),k1_tarski(F_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_257])).

tff(c_289,plain,(
    ! [E_100,F_101] : k2_xboole_0(k2_tarski(E_100,E_100),k1_tarski(F_101)) = k2_tarski(E_100,F_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_40])).

tff(c_320,plain,(
    ! [E_106,F_107] : k2_xboole_0(k1_tarski(E_106),k1_tarski(F_107)) = k2_tarski(E_106,F_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_289])).

tff(c_44,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_326,plain,(
    k2_tarski('#skF_3','#skF_4') = k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_44])).

tff(c_94,plain,(
    ! [A_54,B_55,C_56,D_57] : k4_enumset1(A_54,A_54,A_54,B_55,C_56,D_57) = k2_enumset1(A_54,B_55,C_56,D_57) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_110,plain,(
    ! [C_58,D_59] : k2_enumset1(C_58,C_58,C_58,D_59) = k2_tarski(C_58,D_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_40])).

tff(c_32,plain,(
    ! [A_17,B_18,C_19] : k2_enumset1(A_17,A_17,B_18,C_19) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_126,plain,(
    ! [C_60,D_61] : k1_enumset1(C_60,C_60,D_61) = k2_tarski(C_60,D_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_32])).

tff(c_6,plain,(
    ! [E_9,A_3,B_4] : r2_hidden(E_9,k1_enumset1(A_3,B_4,E_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_132,plain,(
    ! [D_61,C_60] : r2_hidden(D_61,k2_tarski(C_60,D_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_6])).

tff(c_347,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_132])).

tff(c_116,plain,(
    ! [C_58,D_59] : k1_enumset1(C_58,C_58,D_59) = k2_tarski(C_58,D_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_32])).

tff(c_154,plain,(
    ! [E_67,C_68,B_69,A_70] :
      ( E_67 = C_68
      | E_67 = B_69
      | E_67 = A_70
      | ~ r2_hidden(E_67,k1_enumset1(A_70,B_69,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_228,plain,(
    ! [E_82,D_83,C_84] :
      ( E_82 = D_83
      | E_82 = C_84
      | E_82 = C_84
      | ~ r2_hidden(E_82,k2_tarski(C_84,D_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_154])).

tff(c_237,plain,(
    ! [E_82,A_16] :
      ( E_82 = A_16
      | E_82 = A_16
      | E_82 = A_16
      | ~ r2_hidden(E_82,k1_tarski(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_228])).

tff(c_355,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_347,c_237])).

tff(c_359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_42,c_355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.28  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.14/1.28  
% 2.14/1.28  %Foreground sorts:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Background operators:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Foreground operators:
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.14/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.14/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.14/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.14/1.28  
% 2.14/1.29  tff(f_61, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 2.14/1.29  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.14/1.29  tff(f_50, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.14/1.29  tff(f_56, axiom, (![A, B]: (k4_enumset1(A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_enumset1)).
% 2.14/1.29  tff(f_44, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.14/1.29  tff(f_54, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 2.14/1.29  tff(f_48, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.14/1.29  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.14/1.29  tff(c_42, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.29  tff(c_30, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.29  tff(c_176, plain, (![D_73, E_74, B_72, C_71, A_75]: (k4_enumset1(A_75, A_75, B_72, C_71, D_73, E_74)=k3_enumset1(A_75, B_72, C_71, D_73, E_74))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.29  tff(c_40, plain, (![A_35, B_36]: (k4_enumset1(A_35, A_35, A_35, A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.29  tff(c_187, plain, (![D_73, E_74]: (k3_enumset1(D_73, D_73, D_73, D_73, E_74)=k2_tarski(D_73, E_74))), inference(superposition, [status(thm), theory('equality')], [c_176, c_40])).
% 2.14/1.29  tff(c_257, plain, (![F_97, E_94, A_95, D_96, B_93, C_98]: (k2_xboole_0(k3_enumset1(A_95, B_93, C_98, D_96, E_94), k1_tarski(F_97))=k4_enumset1(A_95, B_93, C_98, D_96, E_94, F_97))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.14/1.29  tff(c_273, plain, (![D_99, E_100, F_101]: (k4_enumset1(D_99, D_99, D_99, D_99, E_100, F_101)=k2_xboole_0(k2_tarski(D_99, E_100), k1_tarski(F_101)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_257])).
% 2.14/1.29  tff(c_289, plain, (![E_100, F_101]: (k2_xboole_0(k2_tarski(E_100, E_100), k1_tarski(F_101))=k2_tarski(E_100, F_101))), inference(superposition, [status(thm), theory('equality')], [c_273, c_40])).
% 2.14/1.29  tff(c_320, plain, (![E_106, F_107]: (k2_xboole_0(k1_tarski(E_106), k1_tarski(F_107))=k2_tarski(E_106, F_107))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_289])).
% 2.14/1.29  tff(c_44, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.29  tff(c_326, plain, (k2_tarski('#skF_3', '#skF_4')=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_320, c_44])).
% 2.14/1.29  tff(c_94, plain, (![A_54, B_55, C_56, D_57]: (k4_enumset1(A_54, A_54, A_54, B_55, C_56, D_57)=k2_enumset1(A_54, B_55, C_56, D_57))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.29  tff(c_110, plain, (![C_58, D_59]: (k2_enumset1(C_58, C_58, C_58, D_59)=k2_tarski(C_58, D_59))), inference(superposition, [status(thm), theory('equality')], [c_94, c_40])).
% 2.14/1.29  tff(c_32, plain, (![A_17, B_18, C_19]: (k2_enumset1(A_17, A_17, B_18, C_19)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.29  tff(c_126, plain, (![C_60, D_61]: (k1_enumset1(C_60, C_60, D_61)=k2_tarski(C_60, D_61))), inference(superposition, [status(thm), theory('equality')], [c_110, c_32])).
% 2.14/1.29  tff(c_6, plain, (![E_9, A_3, B_4]: (r2_hidden(E_9, k1_enumset1(A_3, B_4, E_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.14/1.29  tff(c_132, plain, (![D_61, C_60]: (r2_hidden(D_61, k2_tarski(C_60, D_61)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_6])).
% 2.14/1.29  tff(c_347, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_326, c_132])).
% 2.14/1.29  tff(c_116, plain, (![C_58, D_59]: (k1_enumset1(C_58, C_58, D_59)=k2_tarski(C_58, D_59))), inference(superposition, [status(thm), theory('equality')], [c_110, c_32])).
% 2.14/1.29  tff(c_154, plain, (![E_67, C_68, B_69, A_70]: (E_67=C_68 | E_67=B_69 | E_67=A_70 | ~r2_hidden(E_67, k1_enumset1(A_70, B_69, C_68)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.14/1.29  tff(c_228, plain, (![E_82, D_83, C_84]: (E_82=D_83 | E_82=C_84 | E_82=C_84 | ~r2_hidden(E_82, k2_tarski(C_84, D_83)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_154])).
% 2.14/1.29  tff(c_237, plain, (![E_82, A_16]: (E_82=A_16 | E_82=A_16 | E_82=A_16 | ~r2_hidden(E_82, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_228])).
% 2.14/1.29  tff(c_355, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_347, c_237])).
% 2.14/1.29  tff(c_359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_42, c_355])).
% 2.14/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  Inference rules
% 2.14/1.29  ----------------------
% 2.14/1.29  #Ref     : 0
% 2.14/1.29  #Sup     : 75
% 2.14/1.29  #Fact    : 0
% 2.14/1.29  #Define  : 0
% 2.14/1.29  #Split   : 0
% 2.14/1.29  #Chain   : 0
% 2.14/1.29  #Close   : 0
% 2.14/1.29  
% 2.14/1.29  Ordering : KBO
% 2.14/1.29  
% 2.14/1.29  Simplification rules
% 2.14/1.29  ----------------------
% 2.14/1.29  #Subsume      : 0
% 2.14/1.29  #Demod        : 26
% 2.14/1.29  #Tautology    : 49
% 2.14/1.29  #SimpNegUnit  : 1
% 2.14/1.29  #BackRed      : 0
% 2.14/1.29  
% 2.14/1.29  #Partial instantiations: 0
% 2.14/1.29  #Strategies tried      : 1
% 2.14/1.29  
% 2.14/1.29  Timing (in seconds)
% 2.14/1.29  ----------------------
% 2.14/1.29  Preprocessing        : 0.30
% 2.14/1.29  Parsing              : 0.14
% 2.14/1.29  CNF conversion       : 0.02
% 2.14/1.29  Main loop            : 0.20
% 2.14/1.29  Inferencing          : 0.08
% 2.14/1.29  Reduction            : 0.07
% 2.14/1.29  Demodulation         : 0.05
% 2.14/1.29  BG Simplification    : 0.02
% 2.14/1.29  Subsumption          : 0.03
% 2.14/1.29  Abstraction          : 0.01
% 2.14/1.29  MUC search           : 0.00
% 2.14/1.29  Cooper               : 0.00
% 2.14/1.29  Total                : 0.52
% 2.14/1.29  Index Insertion      : 0.00
% 2.14/1.29  Index Deletion       : 0.00
% 2.14/1.29  Index Matching       : 0.00
% 2.14/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
