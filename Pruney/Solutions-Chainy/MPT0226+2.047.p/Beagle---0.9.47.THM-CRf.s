%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:43 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   54 (  69 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    5
%              Number of atoms          :   52 (  79 expanded)
%              Number of equality atoms :   36 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_103])).

tff(c_115,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_112])).

tff(c_285,plain,(
    ! [A_94,B_95] :
      ( ~ r2_hidden(A_94,B_95)
      | k4_xboole_0(k1_tarski(A_94),B_95) != k1_tarski(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_298,plain,(
    ! [A_94] : ~ r2_hidden(A_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_285])).

tff(c_50,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_136,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(k1_tarski(A_64),B_65) = k1_tarski(A_64)
      | r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_146,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_52])).

tff(c_161,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_32,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_197,plain,(
    ! [E_76,C_77,B_78,A_79] :
      ( E_76 = C_77
      | E_76 = B_78
      | E_76 = A_79
      | ~ r2_hidden(E_76,k1_enumset1(A_79,B_78,C_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_225,plain,(
    ! [E_85,B_86,A_87] :
      ( E_85 = B_86
      | E_85 = A_87
      | E_85 = A_87
      | ~ r2_hidden(E_85,k2_tarski(A_87,B_86)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_197])).

tff(c_239,plain,(
    ! [E_88,A_89] :
      ( E_88 = A_89
      | E_88 = A_89
      | E_88 = A_89
      | ~ r2_hidden(E_88,k1_tarski(A_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_225])).

tff(c_242,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_161,c_239])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_50,c_242])).

tff(c_250,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_85,plain,(
    ! [A_54,B_55] : k1_enumset1(A_54,A_54,B_55) = k2_tarski(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [E_11,A_5,C_7] : r2_hidden(E_11,k1_enumset1(A_5,E_11,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_125,plain,(
    ! [A_59,B_60] : r2_hidden(A_59,k2_tarski(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_12])).

tff(c_128,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_125])).

tff(c_259,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_128])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.26  
% 2.01/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.27  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.01/1.27  
% 2.01/1.27  %Foreground sorts:
% 2.01/1.27  
% 2.01/1.27  
% 2.01/1.27  %Background operators:
% 2.01/1.27  
% 2.01/1.27  
% 2.01/1.27  %Foreground operators:
% 2.01/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.01/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.01/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.01/1.27  
% 2.01/1.28  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.01/1.28  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.01/1.28  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.01/1.28  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.01/1.28  tff(f_70, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.01/1.28  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.01/1.28  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.01/1.28  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.01/1.28  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.28  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.28  tff(c_103, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.28  tff(c_112, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_103])).
% 2.01/1.28  tff(c_115, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_112])).
% 2.01/1.28  tff(c_285, plain, (![A_94, B_95]: (~r2_hidden(A_94, B_95) | k4_xboole_0(k1_tarski(A_94), B_95)!=k1_tarski(A_94))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.01/1.28  tff(c_298, plain, (![A_94]: (~r2_hidden(A_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_115, c_285])).
% 2.01/1.28  tff(c_50, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.01/1.28  tff(c_136, plain, (![A_64, B_65]: (k4_xboole_0(k1_tarski(A_64), B_65)=k1_tarski(A_64) | r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.01/1.28  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.01/1.28  tff(c_146, plain, (k1_tarski('#skF_3')=k1_xboole_0 | r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_52])).
% 2.01/1.28  tff(c_161, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_146])).
% 2.01/1.28  tff(c_32, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.28  tff(c_34, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.01/1.28  tff(c_197, plain, (![E_76, C_77, B_78, A_79]: (E_76=C_77 | E_76=B_78 | E_76=A_79 | ~r2_hidden(E_76, k1_enumset1(A_79, B_78, C_77)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.01/1.28  tff(c_225, plain, (![E_85, B_86, A_87]: (E_85=B_86 | E_85=A_87 | E_85=A_87 | ~r2_hidden(E_85, k2_tarski(A_87, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_197])).
% 2.01/1.28  tff(c_239, plain, (![E_88, A_89]: (E_88=A_89 | E_88=A_89 | E_88=A_89 | ~r2_hidden(E_88, k1_tarski(A_89)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_225])).
% 2.01/1.28  tff(c_242, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_161, c_239])).
% 2.01/1.28  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_50, c_242])).
% 2.01/1.28  tff(c_250, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_146])).
% 2.01/1.28  tff(c_85, plain, (![A_54, B_55]: (k1_enumset1(A_54, A_54, B_55)=k2_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.01/1.28  tff(c_12, plain, (![E_11, A_5, C_7]: (r2_hidden(E_11, k1_enumset1(A_5, E_11, C_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.01/1.28  tff(c_125, plain, (![A_59, B_60]: (r2_hidden(A_59, k2_tarski(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_12])).
% 2.01/1.28  tff(c_128, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_125])).
% 2.01/1.28  tff(c_259, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_250, c_128])).
% 2.01/1.28  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_298, c_259])).
% 2.01/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.28  
% 2.01/1.28  Inference rules
% 2.01/1.28  ----------------------
% 2.01/1.28  #Ref     : 0
% 2.01/1.28  #Sup     : 56
% 2.01/1.28  #Fact    : 0
% 2.01/1.28  #Define  : 0
% 2.01/1.28  #Split   : 1
% 2.01/1.28  #Chain   : 0
% 2.01/1.28  #Close   : 0
% 2.01/1.28  
% 2.01/1.28  Ordering : KBO
% 2.01/1.28  
% 2.01/1.28  Simplification rules
% 2.01/1.28  ----------------------
% 2.01/1.28  #Subsume      : 0
% 2.01/1.28  #Demod        : 10
% 2.01/1.28  #Tautology    : 42
% 2.01/1.28  #SimpNegUnit  : 3
% 2.01/1.28  #BackRed      : 2
% 2.01/1.28  
% 2.01/1.28  #Partial instantiations: 0
% 2.01/1.28  #Strategies tried      : 1
% 2.01/1.28  
% 2.01/1.28  Timing (in seconds)
% 2.01/1.28  ----------------------
% 2.01/1.28  Preprocessing        : 0.29
% 2.01/1.28  Parsing              : 0.15
% 2.01/1.28  CNF conversion       : 0.02
% 2.01/1.28  Main loop            : 0.18
% 2.01/1.28  Inferencing          : 0.06
% 2.01/1.28  Reduction            : 0.06
% 2.01/1.28  Demodulation         : 0.04
% 2.01/1.28  BG Simplification    : 0.02
% 2.01/1.28  Subsumption          : 0.03
% 2.01/1.28  Abstraction          : 0.01
% 2.01/1.28  MUC search           : 0.00
% 2.01/1.28  Cooper               : 0.00
% 2.01/1.28  Total                : 0.50
% 2.01/1.28  Index Insertion      : 0.00
% 2.01/1.28  Index Deletion       : 0.00
% 2.01/1.28  Index Matching       : 0.00
% 2.01/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
