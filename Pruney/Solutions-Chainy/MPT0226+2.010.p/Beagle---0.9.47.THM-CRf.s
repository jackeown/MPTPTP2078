%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:39 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   52 (  68 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   43 (  66 expanded)
%              Number of equality atoms :   37 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_50,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_191,plain,(
    ! [A_73,B_74,C_75] : k2_xboole_0(k2_tarski(A_73,B_74),k1_tarski(C_75)) = k1_enumset1(A_73,B_74,C_75) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_206,plain,(
    ! [A_18,C_75] : k2_xboole_0(k1_tarski(A_18),k1_tarski(C_75)) = k1_enumset1(A_18,A_18,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_191])).

tff(c_209,plain,(
    ! [A_18,C_75] : k2_xboole_0(k1_tarski(A_18),k1_tarski(C_75)) = k2_tarski(A_18,C_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_206])).

tff(c_210,plain,(
    ! [A_76,C_77] : k2_xboole_0(k1_tarski(A_76),k1_tarski(C_77)) = k2_tarski(A_76,C_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_206])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_164,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k4_xboole_0(B_69,A_68)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_164])).

tff(c_176,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_173])).

tff(c_216,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_176])).

tff(c_34,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k2_tarski(A_15,B_16),k1_tarski(C_17)) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_228,plain,(
    ! [C_17] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(C_17)) = k1_enumset1('#skF_4','#skF_3',C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_34])).

tff(c_241,plain,(
    ! [C_78] : k1_enumset1('#skF_4','#skF_3',C_78) = k2_tarski('#skF_4',C_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_228])).

tff(c_14,plain,(
    ! [E_14,A_8,C_10] : r2_hidden(E_14,k1_enumset1(A_8,E_14,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_250,plain,(
    ! [C_78] : r2_hidden('#skF_3',k2_tarski('#skF_4',C_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_14])).

tff(c_304,plain,(
    ! [E_85,C_86,B_87,A_88] :
      ( E_85 = C_86
      | E_85 = B_87
      | E_85 = A_88
      | ~ r2_hidden(E_85,k1_enumset1(A_88,B_87,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_472,plain,(
    ! [E_101,B_102,A_103] :
      ( E_101 = B_102
      | E_101 = A_103
      | E_101 = A_103
      | ~ r2_hidden(E_101,k2_tarski(A_103,B_102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_304])).

tff(c_478,plain,(
    ! [C_78] :
      ( C_78 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_250,c_472])).

tff(c_507,plain,(
    ! [C_104] : C_104 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_478])).

tff(c_623,plain,(
    ! [C_104] : C_104 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_50])).

tff(c_636,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_623])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:39:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.34  
% 2.54/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.54/1.35  
% 2.54/1.35  %Foreground sorts:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Background operators:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Foreground operators:
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.54/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.54/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.54/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.54/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.54/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.54/1.35  
% 2.54/1.36  tff(f_69, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.54/1.36  tff(f_54, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.54/1.36  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.54/1.36  tff(f_50, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.54/1.36  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.54/1.36  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.54/1.36  tff(f_48, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.54/1.36  tff(c_50, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.54/1.36  tff(c_38, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.54/1.36  tff(c_36, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.54/1.36  tff(c_191, plain, (![A_73, B_74, C_75]: (k2_xboole_0(k2_tarski(A_73, B_74), k1_tarski(C_75))=k1_enumset1(A_73, B_74, C_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.36  tff(c_206, plain, (![A_18, C_75]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(C_75))=k1_enumset1(A_18, A_18, C_75))), inference(superposition, [status(thm), theory('equality')], [c_36, c_191])).
% 2.54/1.36  tff(c_209, plain, (![A_18, C_75]: (k2_xboole_0(k1_tarski(A_18), k1_tarski(C_75))=k2_tarski(A_18, C_75))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_206])).
% 2.54/1.36  tff(c_210, plain, (![A_76, C_77]: (k2_xboole_0(k1_tarski(A_76), k1_tarski(C_77))=k2_tarski(A_76, C_77))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_206])).
% 2.54/1.36  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.36  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.54/1.36  tff(c_164, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k4_xboole_0(B_69, A_68))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.36  tff(c_173, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_52, c_164])).
% 2.54/1.36  tff(c_176, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_173])).
% 2.54/1.36  tff(c_216, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_210, c_176])).
% 2.54/1.36  tff(c_34, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k2_tarski(A_15, B_16), k1_tarski(C_17))=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.36  tff(c_228, plain, (![C_17]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(C_17))=k1_enumset1('#skF_4', '#skF_3', C_17))), inference(superposition, [status(thm), theory('equality')], [c_216, c_34])).
% 2.54/1.36  tff(c_241, plain, (![C_78]: (k1_enumset1('#skF_4', '#skF_3', C_78)=k2_tarski('#skF_4', C_78))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_228])).
% 2.54/1.36  tff(c_14, plain, (![E_14, A_8, C_10]: (r2_hidden(E_14, k1_enumset1(A_8, E_14, C_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.36  tff(c_250, plain, (![C_78]: (r2_hidden('#skF_3', k2_tarski('#skF_4', C_78)))), inference(superposition, [status(thm), theory('equality')], [c_241, c_14])).
% 2.54/1.36  tff(c_304, plain, (![E_85, C_86, B_87, A_88]: (E_85=C_86 | E_85=B_87 | E_85=A_88 | ~r2_hidden(E_85, k1_enumset1(A_88, B_87, C_86)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.36  tff(c_472, plain, (![E_101, B_102, A_103]: (E_101=B_102 | E_101=A_103 | E_101=A_103 | ~r2_hidden(E_101, k2_tarski(A_103, B_102)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_304])).
% 2.54/1.36  tff(c_478, plain, (![C_78]: (C_78='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_250, c_472])).
% 2.54/1.36  tff(c_507, plain, (![C_104]: (C_104='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_478])).
% 2.54/1.36  tff(c_623, plain, (![C_104]: (C_104!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_507, c_50])).
% 2.54/1.36  tff(c_636, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_623])).
% 2.54/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  Inference rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Ref     : 1
% 2.54/1.36  #Sup     : 166
% 2.54/1.36  #Fact    : 0
% 2.54/1.36  #Define  : 0
% 2.54/1.36  #Split   : 0
% 2.54/1.36  #Chain   : 0
% 2.54/1.36  #Close   : 0
% 2.54/1.36  
% 2.54/1.36  Ordering : KBO
% 2.54/1.36  
% 2.54/1.36  Simplification rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Subsume      : 23
% 2.54/1.36  #Demod        : 44
% 2.54/1.36  #Tautology    : 92
% 2.54/1.36  #SimpNegUnit  : 2
% 2.54/1.36  #BackRed      : 0
% 2.54/1.36  
% 2.54/1.36  #Partial instantiations: 32
% 2.54/1.36  #Strategies tried      : 1
% 2.54/1.36  
% 2.54/1.36  Timing (in seconds)
% 2.54/1.36  ----------------------
% 2.75/1.36  Preprocessing        : 0.32
% 2.75/1.36  Parsing              : 0.16
% 2.75/1.36  CNF conversion       : 0.02
% 2.75/1.36  Main loop            : 0.28
% 2.75/1.36  Inferencing          : 0.11
% 2.75/1.36  Reduction            : 0.09
% 2.75/1.36  Demodulation         : 0.07
% 2.75/1.36  BG Simplification    : 0.02
% 2.75/1.36  Subsumption          : 0.04
% 2.75/1.36  Abstraction          : 0.01
% 2.75/1.36  MUC search           : 0.00
% 2.75/1.36  Cooper               : 0.00
% 2.75/1.36  Total                : 0.62
% 2.75/1.36  Index Insertion      : 0.00
% 2.75/1.36  Index Deletion       : 0.00
% 2.75/1.36  Index Matching       : 0.00
% 2.75/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
