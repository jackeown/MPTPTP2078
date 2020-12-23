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
% DateTime   : Thu Dec  3 09:48:43 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 107 expanded)
%              Number of leaves         :   24 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 ( 127 expanded)
%              Number of equality atoms :   38 ( 114 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_48,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_440,plain,(
    ! [A_68,B_69,C_70] : k2_xboole_0(k2_tarski(A_68,B_69),k1_tarski(C_70)) = k1_enumset1(A_68,B_69,C_70) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_449,plain,(
    ! [A_23,C_70] : k2_xboole_0(k1_tarski(A_23),k1_tarski(C_70)) = k1_enumset1(A_23,A_23,C_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_440])).

tff(c_452,plain,(
    ! [A_23,C_70] : k2_xboole_0(k1_tarski(A_23),k1_tarski(C_70)) = k2_tarski(A_23,C_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_449])).

tff(c_454,plain,(
    ! [A_71,C_72] : k2_xboole_0(k1_tarski(A_71),k1_tarski(C_72)) = k2_tarski(A_71,C_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_449])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_50,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_226,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k4_xboole_0(B_57,A_56)) = k2_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_244,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_226])).

tff(c_248,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_244])).

tff(c_460,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_248])).

tff(c_40,plain,(
    ! [A_20,B_21,C_22] : k2_xboole_0(k2_tarski(A_20,B_21),k1_tarski(C_22)) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_482,plain,(
    ! [C_22] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(C_22)) = k1_enumset1('#skF_4','#skF_3',C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_40])).

tff(c_523,plain,(
    ! [C_77] : k1_enumset1('#skF_4','#skF_3',C_77) = k2_tarski('#skF_4',C_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_482])).

tff(c_18,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_542,plain,(
    ! [C_77] : r2_hidden('#skF_3',k2_tarski('#skF_4',C_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_18])).

tff(c_495,plain,(
    ! [E_73,C_74,B_75,A_76] :
      ( E_73 = C_74
      | E_73 = B_75
      | E_73 = A_76
      | ~ r2_hidden(E_73,k1_enumset1(A_76,B_75,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_885,plain,(
    ! [E_97,B_98,A_99] :
      ( E_97 = B_98
      | E_97 = A_99
      | E_97 = A_99
      | ~ r2_hidden(E_97,k2_tarski(A_99,B_98)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_495])).

tff(c_888,plain,(
    ! [C_77] :
      ( C_77 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_542,c_885])).

tff(c_912,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_888])).

tff(c_906,plain,(
    ! [C_77] : C_77 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_888])).

tff(c_1090,plain,(
    ! [C_1282] : C_1282 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_912,c_906])).

tff(c_1255,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1090,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:59:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.52  
% 3.02/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.52  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.02/1.52  
% 3.02/1.52  %Foreground sorts:
% 3.02/1.52  
% 3.02/1.52  
% 3.02/1.52  %Background operators:
% 3.02/1.52  
% 3.02/1.52  
% 3.02/1.52  %Foreground operators:
% 3.02/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.02/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.02/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.02/1.52  
% 3.11/1.54  tff(f_67, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 3.11/1.54  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.11/1.54  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.11/1.54  tff(f_56, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 3.11/1.54  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.11/1.54  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.11/1.54  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.11/1.54  tff(c_48, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.11/1.54  tff(c_44, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.11/1.54  tff(c_42, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.11/1.54  tff(c_440, plain, (![A_68, B_69, C_70]: (k2_xboole_0(k2_tarski(A_68, B_69), k1_tarski(C_70))=k1_enumset1(A_68, B_69, C_70))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.11/1.54  tff(c_449, plain, (![A_23, C_70]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(C_70))=k1_enumset1(A_23, A_23, C_70))), inference(superposition, [status(thm), theory('equality')], [c_42, c_440])).
% 3.11/1.54  tff(c_452, plain, (![A_23, C_70]: (k2_xboole_0(k1_tarski(A_23), k1_tarski(C_70))=k2_tarski(A_23, C_70))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_449])).
% 3.11/1.54  tff(c_454, plain, (![A_71, C_72]: (k2_xboole_0(k1_tarski(A_71), k1_tarski(C_72))=k2_tarski(A_71, C_72))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_449])).
% 3.11/1.54  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.11/1.54  tff(c_50, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.11/1.54  tff(c_226, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k4_xboole_0(B_57, A_56))=k2_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.11/1.54  tff(c_244, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_226])).
% 3.11/1.54  tff(c_248, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_244])).
% 3.11/1.54  tff(c_460, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_454, c_248])).
% 3.11/1.54  tff(c_40, plain, (![A_20, B_21, C_22]: (k2_xboole_0(k2_tarski(A_20, B_21), k1_tarski(C_22))=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.11/1.54  tff(c_482, plain, (![C_22]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(C_22))=k1_enumset1('#skF_4', '#skF_3', C_22))), inference(superposition, [status(thm), theory('equality')], [c_460, c_40])).
% 3.11/1.54  tff(c_523, plain, (![C_77]: (k1_enumset1('#skF_4', '#skF_3', C_77)=k2_tarski('#skF_4', C_77))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_482])).
% 3.11/1.54  tff(c_18, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.11/1.54  tff(c_542, plain, (![C_77]: (r2_hidden('#skF_3', k2_tarski('#skF_4', C_77)))), inference(superposition, [status(thm), theory('equality')], [c_523, c_18])).
% 3.11/1.54  tff(c_495, plain, (![E_73, C_74, B_75, A_76]: (E_73=C_74 | E_73=B_75 | E_73=A_76 | ~r2_hidden(E_73, k1_enumset1(A_76, B_75, C_74)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.11/1.54  tff(c_885, plain, (![E_97, B_98, A_99]: (E_97=B_98 | E_97=A_99 | E_97=A_99 | ~r2_hidden(E_97, k2_tarski(A_99, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_495])).
% 3.11/1.54  tff(c_888, plain, (![C_77]: (C_77='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_542, c_885])).
% 3.11/1.54  tff(c_912, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_888])).
% 3.11/1.54  tff(c_906, plain, (![C_77]: (C_77='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_888])).
% 3.11/1.54  tff(c_1090, plain, (![C_1282]: (C_1282='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_912, c_906])).
% 3.11/1.54  tff(c_1255, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1090, c_48])).
% 3.11/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.54  
% 3.11/1.54  Inference rules
% 3.11/1.54  ----------------------
% 3.11/1.54  #Ref     : 0
% 3.11/1.54  #Sup     : 353
% 3.11/1.54  #Fact    : 0
% 3.11/1.54  #Define  : 0
% 3.11/1.54  #Split   : 0
% 3.11/1.54  #Chain   : 0
% 3.11/1.54  #Close   : 0
% 3.11/1.54  
% 3.11/1.54  Ordering : KBO
% 3.11/1.54  
% 3.11/1.54  Simplification rules
% 3.11/1.54  ----------------------
% 3.11/1.54  #Subsume      : 66
% 3.11/1.54  #Demod        : 134
% 3.11/1.54  #Tautology    : 181
% 3.11/1.54  #SimpNegUnit  : 7
% 3.11/1.54  #BackRed      : 0
% 3.11/1.54  
% 3.11/1.54  #Partial instantiations: 45
% 3.11/1.54  #Strategies tried      : 1
% 3.11/1.54  
% 3.11/1.54  Timing (in seconds)
% 3.11/1.54  ----------------------
% 3.11/1.54  Preprocessing        : 0.31
% 3.11/1.54  Parsing              : 0.16
% 3.11/1.54  CNF conversion       : 0.02
% 3.11/1.54  Main loop            : 0.46
% 3.11/1.54  Inferencing          : 0.19
% 3.11/1.54  Reduction            : 0.16
% 3.11/1.54  Demodulation         : 0.12
% 3.11/1.54  BG Simplification    : 0.02
% 3.11/1.54  Subsumption          : 0.07
% 3.11/1.54  Abstraction          : 0.02
% 3.11/1.54  MUC search           : 0.00
% 3.11/1.54  Cooper               : 0.00
% 3.11/1.54  Total                : 0.80
% 3.11/1.54  Index Insertion      : 0.00
% 3.11/1.54  Index Deletion       : 0.00
% 3.11/1.54  Index Matching       : 0.00
% 3.11/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
