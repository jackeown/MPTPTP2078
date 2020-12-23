%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:40 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :   50 (  54 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  44 expanded)
%              Number of equality atoms :   32 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_60,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1471,plain,(
    ! [A_1247,B_1248,C_1249,D_1250] : k2_xboole_0(k1_enumset1(A_1247,B_1248,C_1249),k1_tarski(D_1250)) = k2_enumset1(A_1247,B_1248,C_1249,D_1250) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1534,plain,(
    ! [A_32,B_33,D_1250] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(D_1250)) = k2_enumset1(A_32,A_32,B_33,D_1250) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1471])).

tff(c_4863,plain,(
    ! [A_2588,B_2589,D_2590] : k2_xboole_0(k2_tarski(A_2588,B_2589),k1_tarski(D_2590)) = k1_enumset1(A_2588,B_2589,D_2590) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1534])).

tff(c_4926,plain,(
    ! [A_31,D_2590] : k2_xboole_0(k1_tarski(A_31),k1_tarski(D_2590)) = k1_enumset1(A_31,A_31,D_2590) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_4863])).

tff(c_4930,plain,(
    ! [A_2621,D_2622] : k2_xboole_0(k1_tarski(A_2621),k1_tarski(D_2622)) = k2_tarski(A_2621,D_2622) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4926])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_442,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_462,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_442])).

tff(c_465,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_462])).

tff(c_4948,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4930,c_465])).

tff(c_209,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_221,plain,(
    ! [B_56,A_55] : r2_hidden(B_56,k2_tarski(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_16])).

tff(c_5044,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4948,c_221])).

tff(c_38,plain,(
    ! [C_23,A_19] :
      ( C_23 = A_19
      | ~ r2_hidden(C_23,k1_tarski(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5071,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5044,c_38])).

tff(c_5108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5071])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:44:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.96  
% 4.82/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.96  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 4.82/1.96  
% 4.82/1.96  %Foreground sorts:
% 4.82/1.96  
% 4.82/1.96  
% 4.82/1.96  %Background operators:
% 4.82/1.96  
% 4.82/1.96  
% 4.82/1.96  %Foreground operators:
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.82/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.82/1.96  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.82/1.96  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.82/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.82/1.96  tff('#skF_5', type, '#skF_5': $i).
% 4.82/1.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.82/1.96  tff('#skF_6', type, '#skF_6': $i).
% 4.82/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.96  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.82/1.96  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.82/1.96  
% 4.82/1.97  tff(f_74, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 4.82/1.97  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.82/1.97  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.82/1.97  tff(f_69, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.82/1.97  tff(f_63, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 4.82/1.97  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.82/1.97  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.82/1.97  tff(f_52, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.82/1.97  tff(f_59, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.82/1.97  tff(c_60, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.82/1.97  tff(c_56, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.82/1.97  tff(c_54, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.82/1.97  tff(c_58, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.82/1.97  tff(c_1471, plain, (![A_1247, B_1248, C_1249, D_1250]: (k2_xboole_0(k1_enumset1(A_1247, B_1248, C_1249), k1_tarski(D_1250))=k2_enumset1(A_1247, B_1248, C_1249, D_1250))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.82/1.97  tff(c_1534, plain, (![A_32, B_33, D_1250]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(D_1250))=k2_enumset1(A_32, A_32, B_33, D_1250))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1471])).
% 4.82/1.97  tff(c_4863, plain, (![A_2588, B_2589, D_2590]: (k2_xboole_0(k2_tarski(A_2588, B_2589), k1_tarski(D_2590))=k1_enumset1(A_2588, B_2589, D_2590))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1534])).
% 4.82/1.97  tff(c_4926, plain, (![A_31, D_2590]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(D_2590))=k1_enumset1(A_31, A_31, D_2590))), inference(superposition, [status(thm), theory('equality')], [c_54, c_4863])).
% 4.82/1.97  tff(c_4930, plain, (![A_2621, D_2622]: (k2_xboole_0(k1_tarski(A_2621), k1_tarski(D_2622))=k2_tarski(A_2621, D_2622))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4926])).
% 4.82/1.97  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.97  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.82/1.97  tff(c_442, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.82/1.97  tff(c_462, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_442])).
% 4.82/1.97  tff(c_465, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_462])).
% 4.82/1.97  tff(c_4948, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4930, c_465])).
% 4.82/1.97  tff(c_209, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.82/1.97  tff(c_16, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.82/1.97  tff(c_221, plain, (![B_56, A_55]: (r2_hidden(B_56, k2_tarski(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_209, c_16])).
% 4.82/1.97  tff(c_5044, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4948, c_221])).
% 4.82/1.97  tff(c_38, plain, (![C_23, A_19]: (C_23=A_19 | ~r2_hidden(C_23, k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.82/1.97  tff(c_5071, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_5044, c_38])).
% 4.82/1.97  tff(c_5108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_5071])).
% 4.82/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.97  
% 4.82/1.97  Inference rules
% 4.82/1.97  ----------------------
% 4.82/1.97  #Ref     : 0
% 4.82/1.97  #Sup     : 1111
% 4.82/1.97  #Fact    : 0
% 4.82/1.97  #Define  : 0
% 4.82/1.97  #Split   : 6
% 4.82/1.97  #Chain   : 0
% 4.82/1.97  #Close   : 0
% 4.82/1.97  
% 4.82/1.97  Ordering : KBO
% 4.82/1.97  
% 4.82/1.97  Simplification rules
% 4.82/1.97  ----------------------
% 4.82/1.97  #Subsume      : 45
% 4.82/1.97  #Demod        : 949
% 4.82/1.97  #Tautology    : 695
% 4.82/1.97  #SimpNegUnit  : 1
% 4.82/1.97  #BackRed      : 0
% 4.82/1.97  
% 4.82/1.97  #Partial instantiations: 1245
% 4.82/1.97  #Strategies tried      : 1
% 4.82/1.97  
% 4.82/1.97  Timing (in seconds)
% 4.82/1.97  ----------------------
% 4.82/1.97  Preprocessing        : 0.31
% 4.82/1.97  Parsing              : 0.15
% 4.82/1.97  CNF conversion       : 0.02
% 4.82/1.97  Main loop            : 0.90
% 4.82/1.97  Inferencing          : 0.31
% 5.03/1.97  Reduction            : 0.39
% 5.03/1.97  Demodulation         : 0.33
% 5.03/1.97  BG Simplification    : 0.04
% 5.03/1.97  Subsumption          : 0.12
% 5.03/1.98  Abstraction          : 0.04
% 5.03/1.98  MUC search           : 0.00
% 5.03/1.98  Cooper               : 0.00
% 5.03/1.98  Total                : 1.23
% 5.03/1.98  Index Insertion      : 0.00
% 5.03/1.98  Index Deletion       : 0.00
% 5.03/1.98  Index Matching       : 0.00
% 5.03/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
