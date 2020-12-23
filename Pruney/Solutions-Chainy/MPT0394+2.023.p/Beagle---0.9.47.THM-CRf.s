%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:23 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   61 (  93 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 ( 107 expanded)
%              Number of equality atoms :   46 (  74 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_52,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_38,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_82,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [E_13,A_7,B_8] : r2_hidden(E_13,k1_enumset1(A_7,B_8,E_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_100,plain,(
    ! [B_45,A_46] : r2_hidden(B_45,k2_tarski(A_46,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_14])).

tff(c_103,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_100])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = A_50
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(resolution,[status(thm)],[c_6,c_111])).

tff(c_154,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_169,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_154])).

tff(c_172,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_169])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_55,B_56] :
      ( ~ r2_hidden(A_55,B_56)
      | ~ r1_xboole_0(k1_tarski(A_55),B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_239,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden(A_68,B_69)
      | k4_xboole_0(k1_tarski(A_68),B_69) != k1_tarski(A_68) ) ),
    inference(resolution,[status(thm)],[c_10,c_130])).

tff(c_243,plain,(
    ! [A_68] :
      ( ~ r2_hidden(A_68,k1_tarski(A_68))
      | k1_tarski(A_68) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_239])).

tff(c_253,plain,(
    ! [A_68] : k1_tarski(A_68) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_243])).

tff(c_50,plain,(
    ! [A_29] : k1_setfam_1(k1_tarski(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_255,plain,(
    ! [A_70,B_71,C_72] : k2_xboole_0(k2_tarski(A_70,B_71),k1_tarski(C_72)) = k1_enumset1(A_70,B_71,C_72) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_264,plain,(
    ! [A_17,C_72] : k2_xboole_0(k1_tarski(A_17),k1_tarski(C_72)) = k1_enumset1(A_17,A_17,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_255])).

tff(c_267,plain,(
    ! [A_17,C_72] : k2_xboole_0(k1_tarski(A_17),k1_tarski(C_72)) = k2_tarski(A_17,C_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_264])).

tff(c_362,plain,(
    ! [A_88,B_89] :
      ( k3_xboole_0(k1_setfam_1(A_88),k1_setfam_1(B_89)) = k1_setfam_1(k2_xboole_0(A_88,B_89))
      | k1_xboole_0 = B_89
      | k1_xboole_0 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_385,plain,(
    ! [A_88,A_29] :
      ( k1_setfam_1(k2_xboole_0(A_88,k1_tarski(A_29))) = k3_xboole_0(k1_setfam_1(A_88),A_29)
      | k1_tarski(A_29) = k1_xboole_0
      | k1_xboole_0 = A_88 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_362])).

tff(c_438,plain,(
    ! [A_96,A_97] :
      ( k1_setfam_1(k2_xboole_0(A_96,k1_tarski(A_97))) = k3_xboole_0(k1_setfam_1(A_96),A_97)
      | k1_xboole_0 = A_96 ) ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_385])).

tff(c_461,plain,(
    ! [A_17,C_72] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_17)),C_72) = k1_setfam_1(k2_tarski(A_17,C_72))
      | k1_tarski(A_17) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_438])).

tff(c_475,plain,(
    ! [A_17,C_72] :
      ( k1_setfam_1(k2_tarski(A_17,C_72)) = k3_xboole_0(A_17,C_72)
      | k1_tarski(A_17) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_461])).

tff(c_476,plain,(
    ! [A_17,C_72] : k1_setfam_1(k2_tarski(A_17,C_72)) = k3_xboole_0(A_17,C_72) ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_475])).

tff(c_52,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:36:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.40  
% 2.53/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.41  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.53/1.41  
% 2.53/1.41  %Foreground sorts:
% 2.53/1.41  
% 2.53/1.41  
% 2.53/1.41  %Background operators:
% 2.53/1.41  
% 2.53/1.41  
% 2.53/1.41  %Foreground operators:
% 2.53/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.53/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.53/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.53/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.53/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.53/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.53/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.53/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.53/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.53/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.53/1.41  
% 2.53/1.42  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.53/1.42  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.53/1.42  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.53/1.42  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.53/1.42  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.53/1.42  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.53/1.42  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.53/1.42  tff(f_63, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.53/1.42  tff(f_77, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.53/1.42  tff(f_52, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.53/1.42  tff(f_75, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.53/1.42  tff(f_80, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.53/1.42  tff(c_38, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.53/1.42  tff(c_82, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.42  tff(c_14, plain, (![E_13, A_7, B_8]: (r2_hidden(E_13, k1_enumset1(A_7, B_8, E_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.53/1.42  tff(c_100, plain, (![B_45, A_46]: (r2_hidden(B_45, k2_tarski(A_46, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_14])).
% 2.53/1.42  tff(c_103, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_100])).
% 2.53/1.42  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.53/1.42  tff(c_6, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.42  tff(c_111, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=A_50 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.42  tff(c_115, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(resolution, [status(thm)], [c_6, c_111])).
% 2.53/1.42  tff(c_154, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.53/1.42  tff(c_169, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_115, c_154])).
% 2.53/1.42  tff(c_172, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_169])).
% 2.53/1.42  tff(c_10, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k4_xboole_0(A_5, B_6)!=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.42  tff(c_130, plain, (![A_55, B_56]: (~r2_hidden(A_55, B_56) | ~r1_xboole_0(k1_tarski(A_55), B_56))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.53/1.42  tff(c_239, plain, (![A_68, B_69]: (~r2_hidden(A_68, B_69) | k4_xboole_0(k1_tarski(A_68), B_69)!=k1_tarski(A_68))), inference(resolution, [status(thm)], [c_10, c_130])).
% 2.53/1.42  tff(c_243, plain, (![A_68]: (~r2_hidden(A_68, k1_tarski(A_68)) | k1_tarski(A_68)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_172, c_239])).
% 2.53/1.42  tff(c_253, plain, (![A_68]: (k1_tarski(A_68)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_243])).
% 2.53/1.42  tff(c_50, plain, (![A_29]: (k1_setfam_1(k1_tarski(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.53/1.42  tff(c_40, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.53/1.42  tff(c_255, plain, (![A_70, B_71, C_72]: (k2_xboole_0(k2_tarski(A_70, B_71), k1_tarski(C_72))=k1_enumset1(A_70, B_71, C_72))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.42  tff(c_264, plain, (![A_17, C_72]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(C_72))=k1_enumset1(A_17, A_17, C_72))), inference(superposition, [status(thm), theory('equality')], [c_38, c_255])).
% 2.53/1.42  tff(c_267, plain, (![A_17, C_72]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(C_72))=k2_tarski(A_17, C_72))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_264])).
% 2.53/1.42  tff(c_362, plain, (![A_88, B_89]: (k3_xboole_0(k1_setfam_1(A_88), k1_setfam_1(B_89))=k1_setfam_1(k2_xboole_0(A_88, B_89)) | k1_xboole_0=B_89 | k1_xboole_0=A_88)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.53/1.42  tff(c_385, plain, (![A_88, A_29]: (k1_setfam_1(k2_xboole_0(A_88, k1_tarski(A_29)))=k3_xboole_0(k1_setfam_1(A_88), A_29) | k1_tarski(A_29)=k1_xboole_0 | k1_xboole_0=A_88)), inference(superposition, [status(thm), theory('equality')], [c_50, c_362])).
% 2.53/1.42  tff(c_438, plain, (![A_96, A_97]: (k1_setfam_1(k2_xboole_0(A_96, k1_tarski(A_97)))=k3_xboole_0(k1_setfam_1(A_96), A_97) | k1_xboole_0=A_96)), inference(negUnitSimplification, [status(thm)], [c_253, c_385])).
% 2.53/1.42  tff(c_461, plain, (![A_17, C_72]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_17)), C_72)=k1_setfam_1(k2_tarski(A_17, C_72)) | k1_tarski(A_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_267, c_438])).
% 2.53/1.42  tff(c_475, plain, (![A_17, C_72]: (k1_setfam_1(k2_tarski(A_17, C_72))=k3_xboole_0(A_17, C_72) | k1_tarski(A_17)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_461])).
% 2.53/1.42  tff(c_476, plain, (![A_17, C_72]: (k1_setfam_1(k2_tarski(A_17, C_72))=k3_xboole_0(A_17, C_72))), inference(negUnitSimplification, [status(thm)], [c_253, c_475])).
% 2.53/1.42  tff(c_52, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.53/1.42  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_476, c_52])).
% 2.53/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.42  
% 2.53/1.42  Inference rules
% 2.53/1.42  ----------------------
% 2.53/1.42  #Ref     : 0
% 2.53/1.42  #Sup     : 96
% 2.53/1.42  #Fact    : 0
% 2.53/1.42  #Define  : 0
% 2.53/1.42  #Split   : 0
% 2.53/1.42  #Chain   : 0
% 2.53/1.42  #Close   : 0
% 2.53/1.42  
% 2.53/1.42  Ordering : KBO
% 2.53/1.42  
% 2.53/1.42  Simplification rules
% 2.53/1.42  ----------------------
% 2.53/1.42  #Subsume      : 3
% 2.53/1.42  #Demod        : 33
% 2.53/1.42  #Tautology    : 62
% 2.53/1.42  #SimpNegUnit  : 8
% 2.53/1.42  #BackRed      : 1
% 2.53/1.42  
% 2.53/1.42  #Partial instantiations: 0
% 2.53/1.42  #Strategies tried      : 1
% 2.53/1.42  
% 2.53/1.42  Timing (in seconds)
% 2.53/1.42  ----------------------
% 2.53/1.43  Preprocessing        : 0.30
% 2.53/1.43  Parsing              : 0.15
% 2.53/1.43  CNF conversion       : 0.02
% 2.53/1.43  Main loop            : 0.29
% 2.53/1.43  Inferencing          : 0.11
% 2.53/1.43  Reduction            : 0.09
% 2.53/1.43  Demodulation         : 0.07
% 2.53/1.43  BG Simplification    : 0.02
% 2.53/1.43  Subsumption          : 0.04
% 2.53/1.43  Abstraction          : 0.02
% 2.53/1.43  MUC search           : 0.00
% 2.53/1.43  Cooper               : 0.00
% 2.53/1.43  Total                : 0.63
% 2.53/1.43  Index Insertion      : 0.00
% 2.53/1.43  Index Deletion       : 0.00
% 2.53/1.43  Index Matching       : 0.00
% 2.53/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
