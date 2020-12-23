%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:10 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 138 expanded)
%              Number of leaves         :   36 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 186 expanded)
%              Number of equality atoms :   68 ( 154 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_98,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_24,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_146,plain,(
    ! [A_56,B_57] : k4_xboole_0(A_56,k2_xboole_0(A_56,B_57)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_153,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_146])).

tff(c_60,plain,(
    ! [B_30] : k4_xboole_0(k1_tarski(B_30),k1_tarski(B_30)) != k1_tarski(B_30) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_661,plain,(
    ! [B_30] : k1_tarski(B_30) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_60])).

tff(c_74,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_5'(A_37),A_37)
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_789,plain,(
    ! [A_159,B_160] :
      ( k4_xboole_0(k1_tarski(A_159),k1_tarski(B_160)) = k1_tarski(A_159)
      | B_160 = A_159 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    ! [B_32,A_31] :
      ( ~ r2_hidden(B_32,A_31)
      | k4_xboole_0(A_31,k1_tarski(B_32)) != A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_836,plain,(
    ! [B_162,A_163] :
      ( ~ r2_hidden(B_162,k1_tarski(A_163))
      | B_162 = A_163 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_64])).

tff(c_843,plain,(
    ! [A_163] :
      ( '#skF_5'(k1_tarski(A_163)) = A_163
      | k1_tarski(A_163) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_836])).

tff(c_848,plain,(
    ! [A_163] : '#skF_5'(k1_tarski(A_163)) = A_163 ),
    inference(negUnitSimplification,[status(thm)],[c_661,c_843])).

tff(c_52,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_576,plain,(
    ! [A_127,B_128] : k1_enumset1(A_127,A_127,B_128) = k2_tarski(A_127,B_128) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [E_20,B_15,C_16] : r2_hidden(E_20,k1_enumset1(E_20,B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_594,plain,(
    ! [A_129,B_130] : r2_hidden(A_129,k2_tarski(A_129,B_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_34])).

tff(c_597,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_594])).

tff(c_900,plain,(
    ! [D_173,A_174,C_175] :
      ( ~ r2_hidden(D_173,A_174)
      | k4_tarski(C_175,D_173) != '#skF_5'(A_174)
      | k1_xboole_0 = A_174 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_904,plain,(
    ! [C_175,A_21] :
      ( k4_tarski(C_175,A_21) != '#skF_5'(k1_tarski(A_21))
      | k1_tarski(A_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_597,c_900])).

tff(c_917,plain,(
    ! [C_175,A_21] :
      ( k4_tarski(C_175,A_21) != A_21
      | k1_tarski(A_21) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_904])).

tff(c_918,plain,(
    ! [C_175,A_21] : k4_tarski(C_175,A_21) != A_21 ),
    inference(negUnitSimplification,[status(thm)],[c_661,c_917])).

tff(c_256,plain,(
    ! [B_30] : k1_tarski(B_30) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_60])).

tff(c_405,plain,(
    ! [A_100,B_101] :
      ( k4_xboole_0(k1_tarski(A_100),k1_tarski(B_101)) = k1_tarski(A_100)
      | B_101 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_445,plain,(
    ! [B_102,A_103] :
      ( ~ r2_hidden(B_102,k1_tarski(A_103))
      | B_102 = A_103 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_64])).

tff(c_452,plain,(
    ! [A_103] :
      ( '#skF_5'(k1_tarski(A_103)) = A_103
      | k1_tarski(A_103) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_74,c_445])).

tff(c_457,plain,(
    ! [A_103] : '#skF_5'(k1_tarski(A_103)) = A_103 ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_452])).

tff(c_258,plain,(
    ! [A_77,B_78] : k1_enumset1(A_77,A_77,B_78) = k2_tarski(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_291,plain,(
    ! [B_82,A_83] : r2_hidden(B_82,k2_tarski(A_83,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_30])).

tff(c_294,plain,(
    ! [A_21] : r2_hidden(A_21,k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_291])).

tff(c_509,plain,(
    ! [C_113,A_114,D_115] :
      ( ~ r2_hidden(C_113,A_114)
      | k4_tarski(C_113,D_115) != '#skF_5'(A_114)
      | k1_xboole_0 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_513,plain,(
    ! [A_21,D_115] :
      ( k4_tarski(A_21,D_115) != '#skF_5'(k1_tarski(A_21))
      | k1_tarski(A_21) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_294,c_509])).

tff(c_526,plain,(
    ! [A_21,D_115] :
      ( k4_tarski(A_21,D_115) != A_21
      | k1_tarski(A_21) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_513])).

tff(c_527,plain,(
    ! [A_21,D_115] : k4_tarski(A_21,D_115) != A_21 ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_526])).

tff(c_82,plain,(
    k4_tarski('#skF_7','#skF_8') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_126,plain,(
    ! [A_54,B_55] : k1_mcart_1(k4_tarski(A_54,B_55)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_135,plain,(
    k1_mcart_1('#skF_6') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_126])).

tff(c_114,plain,(
    ! [A_52,B_53] : k2_mcart_1(k4_tarski(A_52,B_53)) = B_53 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_123,plain,(
    k2_mcart_1('#skF_6') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_114])).

tff(c_80,plain,
    ( k2_mcart_1('#skF_6') = '#skF_6'
    | k1_mcart_1('#skF_6') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_156,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_123,c_80])).

tff(c_157,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_159,plain,(
    k4_tarski('#skF_6','#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_82])).

tff(c_534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_527,c_159])).

tff(c_535,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_540,plain,(
    k4_tarski('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_82])).

tff(c_925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_918,c_540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.38  
% 2.76/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.38  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.76/1.38  
% 2.76/1.38  %Foreground sorts:
% 2.76/1.38  
% 2.76/1.38  
% 2.76/1.38  %Background operators:
% 2.76/1.38  
% 2.76/1.38  
% 2.76/1.38  %Foreground operators:
% 2.76/1.38  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.76/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.76/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.76/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.76/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.76/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.76/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.76/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.76/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.38  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.76/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.38  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.76/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.76/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.76/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.76/1.38  
% 2.76/1.40  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.76/1.40  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.76/1.40  tff(f_71, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.76/1.40  tff(f_98, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.76/1.40  tff(f_76, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.76/1.40  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.76/1.40  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.76/1.40  tff(f_58, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.76/1.40  tff(f_108, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.76/1.40  tff(f_82, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.76/1.40  tff(c_24, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.40  tff(c_146, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k2_xboole_0(A_56, B_57))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.76/1.40  tff(c_153, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_146])).
% 2.76/1.40  tff(c_60, plain, (![B_30]: (k4_xboole_0(k1_tarski(B_30), k1_tarski(B_30))!=k1_tarski(B_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.40  tff(c_661, plain, (![B_30]: (k1_tarski(B_30)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_60])).
% 2.76/1.40  tff(c_74, plain, (![A_37]: (r2_hidden('#skF_5'(A_37), A_37) | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.76/1.40  tff(c_789, plain, (![A_159, B_160]: (k4_xboole_0(k1_tarski(A_159), k1_tarski(B_160))=k1_tarski(A_159) | B_160=A_159)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.40  tff(c_64, plain, (![B_32, A_31]: (~r2_hidden(B_32, A_31) | k4_xboole_0(A_31, k1_tarski(B_32))!=A_31)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.76/1.40  tff(c_836, plain, (![B_162, A_163]: (~r2_hidden(B_162, k1_tarski(A_163)) | B_162=A_163)), inference(superposition, [status(thm), theory('equality')], [c_789, c_64])).
% 2.76/1.40  tff(c_843, plain, (![A_163]: ('#skF_5'(k1_tarski(A_163))=A_163 | k1_tarski(A_163)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_836])).
% 2.76/1.40  tff(c_848, plain, (![A_163]: ('#skF_5'(k1_tarski(A_163))=A_163)), inference(negUnitSimplification, [status(thm)], [c_661, c_843])).
% 2.76/1.40  tff(c_52, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.76/1.40  tff(c_576, plain, (![A_127, B_128]: (k1_enumset1(A_127, A_127, B_128)=k2_tarski(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.40  tff(c_34, plain, (![E_20, B_15, C_16]: (r2_hidden(E_20, k1_enumset1(E_20, B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.40  tff(c_594, plain, (![A_129, B_130]: (r2_hidden(A_129, k2_tarski(A_129, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_576, c_34])).
% 2.76/1.40  tff(c_597, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_594])).
% 2.76/1.40  tff(c_900, plain, (![D_173, A_174, C_175]: (~r2_hidden(D_173, A_174) | k4_tarski(C_175, D_173)!='#skF_5'(A_174) | k1_xboole_0=A_174)), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.76/1.40  tff(c_904, plain, (![C_175, A_21]: (k4_tarski(C_175, A_21)!='#skF_5'(k1_tarski(A_21)) | k1_tarski(A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_597, c_900])).
% 2.76/1.40  tff(c_917, plain, (![C_175, A_21]: (k4_tarski(C_175, A_21)!=A_21 | k1_tarski(A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_848, c_904])).
% 2.76/1.40  tff(c_918, plain, (![C_175, A_21]: (k4_tarski(C_175, A_21)!=A_21)), inference(negUnitSimplification, [status(thm)], [c_661, c_917])).
% 2.76/1.40  tff(c_256, plain, (![B_30]: (k1_tarski(B_30)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_60])).
% 2.76/1.40  tff(c_405, plain, (![A_100, B_101]: (k4_xboole_0(k1_tarski(A_100), k1_tarski(B_101))=k1_tarski(A_100) | B_101=A_100)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.40  tff(c_445, plain, (![B_102, A_103]: (~r2_hidden(B_102, k1_tarski(A_103)) | B_102=A_103)), inference(superposition, [status(thm), theory('equality')], [c_405, c_64])).
% 2.76/1.40  tff(c_452, plain, (![A_103]: ('#skF_5'(k1_tarski(A_103))=A_103 | k1_tarski(A_103)=k1_xboole_0)), inference(resolution, [status(thm)], [c_74, c_445])).
% 2.76/1.40  tff(c_457, plain, (![A_103]: ('#skF_5'(k1_tarski(A_103))=A_103)), inference(negUnitSimplification, [status(thm)], [c_256, c_452])).
% 2.76/1.40  tff(c_258, plain, (![A_77, B_78]: (k1_enumset1(A_77, A_77, B_78)=k2_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.40  tff(c_30, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.40  tff(c_291, plain, (![B_82, A_83]: (r2_hidden(B_82, k2_tarski(A_83, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_258, c_30])).
% 2.76/1.40  tff(c_294, plain, (![A_21]: (r2_hidden(A_21, k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_291])).
% 2.76/1.40  tff(c_509, plain, (![C_113, A_114, D_115]: (~r2_hidden(C_113, A_114) | k4_tarski(C_113, D_115)!='#skF_5'(A_114) | k1_xboole_0=A_114)), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.76/1.40  tff(c_513, plain, (![A_21, D_115]: (k4_tarski(A_21, D_115)!='#skF_5'(k1_tarski(A_21)) | k1_tarski(A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_294, c_509])).
% 2.76/1.40  tff(c_526, plain, (![A_21, D_115]: (k4_tarski(A_21, D_115)!=A_21 | k1_tarski(A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_457, c_513])).
% 2.76/1.40  tff(c_527, plain, (![A_21, D_115]: (k4_tarski(A_21, D_115)!=A_21)), inference(negUnitSimplification, [status(thm)], [c_256, c_526])).
% 2.76/1.40  tff(c_82, plain, (k4_tarski('#skF_7', '#skF_8')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.76/1.40  tff(c_126, plain, (![A_54, B_55]: (k1_mcart_1(k4_tarski(A_54, B_55))=A_54)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.76/1.40  tff(c_135, plain, (k1_mcart_1('#skF_6')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_82, c_126])).
% 2.76/1.40  tff(c_114, plain, (![A_52, B_53]: (k2_mcart_1(k4_tarski(A_52, B_53))=B_53)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.76/1.40  tff(c_123, plain, (k2_mcart_1('#skF_6')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_82, c_114])).
% 2.76/1.40  tff(c_80, plain, (k2_mcart_1('#skF_6')='#skF_6' | k1_mcart_1('#skF_6')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.76/1.40  tff(c_156, plain, ('#skF_6'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_123, c_80])).
% 2.76/1.40  tff(c_157, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_156])).
% 2.76/1.40  tff(c_159, plain, (k4_tarski('#skF_6', '#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_82])).
% 2.76/1.40  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_527, c_159])).
% 2.76/1.40  tff(c_535, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_156])).
% 2.76/1.40  tff(c_540, plain, (k4_tarski('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_535, c_82])).
% 2.76/1.40  tff(c_925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_918, c_540])).
% 2.76/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.40  
% 2.76/1.40  Inference rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Ref     : 0
% 2.76/1.40  #Sup     : 210
% 2.76/1.40  #Fact    : 0
% 2.76/1.40  #Define  : 0
% 2.76/1.40  #Split   : 1
% 2.76/1.40  #Chain   : 0
% 2.76/1.40  #Close   : 0
% 2.76/1.40  
% 2.76/1.40  Ordering : KBO
% 2.76/1.40  
% 2.76/1.40  Simplification rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Subsume      : 29
% 2.76/1.40  #Demod        : 36
% 2.76/1.40  #Tautology    : 123
% 2.76/1.40  #SimpNegUnit  : 18
% 2.76/1.40  #BackRed      : 7
% 2.76/1.40  
% 2.76/1.40  #Partial instantiations: 0
% 2.76/1.40  #Strategies tried      : 1
% 2.76/1.40  
% 2.76/1.40  Timing (in seconds)
% 2.76/1.40  ----------------------
% 2.76/1.40  Preprocessing        : 0.34
% 2.76/1.40  Parsing              : 0.18
% 2.76/1.40  CNF conversion       : 0.03
% 2.76/1.40  Main loop            : 0.33
% 2.76/1.40  Inferencing          : 0.11
% 2.76/1.40  Reduction            : 0.10
% 2.76/1.40  Demodulation         : 0.07
% 2.76/1.40  BG Simplification    : 0.02
% 2.76/1.40  Subsumption          : 0.05
% 2.76/1.40  Abstraction          : 0.02
% 2.76/1.40  MUC search           : 0.00
% 2.76/1.40  Cooper               : 0.00
% 2.76/1.40  Total                : 0.70
% 2.76/1.40  Index Insertion      : 0.00
% 2.76/1.40  Index Deletion       : 0.00
% 2.76/1.40  Index Matching       : 0.00
% 2.76/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
