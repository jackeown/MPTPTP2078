%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:25 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   54 (  63 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  65 expanded)
%              Number of equality atoms :   41 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_50,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [A_28,B_29] : k2_xboole_0(k1_tarski(A_28),k1_tarski(B_29)) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_333,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_348,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_333])).

tff(c_352,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_348])).

tff(c_52,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_345,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_333])).

tff(c_388,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_345])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_392,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_10])).

tff(c_395,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_392])).

tff(c_94,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_100,plain,(
    ! [B_56,A_55] : r2_hidden(B_56,k2_tarski(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_14])).

tff(c_409,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_100])).

tff(c_42,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_726,plain,(
    ! [E_102,C_103,B_104,A_105] :
      ( E_102 = C_103
      | E_102 = B_104
      | E_102 = A_105
      | ~ r2_hidden(E_102,k1_enumset1(A_105,B_104,C_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_824,plain,(
    ! [E_116,B_117,A_118] :
      ( E_116 = B_117
      | E_116 = A_118
      | E_116 = A_118
      | ~ r2_hidden(E_116,k2_tarski(A_118,B_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_726])).

tff(c_841,plain,(
    ! [E_119,A_120] :
      ( E_119 = A_120
      | E_119 = A_120
      | E_119 = A_120
      | ~ r2_hidden(E_119,k1_tarski(A_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_824])).

tff(c_844,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_409,c_841])).

tff(c_851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_50,c_844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/2.25  
% 3.29/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/2.26  %$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.29/2.26  
% 3.29/2.26  %Foreground sorts:
% 3.29/2.26  
% 3.29/2.26  
% 3.29/2.26  %Background operators:
% 3.29/2.26  
% 3.29/2.26  
% 3.29/2.26  %Foreground operators:
% 3.29/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/2.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/2.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/2.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.29/2.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/2.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/2.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.29/2.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/2.26  tff('#skF_3', type, '#skF_3': $i).
% 3.29/2.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.29/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/2.26  tff('#skF_4', type, '#skF_4': $i).
% 3.29/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/2.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/2.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.29/2.26  
% 3.29/2.27  tff(f_69, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.29/2.27  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.29/2.27  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.29/2.27  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.29/2.27  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.29/2.27  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.29/2.27  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.29/2.27  tff(f_60, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.29/2.27  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.29/2.27  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.29/2.27  tff(c_50, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/2.27  tff(c_40, plain, (![A_28, B_29]: (k2_xboole_0(k1_tarski(A_28), k1_tarski(B_29))=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.29/2.27  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/2.27  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/2.27  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/2.27  tff(c_333, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/2.27  tff(c_348, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_333])).
% 3.29/2.27  tff(c_352, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_348])).
% 3.29/2.27  tff(c_52, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/2.27  tff(c_345, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_333])).
% 3.29/2.27  tff(c_388, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_352, c_345])).
% 3.29/2.27  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/2.27  tff(c_392, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_388, c_10])).
% 3.29/2.27  tff(c_395, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_392])).
% 3.29/2.27  tff(c_94, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/2.27  tff(c_14, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.29/2.27  tff(c_100, plain, (![B_56, A_55]: (r2_hidden(B_56, k2_tarski(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_14])).
% 3.29/2.27  tff(c_409, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_395, c_100])).
% 3.29/2.27  tff(c_42, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.29/2.27  tff(c_44, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/2.27  tff(c_726, plain, (![E_102, C_103, B_104, A_105]: (E_102=C_103 | E_102=B_104 | E_102=A_105 | ~r2_hidden(E_102, k1_enumset1(A_105, B_104, C_103)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.29/2.27  tff(c_824, plain, (![E_116, B_117, A_118]: (E_116=B_117 | E_116=A_118 | E_116=A_118 | ~r2_hidden(E_116, k2_tarski(A_118, B_117)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_726])).
% 3.29/2.27  tff(c_841, plain, (![E_119, A_120]: (E_119=A_120 | E_119=A_120 | E_119=A_120 | ~r2_hidden(E_119, k1_tarski(A_120)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_824])).
% 3.29/2.27  tff(c_844, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_409, c_841])).
% 3.29/2.27  tff(c_851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_50, c_844])).
% 3.29/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/2.27  
% 3.29/2.27  Inference rules
% 3.29/2.27  ----------------------
% 3.29/2.27  #Ref     : 0
% 3.29/2.27  #Sup     : 194
% 3.29/2.27  #Fact    : 0
% 3.29/2.27  #Define  : 0
% 3.29/2.27  #Split   : 0
% 3.29/2.27  #Chain   : 0
% 3.29/2.27  #Close   : 0
% 3.29/2.27  
% 3.29/2.27  Ordering : KBO
% 3.29/2.27  
% 3.29/2.27  Simplification rules
% 3.29/2.27  ----------------------
% 3.29/2.27  #Subsume      : 0
% 3.29/2.27  #Demod        : 185
% 3.29/2.27  #Tautology    : 165
% 3.29/2.27  #SimpNegUnit  : 1
% 3.29/2.27  #BackRed      : 0
% 3.29/2.27  
% 3.29/2.27  #Partial instantiations: 0
% 3.29/2.27  #Strategies tried      : 1
% 3.29/2.27  
% 3.29/2.27  Timing (in seconds)
% 3.29/2.27  ----------------------
% 3.29/2.28  Preprocessing        : 0.68
% 3.29/2.28  Parsing              : 0.32
% 3.29/2.28  CNF conversion       : 0.06
% 3.29/2.28  Main loop            : 0.65
% 3.29/2.28  Inferencing          : 0.20
% 3.29/2.28  Reduction            : 0.27
% 3.29/2.28  Demodulation         : 0.21
% 3.29/2.28  BG Simplification    : 0.05
% 3.29/2.28  Subsumption          : 0.09
% 3.29/2.28  Abstraction          : 0.05
% 3.29/2.28  MUC search           : 0.00
% 3.29/2.28  Cooper               : 0.00
% 3.29/2.28  Total                : 1.38
% 3.42/2.28  Index Insertion      : 0.00
% 3.42/2.28  Index Deletion       : 0.00
% 3.42/2.28  Index Matching       : 0.00
% 3.42/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
