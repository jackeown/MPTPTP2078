%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:52 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   45 (  54 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  56 expanded)
%              Number of equality atoms :   42 (  55 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_28,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [A_30,B_31] : k4_xboole_0(k1_tarski(A_30),k2_tarski(A_30,B_31)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_98,plain,(
    ! [A_10] : k4_xboole_0(k1_tarski(A_10),k1_tarski(A_10)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_91])).

tff(c_20,plain,(
    ! [B_17] : k4_xboole_0(k1_tarski(B_17),k1_tarski(B_17)) != k1_tarski(B_17) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_101,plain,(
    ! [B_17] : k1_tarski(B_17) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_20])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_190,plain,(
    ! [A_39] : k4_xboole_0(A_39,A_39) = k3_xboole_0(A_39,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_110])).

tff(c_228,plain,(
    ! [A_40] : k3_xboole_0(k1_tarski(A_40),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_98])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_233,plain,(
    ! [A_40] : k5_xboole_0(k1_tarski(A_40),k1_xboole_0) = k4_xboole_0(k1_tarski(A_40),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_2])).

tff(c_237,plain,(
    ! [A_40] : k5_xboole_0(k1_tarski(A_40),k1_xboole_0) = k1_tarski(A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_233])).

tff(c_32,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_262,plain,(
    ! [A_43,B_44] : k5_xboole_0(A_43,k4_xboole_0(B_44,A_43)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_283,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_262])).

tff(c_293,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_283])).

tff(c_563,plain,(
    ! [C_60,B_61,A_62] :
      ( k1_xboole_0 = C_60
      | k1_xboole_0 = B_61
      | C_60 = B_61
      | k2_xboole_0(B_61,C_60) != k1_tarski(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_569,plain,(
    ! [A_62] :
      ( k1_xboole_0 = '#skF_1'
      | k1_tarski('#skF_2') = k1_xboole_0
      | k1_tarski('#skF_2') = '#skF_1'
      | k1_tarski(A_62) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_563])).

tff(c_574,plain,(
    ! [A_62] : k1_tarski(A_62) != k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_101,c_30,c_569])).

tff(c_579,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:44:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.09/1.30  
% 2.09/1.30  %Foreground sorts:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Background operators:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Foreground operators:
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.30  
% 2.09/1.31  tff(f_72, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.09/1.31  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.09/1.31  tff(f_50, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 2.09/1.31  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.09/1.31  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.09/1.31  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.09/1.31  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.09/1.31  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.09/1.31  tff(f_62, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.09/1.31  tff(c_28, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.31  tff(c_14, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.31  tff(c_91, plain, (![A_30, B_31]: (k4_xboole_0(k1_tarski(A_30), k2_tarski(A_30, B_31))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.09/1.31  tff(c_98, plain, (![A_10]: (k4_xboole_0(k1_tarski(A_10), k1_tarski(A_10))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_91])).
% 2.09/1.31  tff(c_20, plain, (![B_17]: (k4_xboole_0(k1_tarski(B_17), k1_tarski(B_17))!=k1_tarski(B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.09/1.31  tff(c_101, plain, (![B_17]: (k1_tarski(B_17)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_20])).
% 2.09/1.31  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.31  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.31  tff(c_110, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.31  tff(c_190, plain, (![A_39]: (k4_xboole_0(A_39, A_39)=k3_xboole_0(A_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_110])).
% 2.09/1.31  tff(c_228, plain, (![A_40]: (k3_xboole_0(k1_tarski(A_40), k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_190, c_98])).
% 2.09/1.31  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.31  tff(c_233, plain, (![A_40]: (k5_xboole_0(k1_tarski(A_40), k1_xboole_0)=k4_xboole_0(k1_tarski(A_40), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_228, c_2])).
% 2.09/1.31  tff(c_237, plain, (![A_40]: (k5_xboole_0(k1_tarski(A_40), k1_xboole_0)=k1_tarski(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_233])).
% 2.09/1.31  tff(c_32, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.31  tff(c_262, plain, (![A_43, B_44]: (k5_xboole_0(A_43, k4_xboole_0(B_44, A_43))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.31  tff(c_283, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_262])).
% 2.09/1.31  tff(c_293, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_283])).
% 2.09/1.31  tff(c_563, plain, (![C_60, B_61, A_62]: (k1_xboole_0=C_60 | k1_xboole_0=B_61 | C_60=B_61 | k2_xboole_0(B_61, C_60)!=k1_tarski(A_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.31  tff(c_569, plain, (![A_62]: (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0 | k1_tarski('#skF_2')='#skF_1' | k1_tarski(A_62)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_563])).
% 2.09/1.31  tff(c_574, plain, (![A_62]: (k1_tarski(A_62)!=k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_28, c_101, c_30, c_569])).
% 2.09/1.31  tff(c_579, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_574])).
% 2.09/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.31  
% 2.09/1.31  Inference rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Ref     : 1
% 2.09/1.31  #Sup     : 129
% 2.09/1.31  #Fact    : 0
% 2.09/1.31  #Define  : 0
% 2.09/1.31  #Split   : 0
% 2.09/1.31  #Chain   : 0
% 2.09/1.31  #Close   : 0
% 2.09/1.31  
% 2.09/1.31  Ordering : KBO
% 2.09/1.31  
% 2.09/1.31  Simplification rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Subsume      : 0
% 2.09/1.31  #Demod        : 66
% 2.09/1.31  #Tautology    : 105
% 2.09/1.31  #SimpNegUnit  : 5
% 2.09/1.31  #BackRed      : 2
% 2.09/1.31  
% 2.09/1.31  #Partial instantiations: 0
% 2.09/1.31  #Strategies tried      : 1
% 2.09/1.31  
% 2.09/1.31  Timing (in seconds)
% 2.09/1.31  ----------------------
% 2.09/1.31  Preprocessing        : 0.30
% 2.09/1.31  Parsing              : 0.16
% 2.09/1.31  CNF conversion       : 0.02
% 2.09/1.31  Main loop            : 0.22
% 2.09/1.31  Inferencing          : 0.09
% 2.09/1.31  Reduction            : 0.08
% 2.09/1.31  Demodulation         : 0.06
% 2.09/1.31  BG Simplification    : 0.01
% 2.09/1.31  Subsumption          : 0.03
% 2.09/1.31  Abstraction          : 0.01
% 2.41/1.31  MUC search           : 0.00
% 2.41/1.31  Cooper               : 0.00
% 2.41/1.31  Total                : 0.55
% 2.41/1.31  Index Insertion      : 0.00
% 2.41/1.31  Index Deletion       : 0.00
% 2.41/1.31  Index Matching       : 0.00
% 2.41/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
