%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:03 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   62 (  78 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 (  95 expanded)
%              Number of equality atoms :   38 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_54,plain,(
    ! [B_46] : k2_zfmisc_1(k1_xboole_0,B_46) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_138,plain,(
    ! [A_66,B_67] : r1_xboole_0(k3_xboole_0(A_66,B_67),k5_xboole_0(A_66,B_67)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_141,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,k5_xboole_0(A_8,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_145,plain,(
    ! [A_8] : r1_xboole_0(k1_xboole_0,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_141])).

tff(c_180,plain,(
    ! [A_73,B_74,C_75] :
      ( ~ r1_xboole_0(A_73,B_74)
      | ~ r2_hidden(C_75,k3_xboole_0(A_73,B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_183,plain,(
    ! [A_8,C_75] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_75,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_180])).

tff(c_184,plain,(
    ! [C_75] : ~ r2_hidden(C_75,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_56,plain,
    ( k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_109,plain,(
    k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_154,plain,(
    ! [B_71,A_72] :
      ( k1_xboole_0 = B_71
      | k1_xboole_0 = A_72
      | k2_zfmisc_1(A_72,B_71) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_157,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_154])).

tff(c_166,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_157])).

tff(c_36,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_114,plain,(
    ! [A_61,B_62] : k1_enumset1(A_61,A_61,B_62) = k2_tarski(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_132,plain,(
    ! [A_63,B_64] : r2_hidden(A_63,k2_tarski(A_63,B_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_18])).

tff(c_135,plain,(
    ! [A_17] : r2_hidden(A_17,k1_tarski(A_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_132])).

tff(c_176,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_135])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_176])).

tff(c_197,plain,(
    ! [A_79] : ~ r1_xboole_0(A_79,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_202,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_145,c_197])).

tff(c_203,plain,(
    k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_247,plain,(
    ! [B_89,A_90] :
      ( k1_xboole_0 = B_89
      | k1_xboole_0 = A_90
      | k2_zfmisc_1(A_90,B_89) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_250,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_247])).

tff(c_259,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_250])).

tff(c_204,plain,(
    k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_266,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_204])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.25  
% 2.23/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.25  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.23/1.25  
% 2.23/1.25  %Foreground sorts:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Background operators:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Foreground operators:
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.23/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.25  
% 2.23/1.26  tff(f_80, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.23/1.26  tff(f_90, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.23/1.26  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.23/1.26  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.23/1.26  tff(f_41, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.23/1.26  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.23/1.26  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.23/1.26  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.23/1.26  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.23/1.26  tff(c_54, plain, (![B_46]: (k2_zfmisc_1(k1_xboole_0, B_46)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.23/1.26  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.23/1.26  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.26  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.23/1.26  tff(c_138, plain, (![A_66, B_67]: (r1_xboole_0(k3_xboole_0(A_66, B_67), k5_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.26  tff(c_141, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, k5_xboole_0(A_8, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_138])).
% 2.23/1.26  tff(c_145, plain, (![A_8]: (r1_xboole_0(k1_xboole_0, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_141])).
% 2.23/1.26  tff(c_180, plain, (![A_73, B_74, C_75]: (~r1_xboole_0(A_73, B_74) | ~r2_hidden(C_75, k3_xboole_0(A_73, B_74)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.23/1.26  tff(c_183, plain, (![A_8, C_75]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_75, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_180])).
% 2.23/1.26  tff(c_184, plain, (![C_75]: (~r2_hidden(C_75, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_183])).
% 2.23/1.26  tff(c_56, plain, (k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.23/1.26  tff(c_109, plain, (k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 2.23/1.26  tff(c_154, plain, (![B_71, A_72]: (k1_xboole_0=B_71 | k1_xboole_0=A_72 | k2_zfmisc_1(A_72, B_71)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.23/1.26  tff(c_157, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_109, c_154])).
% 2.23/1.26  tff(c_166, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_157])).
% 2.23/1.26  tff(c_36, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.26  tff(c_114, plain, (![A_61, B_62]: (k1_enumset1(A_61, A_61, B_62)=k2_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.26  tff(c_18, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.26  tff(c_132, plain, (![A_63, B_64]: (r2_hidden(A_63, k2_tarski(A_63, B_64)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_18])).
% 2.23/1.26  tff(c_135, plain, (![A_17]: (r2_hidden(A_17, k1_tarski(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_132])).
% 2.23/1.26  tff(c_176, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_166, c_135])).
% 2.23/1.26  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_176])).
% 2.23/1.26  tff(c_197, plain, (![A_79]: (~r1_xboole_0(A_79, k1_xboole_0))), inference(splitRight, [status(thm)], [c_183])).
% 2.23/1.26  tff(c_202, plain, $false, inference(resolution, [status(thm)], [c_145, c_197])).
% 2.23/1.26  tff(c_203, plain, (k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.23/1.26  tff(c_247, plain, (![B_89, A_90]: (k1_xboole_0=B_89 | k1_xboole_0=A_90 | k2_zfmisc_1(A_90, B_89)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.23/1.26  tff(c_250, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_203, c_247])).
% 2.23/1.26  tff(c_259, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_58, c_250])).
% 2.23/1.26  tff(c_204, plain, (k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 2.23/1.26  tff(c_266, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_259, c_204])).
% 2.23/1.26  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_266])).
% 2.23/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.26  
% 2.23/1.26  Inference rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Ref     : 0
% 2.23/1.26  #Sup     : 47
% 2.23/1.26  #Fact    : 0
% 2.23/1.26  #Define  : 0
% 2.23/1.26  #Split   : 2
% 2.23/1.26  #Chain   : 0
% 2.23/1.26  #Close   : 0
% 2.23/1.26  
% 2.23/1.26  Ordering : KBO
% 2.23/1.26  
% 2.23/1.26  Simplification rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Subsume      : 0
% 2.23/1.27  #Demod        : 15
% 2.23/1.27  #Tautology    : 35
% 2.23/1.27  #SimpNegUnit  : 3
% 2.23/1.27  #BackRed      : 4
% 2.23/1.27  
% 2.23/1.27  #Partial instantiations: 0
% 2.23/1.27  #Strategies tried      : 1
% 2.23/1.27  
% 2.23/1.27  Timing (in seconds)
% 2.23/1.27  ----------------------
% 2.23/1.27  Preprocessing        : 0.33
% 2.23/1.27  Parsing              : 0.18
% 2.23/1.27  CNF conversion       : 0.02
% 2.23/1.27  Main loop            : 0.17
% 2.23/1.27  Inferencing          : 0.05
% 2.23/1.27  Reduction            : 0.06
% 2.23/1.27  Demodulation         : 0.04
% 2.23/1.27  BG Simplification    : 0.02
% 2.23/1.27  Subsumption          : 0.03
% 2.23/1.27  Abstraction          : 0.01
% 2.23/1.27  MUC search           : 0.00
% 2.23/1.27  Cooper               : 0.00
% 2.23/1.27  Total                : 0.53
% 2.23/1.27  Index Insertion      : 0.00
% 2.23/1.27  Index Deletion       : 0.00
% 2.23/1.27  Index Matching       : 0.00
% 2.23/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
