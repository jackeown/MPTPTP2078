%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:11 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 104 expanded)
%              Number of leaves         :   32 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 126 expanded)
%              Number of equality atoms :   40 (  94 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
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

tff(f_98,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_91,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_94,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_476,plain,(
    ! [A_153,B_154] : k1_enumset1(A_153,A_153,B_154) = k2_tarski(A_153,B_154) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [E_8,A_2,C_4] : r2_hidden(E_8,k1_enumset1(A_2,E_8,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_525,plain,(
    ! [A_157,B_158] : r2_hidden(A_157,k2_tarski(A_157,B_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_8])).

tff(c_528,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_525])).

tff(c_169,plain,(
    ! [A_60,B_61] : k1_enumset1(A_60,A_60,B_61) = k2_tarski(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_189,plain,(
    ! [A_62,B_63] : r2_hidden(A_62,k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_8])).

tff(c_192,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_189])).

tff(c_74,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_88,plain,(
    ! [A_38,B_39] : k1_mcart_1(k4_tarski(A_38,B_39)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_97,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_88])).

tff(c_109,plain,(
    ! [A_42,B_43] : k2_mcart_1(k4_tarski(A_42,B_43)) = B_43 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_118,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_109])).

tff(c_72,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_135,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_118,c_72])).

tff(c_136,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_139,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_74])).

tff(c_349,plain,(
    ! [A_109,B_110] : k2_zfmisc_1(k1_tarski(A_109),k1_tarski(B_110)) = k1_tarski(k4_tarski(A_109,B_110)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_40,B_41] : k2_xboole_0(k1_tarski(A_40),B_41) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_108,plain,(
    ! [A_40] : k1_tarski(A_40) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_293,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(k1_tarski(A_92),B_93)
      | ~ r2_hidden(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( ~ r1_tarski(A_23,k2_zfmisc_1(A_23,B_24))
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_297,plain,(
    ! [A_92,B_24] :
      ( k1_tarski(A_92) = k1_xboole_0
      | ~ r2_hidden(A_92,k2_zfmisc_1(k1_tarski(A_92),B_24)) ) ),
    inference(resolution,[status(thm)],[c_293,c_44])).

tff(c_307,plain,(
    ! [A_92,B_24] : ~ r2_hidden(A_92,k2_zfmisc_1(k1_tarski(A_92),B_24)) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_297])).

tff(c_385,plain,(
    ! [A_116,B_117] : ~ r2_hidden(A_116,k1_tarski(k4_tarski(A_116,B_117))) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_307])).

tff(c_388,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_385])).

tff(c_391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_388])).

tff(c_392,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_395,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_74])).

tff(c_611,plain,(
    ! [A_184,B_185] : k2_zfmisc_1(k1_tarski(A_184),k1_tarski(B_185)) = k1_tarski(k4_tarski(A_184,B_185)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_458,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k1_tarski(A_144),B_145)
      | ~ r2_hidden(A_144,B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( ~ r1_tarski(A_23,k2_zfmisc_1(B_24,A_23))
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_466,plain,(
    ! [A_144,B_24] :
      ( k1_tarski(A_144) = k1_xboole_0
      | ~ r2_hidden(A_144,k2_zfmisc_1(B_24,k1_tarski(A_144))) ) ),
    inference(resolution,[status(thm)],[c_458,c_42])).

tff(c_472,plain,(
    ! [A_144,B_24] : ~ r2_hidden(A_144,k2_zfmisc_1(B_24,k1_tarski(A_144))) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_466])).

tff(c_634,plain,(
    ! [B_186,A_187] : ~ r2_hidden(B_186,k1_tarski(k4_tarski(A_187,B_186))) ),
    inference(superposition,[status(thm),theory(equality)],[c_611,c_472])).

tff(c_637,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_634])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:11:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.34  
% 2.72/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.34  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.72/1.34  
% 2.72/1.34  %Foreground sorts:
% 2.72/1.34  
% 2.72/1.34  
% 2.72/1.34  %Background operators:
% 2.72/1.34  
% 2.72/1.34  
% 2.72/1.34  %Foreground operators:
% 2.72/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.72/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.72/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.34  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.72/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.72/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.34  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.72/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.72/1.34  
% 2.72/1.36  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.72/1.36  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.72/1.36  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.72/1.36  tff(f_108, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.72/1.36  tff(f_98, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.72/1.36  tff(f_91, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 2.72/1.36  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.72/1.36  tff(f_94, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.72/1.36  tff(f_54, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.72/1.36  tff(f_62, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.72/1.36  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.72/1.36  tff(c_476, plain, (![A_153, B_154]: (k1_enumset1(A_153, A_153, B_154)=k2_tarski(A_153, B_154))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.72/1.36  tff(c_8, plain, (![E_8, A_2, C_4]: (r2_hidden(E_8, k1_enumset1(A_2, E_8, C_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.72/1.36  tff(c_525, plain, (![A_157, B_158]: (r2_hidden(A_157, k2_tarski(A_157, B_158)))), inference(superposition, [status(thm), theory('equality')], [c_476, c_8])).
% 2.72/1.36  tff(c_528, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_525])).
% 2.72/1.36  tff(c_169, plain, (![A_60, B_61]: (k1_enumset1(A_60, A_60, B_61)=k2_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.72/1.36  tff(c_189, plain, (![A_62, B_63]: (r2_hidden(A_62, k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_169, c_8])).
% 2.72/1.36  tff(c_192, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_189])).
% 2.72/1.36  tff(c_74, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.36  tff(c_88, plain, (![A_38, B_39]: (k1_mcart_1(k4_tarski(A_38, B_39))=A_38)), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.72/1.36  tff(c_97, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_74, c_88])).
% 2.72/1.36  tff(c_109, plain, (![A_42, B_43]: (k2_mcart_1(k4_tarski(A_42, B_43))=B_43)), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.72/1.36  tff(c_118, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_74, c_109])).
% 2.72/1.36  tff(c_72, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.72/1.36  tff(c_135, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_118, c_72])).
% 2.72/1.36  tff(c_136, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_135])).
% 2.72/1.36  tff(c_139, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_74])).
% 2.72/1.36  tff(c_349, plain, (![A_109, B_110]: (k2_zfmisc_1(k1_tarski(A_109), k1_tarski(B_110))=k1_tarski(k4_tarski(A_109, B_110)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.72/1.36  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.36  tff(c_104, plain, (![A_40, B_41]: (k2_xboole_0(k1_tarski(A_40), B_41)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.72/1.36  tff(c_108, plain, (![A_40]: (k1_tarski(A_40)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_104])).
% 2.72/1.36  tff(c_293, plain, (![A_92, B_93]: (r1_tarski(k1_tarski(A_92), B_93) | ~r2_hidden(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.72/1.36  tff(c_44, plain, (![A_23, B_24]: (~r1_tarski(A_23, k2_zfmisc_1(A_23, B_24)) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.72/1.36  tff(c_297, plain, (![A_92, B_24]: (k1_tarski(A_92)=k1_xboole_0 | ~r2_hidden(A_92, k2_zfmisc_1(k1_tarski(A_92), B_24)))), inference(resolution, [status(thm)], [c_293, c_44])).
% 2.72/1.36  tff(c_307, plain, (![A_92, B_24]: (~r2_hidden(A_92, k2_zfmisc_1(k1_tarski(A_92), B_24)))), inference(negUnitSimplification, [status(thm)], [c_108, c_297])).
% 2.72/1.36  tff(c_385, plain, (![A_116, B_117]: (~r2_hidden(A_116, k1_tarski(k4_tarski(A_116, B_117))))), inference(superposition, [status(thm), theory('equality')], [c_349, c_307])).
% 2.72/1.36  tff(c_388, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_385])).
% 2.72/1.36  tff(c_391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_388])).
% 2.72/1.36  tff(c_392, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_135])).
% 2.72/1.36  tff(c_395, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_392, c_74])).
% 2.72/1.36  tff(c_611, plain, (![A_184, B_185]: (k2_zfmisc_1(k1_tarski(A_184), k1_tarski(B_185))=k1_tarski(k4_tarski(A_184, B_185)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.72/1.36  tff(c_458, plain, (![A_144, B_145]: (r1_tarski(k1_tarski(A_144), B_145) | ~r2_hidden(A_144, B_145))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.72/1.36  tff(c_42, plain, (![A_23, B_24]: (~r1_tarski(A_23, k2_zfmisc_1(B_24, A_23)) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.72/1.36  tff(c_466, plain, (![A_144, B_24]: (k1_tarski(A_144)=k1_xboole_0 | ~r2_hidden(A_144, k2_zfmisc_1(B_24, k1_tarski(A_144))))), inference(resolution, [status(thm)], [c_458, c_42])).
% 2.72/1.36  tff(c_472, plain, (![A_144, B_24]: (~r2_hidden(A_144, k2_zfmisc_1(B_24, k1_tarski(A_144))))), inference(negUnitSimplification, [status(thm)], [c_108, c_466])).
% 2.72/1.36  tff(c_634, plain, (![B_186, A_187]: (~r2_hidden(B_186, k1_tarski(k4_tarski(A_187, B_186))))), inference(superposition, [status(thm), theory('equality')], [c_611, c_472])).
% 2.72/1.36  tff(c_637, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_395, c_634])).
% 2.72/1.36  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_528, c_637])).
% 2.72/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.36  
% 2.72/1.36  Inference rules
% 2.72/1.36  ----------------------
% 2.72/1.36  #Ref     : 0
% 2.72/1.36  #Sup     : 132
% 2.72/1.36  #Fact    : 0
% 2.72/1.36  #Define  : 0
% 2.72/1.36  #Split   : 1
% 2.72/1.36  #Chain   : 0
% 2.72/1.36  #Close   : 0
% 2.72/1.36  
% 2.72/1.36  Ordering : KBO
% 2.72/1.36  
% 2.72/1.36  Simplification rules
% 2.72/1.36  ----------------------
% 2.72/1.36  #Subsume      : 0
% 2.72/1.36  #Demod        : 58
% 2.72/1.36  #Tautology    : 92
% 2.72/1.36  #SimpNegUnit  : 8
% 2.72/1.36  #BackRed      : 5
% 2.72/1.36  
% 2.72/1.36  #Partial instantiations: 0
% 2.72/1.36  #Strategies tried      : 1
% 2.72/1.36  
% 2.72/1.36  Timing (in seconds)
% 2.72/1.36  ----------------------
% 2.72/1.36  Preprocessing        : 0.33
% 2.72/1.36  Parsing              : 0.17
% 2.72/1.36  CNF conversion       : 0.02
% 2.72/1.36  Main loop            : 0.27
% 2.72/1.36  Inferencing          : 0.10
% 2.72/1.36  Reduction            : 0.09
% 2.72/1.36  Demodulation         : 0.07
% 2.72/1.36  BG Simplification    : 0.02
% 2.72/1.36  Subsumption          : 0.04
% 2.72/1.36  Abstraction          : 0.02
% 2.72/1.36  MUC search           : 0.00
% 2.72/1.36  Cooper               : 0.00
% 2.72/1.36  Total                : 0.64
% 2.72/1.36  Index Insertion      : 0.00
% 2.72/1.36  Index Deletion       : 0.00
% 2.72/1.36  Index Matching       : 0.00
% 2.72/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
