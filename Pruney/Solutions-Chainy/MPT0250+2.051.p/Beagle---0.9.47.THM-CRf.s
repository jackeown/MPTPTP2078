%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:38 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :   58 (  71 expanded)
%              Number of leaves         :   30 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  68 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_42,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_258,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_270,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_258])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_353,plain,(
    ! [A_102,B_103,C_104] : k5_xboole_0(k5_xboole_0(A_102,B_103),C_104) = k5_xboole_0(A_102,k5_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1507,plain,(
    ! [A_152,B_153,C_154] : k5_xboole_0(A_152,k5_xboole_0(k3_xboole_0(A_152,B_153),C_154)) = k5_xboole_0(k4_xboole_0(A_152,B_153),C_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_353])).

tff(c_4445,plain,(
    ! [A_183,B_184,B_185] : k5_xboole_0(A_183,k5_xboole_0(B_184,k3_xboole_0(A_183,B_185))) = k5_xboole_0(k4_xboole_0(A_183,B_185),B_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1507])).

tff(c_4613,plain,(
    ! [A_1,B_2] : k5_xboole_0(k4_xboole_0(A_1,B_2),B_2) = k5_xboole_0(A_1,k4_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_4445])).

tff(c_4661,plain,(
    ! [A_186,B_187] : k5_xboole_0(k4_xboole_0(A_186,B_187),B_187) = k2_xboole_0(A_186,B_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4613])).

tff(c_4834,plain,(
    ! [B_188,A_189] : k5_xboole_0(B_188,k4_xboole_0(A_189,B_188)) = k2_xboole_0(A_189,B_188) ),
    inference(superposition,[status(thm),theory(equality)],[c_4661,c_4])).

tff(c_4915,plain,(
    ! [B_188,A_189] : k2_xboole_0(B_188,A_189) = k2_xboole_0(A_189,B_188) ),
    inference(superposition,[status(thm),theory(equality)],[c_4834,c_18])).

tff(c_44,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_144,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_144])).

tff(c_241,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_4950,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4915,c_241])).

tff(c_4954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4950])).

tff(c_4955,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_20,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_185,plain,(
    ! [A_65,C_66,B_67] :
      ( r2_hidden(A_65,C_66)
      | ~ r1_tarski(k2_tarski(A_65,B_67),C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_218,plain,(
    ! [A_73,C_74] :
      ( r2_hidden(A_73,C_74)
      | ~ r1_tarski(k1_tarski(A_73),C_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_185])).

tff(c_232,plain,(
    ! [A_73,B_10] : r2_hidden(A_73,k2_xboole_0(k1_tarski(A_73),B_10)) ),
    inference(resolution,[status(thm)],[c_14,c_218])).

tff(c_4962,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4955,c_232])).

tff(c_4969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.01/2.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.84  
% 8.01/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.84  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 8.01/2.84  
% 8.01/2.84  %Foreground sorts:
% 8.01/2.84  
% 8.01/2.84  
% 8.01/2.84  %Background operators:
% 8.01/2.84  
% 8.01/2.84  
% 8.01/2.84  %Foreground operators:
% 8.01/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.01/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.01/2.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.01/2.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.01/2.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.01/2.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.01/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.01/2.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.01/2.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.01/2.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.01/2.84  tff('#skF_2', type, '#skF_2': $i).
% 8.01/2.84  tff('#skF_1', type, '#skF_1': $i).
% 8.01/2.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.01/2.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.01/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.01/2.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.01/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.01/2.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.01/2.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.01/2.84  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.01/2.84  
% 8.01/2.85  tff(f_70, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 8.01/2.85  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.01/2.85  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.01/2.85  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.01/2.85  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.01/2.85  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.01/2.85  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.01/2.85  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.01/2.85  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 8.01/2.85  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 8.01/2.85  tff(c_42, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.01/2.85  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.01/2.85  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.01/2.85  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.01/2.85  tff(c_258, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.01/2.85  tff(c_270, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_258])).
% 8.01/2.85  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.01/2.85  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.01/2.85  tff(c_353, plain, (![A_102, B_103, C_104]: (k5_xboole_0(k5_xboole_0(A_102, B_103), C_104)=k5_xboole_0(A_102, k5_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.01/2.85  tff(c_1507, plain, (![A_152, B_153, C_154]: (k5_xboole_0(A_152, k5_xboole_0(k3_xboole_0(A_152, B_153), C_154))=k5_xboole_0(k4_xboole_0(A_152, B_153), C_154))), inference(superposition, [status(thm), theory('equality')], [c_12, c_353])).
% 8.01/2.85  tff(c_4445, plain, (![A_183, B_184, B_185]: (k5_xboole_0(A_183, k5_xboole_0(B_184, k3_xboole_0(A_183, B_185)))=k5_xboole_0(k4_xboole_0(A_183, B_185), B_184))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1507])).
% 8.01/2.85  tff(c_4613, plain, (![A_1, B_2]: (k5_xboole_0(k4_xboole_0(A_1, B_2), B_2)=k5_xboole_0(A_1, k4_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_4445])).
% 8.01/2.85  tff(c_4661, plain, (![A_186, B_187]: (k5_xboole_0(k4_xboole_0(A_186, B_187), B_187)=k2_xboole_0(A_186, B_187))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4613])).
% 8.01/2.85  tff(c_4834, plain, (![B_188, A_189]: (k5_xboole_0(B_188, k4_xboole_0(A_189, B_188))=k2_xboole_0(A_189, B_188))), inference(superposition, [status(thm), theory('equality')], [c_4661, c_4])).
% 8.01/2.85  tff(c_4915, plain, (![B_188, A_189]: (k2_xboole_0(B_188, A_189)=k2_xboole_0(A_189, B_188))), inference(superposition, [status(thm), theory('equality')], [c_4834, c_18])).
% 8.01/2.85  tff(c_44, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.01/2.85  tff(c_144, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.01/2.85  tff(c_151, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_144])).
% 8.01/2.85  tff(c_241, plain, (~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_151])).
% 8.01/2.85  tff(c_4950, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4915, c_241])).
% 8.01/2.85  tff(c_4954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_4950])).
% 8.01/2.85  tff(c_4955, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_151])).
% 8.01/2.85  tff(c_20, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.01/2.85  tff(c_185, plain, (![A_65, C_66, B_67]: (r2_hidden(A_65, C_66) | ~r1_tarski(k2_tarski(A_65, B_67), C_66))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.01/2.85  tff(c_218, plain, (![A_73, C_74]: (r2_hidden(A_73, C_74) | ~r1_tarski(k1_tarski(A_73), C_74))), inference(superposition, [status(thm), theory('equality')], [c_20, c_185])).
% 8.01/2.85  tff(c_232, plain, (![A_73, B_10]: (r2_hidden(A_73, k2_xboole_0(k1_tarski(A_73), B_10)))), inference(resolution, [status(thm)], [c_14, c_218])).
% 8.01/2.85  tff(c_4962, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4955, c_232])).
% 8.01/2.85  tff(c_4969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_4962])).
% 8.01/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.01/2.85  
% 8.01/2.85  Inference rules
% 8.01/2.85  ----------------------
% 8.01/2.85  #Ref     : 0
% 8.01/2.85  #Sup     : 1254
% 8.01/2.85  #Fact    : 0
% 8.01/2.85  #Define  : 0
% 8.01/2.85  #Split   : 1
% 8.01/2.85  #Chain   : 0
% 8.01/2.85  #Close   : 0
% 8.01/2.85  
% 8.01/2.85  Ordering : KBO
% 8.01/2.85  
% 8.01/2.85  Simplification rules
% 8.01/2.85  ----------------------
% 8.01/2.85  #Subsume      : 167
% 8.01/2.85  #Demod        : 850
% 8.01/2.85  #Tautology    : 216
% 8.01/2.85  #SimpNegUnit  : 1
% 8.01/2.85  #BackRed      : 3
% 8.01/2.85  
% 8.01/2.85  #Partial instantiations: 0
% 8.01/2.85  #Strategies tried      : 1
% 8.01/2.85  
% 8.01/2.85  Timing (in seconds)
% 8.01/2.85  ----------------------
% 8.01/2.85  Preprocessing        : 0.34
% 8.01/2.85  Parsing              : 0.18
% 8.01/2.85  CNF conversion       : 0.02
% 8.01/2.85  Main loop            : 1.74
% 8.01/2.85  Inferencing          : 0.36
% 8.01/2.85  Reduction            : 1.10
% 8.01/2.85  Demodulation         : 1.02
% 8.01/2.85  BG Simplification    : 0.06
% 8.01/2.85  Subsumption          : 0.16
% 8.01/2.85  Abstraction          : 0.09
% 8.01/2.85  MUC search           : 0.00
% 8.01/2.85  Cooper               : 0.00
% 8.01/2.85  Total                : 2.11
% 8.01/2.86  Index Insertion      : 0.00
% 8.01/2.86  Index Deletion       : 0.00
% 8.01/2.86  Index Matching       : 0.00
% 8.01/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
