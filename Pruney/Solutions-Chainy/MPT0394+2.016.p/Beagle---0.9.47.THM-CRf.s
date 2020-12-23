%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:23 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   50 (  69 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  79 expanded)
%              Number of equality atoms :   37 (  54 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

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
    ! [A_23] : k2_tarski(A_23,A_23) = k1_tarski(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_89,plain,(
    ! [A_52,B_53] : k1_enumset1(A_52,A_52,B_53) = k2_tarski(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [E_11,A_5,B_6] : r2_hidden(E_11,k1_enumset1(A_5,B_6,E_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_107,plain,(
    ! [B_54,A_55] : r2_hidden(B_54,k2_tarski(A_55,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_10])).

tff(c_110,plain,(
    ! [A_23] : r2_hidden(A_23,k1_tarski(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_107])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [A_59,B_60] :
      ( ~ r2_hidden(A_59,B_60)
      | ~ r1_xboole_0(k1_tarski(A_59),B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_191,plain,(
    ! [A_70,B_71] :
      ( ~ r2_hidden(A_70,B_71)
      | k3_xboole_0(k1_tarski(A_70),B_71) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_118])).

tff(c_195,plain,(
    ! [A_70] :
      ( ~ r2_hidden(A_70,k1_tarski(A_70))
      | k1_tarski(A_70) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_191])).

tff(c_197,plain,(
    ! [A_70] : k1_tarski(A_70) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_195])).

tff(c_50,plain,(
    ! [A_35] : k1_setfam_1(k1_tarski(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_309,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(k1_setfam_1(A_91),k1_setfam_1(B_92)) = k1_setfam_1(k2_xboole_0(A_91,B_92))
      | k1_xboole_0 = B_92
      | k1_xboole_0 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_326,plain,(
    ! [A_35,B_92] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_35),B_92)) = k3_xboole_0(A_35,k1_setfam_1(B_92))
      | k1_xboole_0 = B_92
      | k1_tarski(A_35) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_309])).

tff(c_532,plain,(
    ! [A_110,B_111] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(A_110),B_111)) = k3_xboole_0(A_110,k1_setfam_1(B_111))
      | k1_xboole_0 = B_111 ) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_326])).

tff(c_570,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,k1_setfam_1(k1_tarski(B_13))) = k1_setfam_1(k2_tarski(A_12,B_13))
      | k1_tarski(B_13) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_532])).

tff(c_583,plain,(
    ! [A_12,B_13] :
      ( k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13)
      | k1_tarski(B_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_570])).

tff(c_584,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_583])).

tff(c_52,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:56:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.34  
% 2.35/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.34  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.35/1.34  
% 2.35/1.34  %Foreground sorts:
% 2.35/1.34  
% 2.35/1.34  
% 2.35/1.34  %Background operators:
% 2.35/1.34  
% 2.35/1.34  
% 2.35/1.34  %Foreground operators:
% 2.35/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.35/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.35/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.35/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.35/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.35/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.35/1.35  
% 2.35/1.36  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.35/1.36  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.35/1.36  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.35/1.36  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.35/1.36  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.35/1.36  tff(f_63, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.35/1.36  tff(f_77, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.35/1.36  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.35/1.36  tff(f_75, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.35/1.36  tff(f_80, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.35/1.36  tff(c_38, plain, (![A_23]: (k2_tarski(A_23, A_23)=k1_tarski(A_23))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.35/1.36  tff(c_89, plain, (![A_52, B_53]: (k1_enumset1(A_52, A_52, B_53)=k2_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.36  tff(c_10, plain, (![E_11, A_5, B_6]: (r2_hidden(E_11, k1_enumset1(A_5, B_6, E_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.35/1.36  tff(c_107, plain, (![B_54, A_55]: (r2_hidden(B_54, k2_tarski(A_55, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_10])).
% 2.35/1.36  tff(c_110, plain, (![A_23]: (r2_hidden(A_23, k1_tarski(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_107])).
% 2.35/1.36  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.36  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.36  tff(c_118, plain, (![A_59, B_60]: (~r2_hidden(A_59, B_60) | ~r1_xboole_0(k1_tarski(A_59), B_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.35/1.36  tff(c_191, plain, (![A_70, B_71]: (~r2_hidden(A_70, B_71) | k3_xboole_0(k1_tarski(A_70), B_71)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_118])).
% 2.35/1.36  tff(c_195, plain, (![A_70]: (~r2_hidden(A_70, k1_tarski(A_70)) | k1_tarski(A_70)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_191])).
% 2.35/1.36  tff(c_197, plain, (![A_70]: (k1_tarski(A_70)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_110, c_195])).
% 2.35/1.36  tff(c_50, plain, (![A_35]: (k1_setfam_1(k1_tarski(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.35/1.36  tff(c_32, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.35/1.36  tff(c_309, plain, (![A_91, B_92]: (k3_xboole_0(k1_setfam_1(A_91), k1_setfam_1(B_92))=k1_setfam_1(k2_xboole_0(A_91, B_92)) | k1_xboole_0=B_92 | k1_xboole_0=A_91)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.35/1.36  tff(c_326, plain, (![A_35, B_92]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_35), B_92))=k3_xboole_0(A_35, k1_setfam_1(B_92)) | k1_xboole_0=B_92 | k1_tarski(A_35)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_50, c_309])).
% 2.35/1.36  tff(c_532, plain, (![A_110, B_111]: (k1_setfam_1(k2_xboole_0(k1_tarski(A_110), B_111))=k3_xboole_0(A_110, k1_setfam_1(B_111)) | k1_xboole_0=B_111)), inference(negUnitSimplification, [status(thm)], [c_197, c_326])).
% 2.35/1.36  tff(c_570, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k1_setfam_1(k1_tarski(B_13)))=k1_setfam_1(k2_tarski(A_12, B_13)) | k1_tarski(B_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_532])).
% 2.35/1.36  tff(c_583, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13) | k1_tarski(B_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_570])).
% 2.35/1.36  tff(c_584, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(negUnitSimplification, [status(thm)], [c_197, c_583])).
% 2.35/1.36  tff(c_52, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.35/1.36  tff(c_589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_584, c_52])).
% 2.35/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.36  
% 2.35/1.36  Inference rules
% 2.35/1.36  ----------------------
% 2.35/1.36  #Ref     : 0
% 2.35/1.36  #Sup     : 121
% 2.35/1.36  #Fact    : 0
% 2.35/1.36  #Define  : 0
% 2.35/1.36  #Split   : 0
% 2.35/1.36  #Chain   : 0
% 2.35/1.36  #Close   : 0
% 2.35/1.36  
% 2.35/1.36  Ordering : KBO
% 2.35/1.36  
% 2.35/1.36  Simplification rules
% 2.35/1.36  ----------------------
% 2.35/1.36  #Subsume      : 3
% 2.35/1.36  #Demod        : 61
% 2.35/1.36  #Tautology    : 84
% 2.35/1.36  #SimpNegUnit  : 10
% 2.35/1.36  #BackRed      : 1
% 2.35/1.36  
% 2.35/1.36  #Partial instantiations: 0
% 2.35/1.36  #Strategies tried      : 1
% 2.35/1.36  
% 2.35/1.36  Timing (in seconds)
% 2.35/1.36  ----------------------
% 2.35/1.36  Preprocessing        : 0.34
% 2.35/1.36  Parsing              : 0.17
% 2.35/1.36  CNF conversion       : 0.03
% 2.35/1.36  Main loop            : 0.26
% 2.35/1.36  Inferencing          : 0.10
% 2.35/1.36  Reduction            : 0.08
% 2.35/1.36  Demodulation         : 0.06
% 2.35/1.36  BG Simplification    : 0.02
% 2.35/1.36  Subsumption          : 0.04
% 2.35/1.36  Abstraction          : 0.02
% 2.35/1.36  MUC search           : 0.00
% 2.35/1.36  Cooper               : 0.00
% 2.35/1.36  Total                : 0.62
% 2.35/1.36  Index Insertion      : 0.00
% 2.35/1.36  Index Deletion       : 0.00
% 2.35/1.36  Index Matching       : 0.00
% 2.35/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
