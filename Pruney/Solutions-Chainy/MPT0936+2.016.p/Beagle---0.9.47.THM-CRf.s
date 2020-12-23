%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:29 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   53 (  99 expanded)
%              Number of leaves         :   33 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  95 expanded)
%              Number of equality atoms :   37 (  94 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_108,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_108])).

tff(c_120,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_117])).

tff(c_22,plain,(
    ! [B_35] : k4_xboole_0(k1_tarski(B_35),k1_tarski(B_35)) != k1_tarski(B_35) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_121,plain,(
    ! [B_35] : k1_tarski(B_35) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_22])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_209,plain,(
    ! [A_75,B_76,C_77] : k2_zfmisc_1(k2_tarski(A_75,B_76),k1_tarski(C_77)) = k2_tarski(k4_tarski(A_75,C_77),k4_tarski(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_231,plain,(
    ! [B_76,C_77] : k2_zfmisc_1(k2_tarski(B_76,B_76),k1_tarski(C_77)) = k1_tarski(k4_tarski(B_76,C_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_8])).

tff(c_265,plain,(
    ! [B_78,C_79] : k2_zfmisc_1(k1_tarski(B_78),k1_tarski(C_79)) = k1_tarski(k4_tarski(B_78,C_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_231])).

tff(c_34,plain,(
    ! [A_41,B_42] :
      ( k1_relat_1(k2_zfmisc_1(A_41,B_42)) = A_41
      | k1_xboole_0 = B_42
      | k1_xboole_0 = A_41 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_271,plain,(
    ! [B_78,C_79] :
      ( k1_relat_1(k1_tarski(k4_tarski(B_78,C_79))) = k1_tarski(B_78)
      | k1_tarski(C_79) = k1_xboole_0
      | k1_tarski(B_78) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_34])).

tff(c_279,plain,(
    ! [B_78,C_79] : k1_relat_1(k1_tarski(k4_tarski(B_78,C_79))) = k1_tarski(B_78) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_121,c_271])).

tff(c_40,plain,(
    ! [A_43,B_44,C_45] : k4_tarski(k4_tarski(A_43,B_44),C_45) = k3_mcart_1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_282,plain,(
    ! [B_80,C_81] : k1_relat_1(k1_tarski(k4_tarski(B_80,C_81))) = k1_tarski(B_80) ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_121,c_271])).

tff(c_291,plain,(
    ! [A_43,B_44,C_45] : k1_relat_1(k1_tarski(k3_mcart_1(A_43,B_44,C_45))) = k1_tarski(k4_tarski(A_43,B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_282])).

tff(c_42,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1','#skF_2','#skF_3')))) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_390,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_42])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.34  
% 2.19/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.34  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.34  
% 2.19/1.34  %Foreground sorts:
% 2.19/1.34  
% 2.19/1.34  
% 2.19/1.34  %Background operators:
% 2.19/1.34  
% 2.19/1.34  
% 2.19/1.34  %Foreground operators:
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.19/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.34  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.19/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.19/1.34  
% 2.19/1.35  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.19/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.19/1.35  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.19/1.35  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.19/1.35  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.35  tff(f_54, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.19/1.35  tff(f_68, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 2.19/1.35  tff(f_73, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.19/1.35  tff(f_76, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 2.19/1.35  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.35  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.35  tff(c_108, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.35  tff(c_117, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_108])).
% 2.19/1.35  tff(c_120, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_117])).
% 2.19/1.35  tff(c_22, plain, (![B_35]: (k4_xboole_0(k1_tarski(B_35), k1_tarski(B_35))!=k1_tarski(B_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.35  tff(c_121, plain, (![B_35]: (k1_tarski(B_35)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_22])).
% 2.19/1.35  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.19/1.35  tff(c_209, plain, (![A_75, B_76, C_77]: (k2_zfmisc_1(k2_tarski(A_75, B_76), k1_tarski(C_77))=k2_tarski(k4_tarski(A_75, C_77), k4_tarski(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.19/1.35  tff(c_231, plain, (![B_76, C_77]: (k2_zfmisc_1(k2_tarski(B_76, B_76), k1_tarski(C_77))=k1_tarski(k4_tarski(B_76, C_77)))), inference(superposition, [status(thm), theory('equality')], [c_209, c_8])).
% 2.19/1.35  tff(c_265, plain, (![B_78, C_79]: (k2_zfmisc_1(k1_tarski(B_78), k1_tarski(C_79))=k1_tarski(k4_tarski(B_78, C_79)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_231])).
% 2.19/1.35  tff(c_34, plain, (![A_41, B_42]: (k1_relat_1(k2_zfmisc_1(A_41, B_42))=A_41 | k1_xboole_0=B_42 | k1_xboole_0=A_41)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.19/1.35  tff(c_271, plain, (![B_78, C_79]: (k1_relat_1(k1_tarski(k4_tarski(B_78, C_79)))=k1_tarski(B_78) | k1_tarski(C_79)=k1_xboole_0 | k1_tarski(B_78)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_265, c_34])).
% 2.19/1.35  tff(c_279, plain, (![B_78, C_79]: (k1_relat_1(k1_tarski(k4_tarski(B_78, C_79)))=k1_tarski(B_78))), inference(negUnitSimplification, [status(thm)], [c_121, c_121, c_271])).
% 2.19/1.35  tff(c_40, plain, (![A_43, B_44, C_45]: (k4_tarski(k4_tarski(A_43, B_44), C_45)=k3_mcart_1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.19/1.35  tff(c_282, plain, (![B_80, C_81]: (k1_relat_1(k1_tarski(k4_tarski(B_80, C_81)))=k1_tarski(B_80))), inference(negUnitSimplification, [status(thm)], [c_121, c_121, c_271])).
% 2.19/1.35  tff(c_291, plain, (![A_43, B_44, C_45]: (k1_relat_1(k1_tarski(k3_mcart_1(A_43, B_44, C_45)))=k1_tarski(k4_tarski(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_282])).
% 2.19/1.35  tff(c_42, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_1', '#skF_2', '#skF_3'))))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.35  tff(c_390, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_42])).
% 2.19/1.35  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_279, c_390])).
% 2.19/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.35  
% 2.19/1.35  Inference rules
% 2.19/1.35  ----------------------
% 2.19/1.35  #Ref     : 0
% 2.19/1.35  #Sup     : 82
% 2.19/1.35  #Fact    : 0
% 2.19/1.35  #Define  : 0
% 2.19/1.35  #Split   : 0
% 2.19/1.35  #Chain   : 0
% 2.19/1.35  #Close   : 0
% 2.19/1.35  
% 2.19/1.35  Ordering : KBO
% 2.19/1.35  
% 2.19/1.35  Simplification rules
% 2.19/1.35  ----------------------
% 2.19/1.35  #Subsume      : 0
% 2.19/1.35  #Demod        : 28
% 2.19/1.35  #Tautology    : 57
% 2.19/1.35  #SimpNegUnit  : 8
% 2.19/1.35  #BackRed      : 2
% 2.19/1.35  
% 2.19/1.35  #Partial instantiations: 0
% 2.19/1.35  #Strategies tried      : 1
% 2.19/1.35  
% 2.19/1.35  Timing (in seconds)
% 2.19/1.35  ----------------------
% 2.19/1.35  Preprocessing        : 0.35
% 2.19/1.35  Parsing              : 0.19
% 2.19/1.35  CNF conversion       : 0.02
% 2.19/1.35  Main loop            : 0.20
% 2.19/1.35  Inferencing          : 0.08
% 2.19/1.35  Reduction            : 0.07
% 2.19/1.35  Demodulation         : 0.05
% 2.19/1.35  BG Simplification    : 0.02
% 2.19/1.35  Subsumption          : 0.02
% 2.19/1.35  Abstraction          : 0.02
% 2.19/1.35  MUC search           : 0.00
% 2.19/1.35  Cooper               : 0.00
% 2.19/1.35  Total                : 0.57
% 2.19/1.35  Index Insertion      : 0.00
% 2.19/1.35  Index Deletion       : 0.00
% 2.19/1.35  Index Matching       : 0.00
% 2.19/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
