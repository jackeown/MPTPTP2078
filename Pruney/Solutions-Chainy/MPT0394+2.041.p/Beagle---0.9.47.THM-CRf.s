%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:26 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  71 expanded)
%              Number of equality atoms :   44 (  62 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_10,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [A_45,B_46] : k3_xboole_0(k1_tarski(A_45),k2_tarski(A_45,B_46)) = k1_tarski(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_105,plain,(
    ! [A_14] : k3_xboole_0(k1_tarski(A_14),k1_tarski(A_14)) = k1_tarski(A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_96])).

tff(c_87,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(A_43,B_44)
      | k3_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [B_27] : ~ r1_xboole_0(k1_tarski(B_27),k1_tarski(B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_95,plain,(
    ! [B_27] : k3_xboole_0(k1_tarski(B_27),k1_tarski(B_27)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_20])).

tff(c_109,plain,(
    ! [B_27] : k1_tarski(B_27) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_95])).

tff(c_26,plain,(
    ! [A_32] : k1_setfam_1(k1_tarski(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_17,B_18,C_19] : k2_enumset1(A_17,A_17,B_18,C_19) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_20,B_21,C_22,D_23] : k3_enumset1(A_20,A_20,B_21,C_22,D_23) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_236,plain,(
    ! [B_67,A_65,D_64,E_63,C_66] : k2_xboole_0(k2_enumset1(A_65,B_67,C_66,D_64),k1_tarski(E_63)) = k3_enumset1(A_65,B_67,C_66,D_64,E_63) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_245,plain,(
    ! [A_17,B_18,C_19,E_63] : k3_enumset1(A_17,A_17,B_18,C_19,E_63) = k2_xboole_0(k1_enumset1(A_17,B_18,C_19),k1_tarski(E_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_236])).

tff(c_286,plain,(
    ! [A_70,B_71,C_72,E_73] : k2_xboole_0(k1_enumset1(A_70,B_71,C_72),k1_tarski(E_73)) = k2_enumset1(A_70,B_71,C_72,E_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_245])).

tff(c_298,plain,(
    ! [A_15,B_16,E_73] : k2_xboole_0(k2_tarski(A_15,B_16),k1_tarski(E_73)) = k2_enumset1(A_15,A_15,B_16,E_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_286])).

tff(c_302,plain,(
    ! [A_74,B_75,E_76] : k2_xboole_0(k2_tarski(A_74,B_75),k1_tarski(E_76)) = k1_enumset1(A_74,B_75,E_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_298])).

tff(c_314,plain,(
    ! [A_14,E_76] : k2_xboole_0(k1_tarski(A_14),k1_tarski(E_76)) = k1_enumset1(A_14,A_14,E_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_302])).

tff(c_318,plain,(
    ! [A_77,E_78] : k2_xboole_0(k1_tarski(A_77),k1_tarski(E_78)) = k2_tarski(A_77,E_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_314])).

tff(c_138,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(k1_setfam_1(A_57),k1_setfam_1(B_58)) = k1_setfam_1(k2_xboole_0(A_57,B_58))
      | k1_xboole_0 = B_58
      | k1_xboole_0 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_150,plain,(
    ! [A_57,A_32] :
      ( k1_setfam_1(k2_xboole_0(A_57,k1_tarski(A_32))) = k3_xboole_0(k1_setfam_1(A_57),A_32)
      | k1_tarski(A_32) = k1_xboole_0
      | k1_xboole_0 = A_57 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_138])).

tff(c_154,plain,(
    ! [A_57,A_32] :
      ( k1_setfam_1(k2_xboole_0(A_57,k1_tarski(A_32))) = k3_xboole_0(k1_setfam_1(A_57),A_32)
      | k1_xboole_0 = A_57 ) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_150])).

tff(c_324,plain,(
    ! [A_77,E_78] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_77)),E_78) = k1_setfam_1(k2_tarski(A_77,E_78))
      | k1_tarski(A_77) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_154])).

tff(c_340,plain,(
    ! [A_77,E_78] :
      ( k1_setfam_1(k2_tarski(A_77,E_78)) = k3_xboole_0(A_77,E_78)
      | k1_tarski(A_77) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_324])).

tff(c_341,plain,(
    ! [A_77,E_78] : k1_setfam_1(k2_tarski(A_77,E_78)) = k3_xboole_0(A_77,E_78) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_340])).

tff(c_28,plain,(
    k1_setfam_1(k2_tarski('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:33:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.35  
% 2.24/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.36  %$ r1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.24/1.36  
% 2.24/1.36  %Foreground sorts:
% 2.24/1.36  
% 2.24/1.36  
% 2.24/1.36  %Background operators:
% 2.24/1.36  
% 2.24/1.36  
% 2.24/1.36  %Foreground operators:
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.24/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.24/1.36  
% 2.24/1.37  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.24/1.37  tff(f_50, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.24/1.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.24/1.37  tff(f_48, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 2.24/1.37  tff(f_62, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.24/1.37  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.24/1.37  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.24/1.37  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.24/1.37  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.24/1.37  tff(f_60, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 2.24/1.37  tff(f_65, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.24/1.37  tff(c_10, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.37  tff(c_96, plain, (![A_45, B_46]: (k3_xboole_0(k1_tarski(A_45), k2_tarski(A_45, B_46))=k1_tarski(A_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.37  tff(c_105, plain, (![A_14]: (k3_xboole_0(k1_tarski(A_14), k1_tarski(A_14))=k1_tarski(A_14))), inference(superposition, [status(thm), theory('equality')], [c_10, c_96])).
% 2.24/1.37  tff(c_87, plain, (![A_43, B_44]: (r1_xboole_0(A_43, B_44) | k3_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.37  tff(c_20, plain, (![B_27]: (~r1_xboole_0(k1_tarski(B_27), k1_tarski(B_27)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.24/1.37  tff(c_95, plain, (![B_27]: (k3_xboole_0(k1_tarski(B_27), k1_tarski(B_27))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_87, c_20])).
% 2.24/1.37  tff(c_109, plain, (![B_27]: (k1_tarski(B_27)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_95])).
% 2.24/1.37  tff(c_26, plain, (![A_32]: (k1_setfam_1(k1_tarski(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.24/1.37  tff(c_12, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.24/1.37  tff(c_14, plain, (![A_17, B_18, C_19]: (k2_enumset1(A_17, A_17, B_18, C_19)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.37  tff(c_16, plain, (![A_20, B_21, C_22, D_23]: (k3_enumset1(A_20, A_20, B_21, C_22, D_23)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.37  tff(c_236, plain, (![B_67, A_65, D_64, E_63, C_66]: (k2_xboole_0(k2_enumset1(A_65, B_67, C_66, D_64), k1_tarski(E_63))=k3_enumset1(A_65, B_67, C_66, D_64, E_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.37  tff(c_245, plain, (![A_17, B_18, C_19, E_63]: (k3_enumset1(A_17, A_17, B_18, C_19, E_63)=k2_xboole_0(k1_enumset1(A_17, B_18, C_19), k1_tarski(E_63)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_236])).
% 2.24/1.37  tff(c_286, plain, (![A_70, B_71, C_72, E_73]: (k2_xboole_0(k1_enumset1(A_70, B_71, C_72), k1_tarski(E_73))=k2_enumset1(A_70, B_71, C_72, E_73))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_245])).
% 2.24/1.37  tff(c_298, plain, (![A_15, B_16, E_73]: (k2_xboole_0(k2_tarski(A_15, B_16), k1_tarski(E_73))=k2_enumset1(A_15, A_15, B_16, E_73))), inference(superposition, [status(thm), theory('equality')], [c_12, c_286])).
% 2.24/1.37  tff(c_302, plain, (![A_74, B_75, E_76]: (k2_xboole_0(k2_tarski(A_74, B_75), k1_tarski(E_76))=k1_enumset1(A_74, B_75, E_76))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_298])).
% 2.24/1.37  tff(c_314, plain, (![A_14, E_76]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(E_76))=k1_enumset1(A_14, A_14, E_76))), inference(superposition, [status(thm), theory('equality')], [c_10, c_302])).
% 2.24/1.37  tff(c_318, plain, (![A_77, E_78]: (k2_xboole_0(k1_tarski(A_77), k1_tarski(E_78))=k2_tarski(A_77, E_78))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_314])).
% 2.24/1.37  tff(c_138, plain, (![A_57, B_58]: (k3_xboole_0(k1_setfam_1(A_57), k1_setfam_1(B_58))=k1_setfam_1(k2_xboole_0(A_57, B_58)) | k1_xboole_0=B_58 | k1_xboole_0=A_57)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.24/1.37  tff(c_150, plain, (![A_57, A_32]: (k1_setfam_1(k2_xboole_0(A_57, k1_tarski(A_32)))=k3_xboole_0(k1_setfam_1(A_57), A_32) | k1_tarski(A_32)=k1_xboole_0 | k1_xboole_0=A_57)), inference(superposition, [status(thm), theory('equality')], [c_26, c_138])).
% 2.24/1.37  tff(c_154, plain, (![A_57, A_32]: (k1_setfam_1(k2_xboole_0(A_57, k1_tarski(A_32)))=k3_xboole_0(k1_setfam_1(A_57), A_32) | k1_xboole_0=A_57)), inference(negUnitSimplification, [status(thm)], [c_109, c_150])).
% 2.24/1.37  tff(c_324, plain, (![A_77, E_78]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_77)), E_78)=k1_setfam_1(k2_tarski(A_77, E_78)) | k1_tarski(A_77)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_318, c_154])).
% 2.24/1.37  tff(c_340, plain, (![A_77, E_78]: (k1_setfam_1(k2_tarski(A_77, E_78))=k3_xboole_0(A_77, E_78) | k1_tarski(A_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_324])).
% 2.24/1.37  tff(c_341, plain, (![A_77, E_78]: (k1_setfam_1(k2_tarski(A_77, E_78))=k3_xboole_0(A_77, E_78))), inference(negUnitSimplification, [status(thm)], [c_109, c_340])).
% 2.24/1.37  tff(c_28, plain, (k1_setfam_1(k2_tarski('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.24/1.37  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_341, c_28])).
% 2.24/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.37  
% 2.24/1.37  Inference rules
% 2.24/1.37  ----------------------
% 2.24/1.37  #Ref     : 0
% 2.24/1.37  #Sup     : 94
% 2.24/1.37  #Fact    : 0
% 2.24/1.37  #Define  : 0
% 2.24/1.37  #Split   : 0
% 2.24/1.37  #Chain   : 0
% 2.24/1.37  #Close   : 0
% 2.24/1.37  
% 2.24/1.37  Ordering : KBO
% 2.24/1.37  
% 2.24/1.37  Simplification rules
% 2.24/1.37  ----------------------
% 2.24/1.37  #Subsume      : 1
% 2.24/1.37  #Demod        : 40
% 2.24/1.37  #Tautology    : 62
% 2.24/1.37  #SimpNegUnit  : 13
% 2.24/1.37  #BackRed      : 4
% 2.24/1.37  
% 2.24/1.37  #Partial instantiations: 0
% 2.24/1.37  #Strategies tried      : 1
% 2.24/1.37  
% 2.24/1.37  Timing (in seconds)
% 2.24/1.37  ----------------------
% 2.24/1.37  Preprocessing        : 0.33
% 2.24/1.37  Parsing              : 0.18
% 2.24/1.37  CNF conversion       : 0.02
% 2.24/1.37  Main loop            : 0.22
% 2.24/1.37  Inferencing          : 0.09
% 2.24/1.37  Reduction            : 0.07
% 2.24/1.37  Demodulation         : 0.05
% 2.24/1.37  BG Simplification    : 0.02
% 2.24/1.37  Subsumption          : 0.03
% 2.24/1.37  Abstraction          : 0.02
% 2.24/1.37  MUC search           : 0.00
% 2.24/1.37  Cooper               : 0.00
% 2.24/1.37  Total                : 0.58
% 2.24/1.37  Index Insertion      : 0.00
% 2.24/1.37  Index Deletion       : 0.00
% 2.24/1.37  Index Matching       : 0.00
% 2.24/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
